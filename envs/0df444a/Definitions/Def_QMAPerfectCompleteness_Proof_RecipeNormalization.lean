-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
-- name    : QMAPerfectCompleteness_Proof_RecipeNormalization
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:48:25.761237+00:00
-- url     : https://prove2.me/theorems/fe516fa6-571d-46bf-b017-7bce539e88be
-- title:
--   Pushing wire maps into circuit recipes
-- statement:
--   Defines expression lifting, current-address substitution and normalization of nested wire mappings. The evaluation identities preserve the generated instruction list while moving address arithmetic into the leaf instructions and source traversal.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeNormalization.lean, retained declaration span lines 9–101.

/- Generated from Solutions.RecipeNormalization by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Push wire mappings through bounded recipes, keeping the finite loop structure. This lets
the code generator evaluate each address once, without a subsequent circuit-parsing pass. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe
namespace Expr

def lift : Expr → Expr
  | .lit n => .lit n
  | .param p => .param p
  | .bound j => .bound (j+1)
  | .addr => .addr
  | .add a b => .add a.lift b.lift
  | .sub a b => .sub a.lift b.lift
  | .scale n a => .scale n a.lift
  | .half a => .half a.lift
  | .ifLt a b y n => .ifLt a.lift b.lift y.lift n.lift

@[simp] theorem eval_lift (e : Expr) (env : Environment) (ctx : List ℕ) (j addr : ℕ) :
    e.lift.eval env (j::ctx) addr=e.eval env ctx addr := by
  induction e <;> simp_all [lift,eval]

def replaceAddr (e value : Expr) : Expr :=
  match e with
  | .lit n => .lit n
  | .param p => .param p
  | .bound j => .bound j
  | .addr => value
  | .add a b => .add (a.replaceAddr value) (b.replaceAddr value)
  | .sub a b => .sub (a.replaceAddr value) (b.replaceAddr value)
  | .scale n a => .scale n (a.replaceAddr value)
  | .half a => .half (a.replaceAddr value)
  | .ifLt a b y n => .ifLt (a.replaceAddr value) (b.replaceAddr value) (y.replaceAddr value) (n.replaceAddr value)

@[simp] theorem eval_replaceAddr (e value : Expr) (env : Environment) (ctx : List ℕ) (addr : ℕ) :
    (e.replaceAddr value).eval env ctx addr=e.eval env ctx (value.eval env ctx addr) := by
  induction e <;> simp_all [replaceAddr,eval]
end Expr

namespace Recipe

def mapInstruction (wireMap : Expr) (env : Environment) (ctx : List ℕ)
    (i : RawEncoding.Instruction) : RawEncoding.Instruction :=
  { i with wires := i.wires.map (fun w=>wireMap.eval env ctx w) }

@[simp] theorem mapInstruction_lift (wireMap : Expr) (env : Environment) (ctx : List ℕ)
    (j : ℕ) (i : RawEncoding.Instruction) :
    mapInstruction wireMap.lift env (j::ctx) i=mapInstruction wireMap env ctx i := by
  simp [mapInstruction]

@[simp] theorem mapInstruction_lift_fun (wireMap : Expr) (env : Environment) (ctx : List ℕ) (j : ℕ) :
    mapInstruction wireMap.lift env (j::ctx)=mapInstruction wireMap env ctx := by
  funext i
  exact mapInstruction_lift wireMap env ctx j i



/-- Compose each outer mapping into its leaf addresses, lifting it under loop binders. -/
def mapNormalize (wireMap : Expr) : Recipe → Recipe
  | .nil => .nil
  | .emit t wires => .emit t (wires.map (wireMap.replaceAddr ·))
  | .append a b => .append (a.mapNormalize wireMap) (b.mapNormalize wireMap)
  | .forUp n b => .forUp n (b.mapNormalize wireMap.lift)
  | .forDown n b => .forDown n (b.mapNormalize wireMap.lift)
  | .ifLt a b y n => .ifLt a b (y.mapNormalize wireMap) (n.mapNormalize wireMap)
  | .source r m => .source r (wireMap.replaceAddr m)
  | .mapWires m b => b.mapNormalize (wireMap.replaceAddr m)

/-- Normalization changes neither the generated gate list nor its order. -/
theorem eval_mapNormalize (p : Recipe) (wireMap : Expr) (env : Environment) (ctx : List ℕ)
    (src : List RawEncoding.Instruction) :
    (p.mapNormalize wireMap).eval env ctx src=
      (p.eval env ctx src).map (mapInstruction wireMap env ctx) := by
  induction p generalizing wireMap ctx with
  | nil => rfl
  | emit t wires => simp [mapNormalize,eval,mapInstruction,List.map_map,Function.comp_def]
  | append a b ia ib => simp [mapNormalize,eval,ia,ib]
  | forUp n b ih => simp [mapNormalize,eval,ih,List.map_flatMap,Function.comp_def,mapInstruction]
  | forDown n b ih => simp [mapNormalize,eval,ih,List.map_flatMap,Function.comp_def,mapInstruction]
  | ifLt a b y n iy inn => simp only [mapNormalize,eval]; split_ifs <;> simp [iy,inn]
  | source r m => simp [mapNormalize,eval,mapInstruction,List.map_map,Function.comp_def]
  | mapWires m b ih =>
    simp only [mapNormalize,eval,ih,List.map_map]
    congr 1
    funext i
    simp [Function.comp_def,mapInstruction]

def normalize (p : Recipe) : Recipe := p.mapNormalize .addr

@[simp] theorem eval_normalize (p : Recipe) (env : Environment) (ctx : List ℕ)
    (src : List RawEncoding.Instruction) : p.normalize.eval env ctx src=p.eval env ctx src := by
  rw [normalize,eval_mapNormalize]
  have h : mapInstruction Expr.addr env ctx=id := by
    funext i
    simp [mapInstruction,Expr.eval]
  rw [h,List.map_id]

end Recipe
end QMAPerfectCompleteness.Main.CircuitRecipe


