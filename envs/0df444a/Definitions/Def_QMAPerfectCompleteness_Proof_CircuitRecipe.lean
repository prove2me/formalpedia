-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
-- name    : QMAPerfectCompleteness_Proof_CircuitRecipe
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:47:37.474198+00:00
-- url     : https://prove2.me/theorems/be7c941a-0a4c-4713-8940-19a3bc2f20ea
-- title:
--   Finite recipes for parameterized circuits
-- statement:
--   Defines an expression language for wire addresses and a finite circuit-generator language with bounded loops, branches, source-circuit traversal and wire relabeling. Its evaluation gives a literal list of raw gate instructions for a chosen register environment.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CircuitRecipe.lean, retained declaration span lines 10–148.

/- Generated from Solutions.CircuitRecipe by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Finite circuit-generator recipes. Loops range over unary widths; wire arithmetic is
explicit and preserves the dynamic structure of the paper's polynomial circuit constructions. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe

inductive Param where
  | proof | ancilla | output | hadamards | clock | ell | index
  deriving DecidableEq, Fintype, Repr
abbrev Environment := Param → ℕ

inductive Expr where
  | lit : ℕ → Expr
  | param : Param → Expr
  | bound : ℕ → Expr
  | addr : Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | half : Expr → Expr
  | scale : ℕ → Expr → Expr
  | ifLt : Expr → Expr → Expr → Expr → Expr
  deriving Repr, DecidableEq

namespace Expr

def eval (e : Expr) (env : Environment) (ctx : List ℕ) (addr : ℕ := 0) : ℕ :=
  match e with
  | .lit n => n
  | .param p => env p
  | .bound j => ctx[j]?.getD 0
  | .addr => addr
  | .add a b => a.eval env ctx addr + b.eval env ctx addr
  | .sub a b => a.eval env ctx addr - b.eval env ctx addr
  | .half a => a.eval env ctx addr / 2
  | .scale n a => n*a.eval env ctx addr
  | .ifLt a b y n => if a.eval env ctx addr < b.eval env ctx addr then y.eval env ctx addr else n.eval env ctx addr





end Expr

inductive Recipe where
  | nil : Recipe
  | emit : ℕ → List Expr → Recipe
  | append : Recipe → Recipe → Recipe
  | forUp : Expr → Recipe → Recipe
  | forDown : Expr → Recipe → Recipe
  | ifLt : Expr → Expr → Recipe → Recipe → Recipe
  | source : Bool → Expr → Recipe
  | mapWires : Expr → Recipe → Recipe
  deriving Repr

namespace Recipe

def eval (p : Recipe) (env : Environment) (ctx : List ℕ)
    (src : List RawEncoding.Instruction) : List RawEncoding.Instruction :=
  match p with
  | .nil => []
  | .emit tag wires => [⟨tag,wires.map (fun e => e.eval env ctx)⟩]
  | .append a b => a.eval env ctx src ++ b.eval env ctx src
  | .forUp n body => (List.range (n.eval env ctx)).flatMap (fun j => body.eval env (j::ctx) src)
  | .forDown n body => ((List.range (n.eval env ctx)).reverse).flatMap (fun j => body.eval env (j::ctx) src)
  | .ifLt a b y n => if a.eval env ctx < b.eval env ctx then y.eval env ctx src else n.eval env ctx src
  | .source reverse wireMap => (if reverse then src.reverse else src).map
      (fun i => {i with wires := i.wires.map (fun w => wireMap.eval env ctx w)})
  | .mapWires wireMap body => (body.eval env ctx src).map
      (fun i => {i with wires := i.wires.map (fun w => wireMap.eval env ctx w)})




/-- Reverse gate order without expanding loops. All primitive G2 gates are self-adjoint. -/
def reverse : Recipe → Recipe
  | .nil => .nil
  | .emit t w => .emit t w
  | .append a b => .append b.reverse a.reverse
  | .forUp n b => .forDown n b.reverse
  | .forDown n b => .forUp n b.reverse
  | .ifLt a b y n => .ifLt a b y.reverse n.reverse
  | .source r w => .source (!r) w
  | .mapWires w b => .mapWires w b.reverse



end Recipe

structure Circuit where
  proofQubits : Expr
  ancillaQubits : Expr
  output : Expr
  gates : Recipe

def Circuit.eval (C : Circuit) (env : Environment) (src : List RawEncoding.Instruction) : RawEncoding.Circuit :=
  ⟨C.proofQubits.eval env [],C.ancillaQubits.eval env [],C.output.eval env [],C.gates.eval env [] src⟩

end QMAPerfectCompleteness.Main.CircuitRecipe


