-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxOrdinaryComponent
-- name    : BS2_b3ba934b_MinmaxOrdinaryComponent
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:33:57.810099+00:00
-- url     : https://prove2.me/theorems/f5e1c741-3d63-4752-8431-63f4c6cdcd91
-- title:
--   Sensitivity separation: MinmaxOrdinaryComponent (complete source module)
-- statement:
--   Complete Lean source module `MinmaxOrdinaryComponent` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxOrdinaryComponent.lean; original SHA-256 588db42e058723589db3b87fe5c24c1837a5a8b779d45fdb31b9aff033f64174; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Constant upper-threshold components of actual graded min/max parents. -/
import Definitions.Def_BS2_b3ba934b_MinmaxMParent
import Definitions.Def_BS2_b3ba934b_OrdinaryNumericA

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundConditionalNumeric ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem ordinary_upper_component_accepts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤ S.tolerance l → t b ≤ u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (d : ℕ) (hd : d ≤ S.tolerance l) (x : ((V × Bool) × I) → Bool)
    (hx : ordinaryParent S F (u d) (S.guard l) d x=true) : parent S F l x=true := by
  obtain ⟨w,htarget,hcount⟩ := (ordinary_parent_true S F (u d) (S.guard l) d x).1 hx
  exact oriented_implies_parent S F hF l t u ht hu hlu hdef x w d false hd
    ⟨hF _ _ (hlu d hd) _ (htarget true),htarget false,hcount⟩

theorem ordinary_upper_component_down_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hlu : ∀ b, b ≤ S.tolerance l → t b ≤ u b)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (d : ℕ) (hd : d ≤ S.tolerance l) (x : ((V × Bool) × I) → Bool) :
    flipsTo (parent S F l) false x ⊆ flipsTo (ordinaryParent S F (u d) (S.guard l) d) false x := by
  intro bit hbit
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  cases hh : ordinaryParent S F (u d) (S.guard l) d (flip x {bit}) with
  | false => rfl
  | true =>
    have hon := ordinary_upper_component_accepts S F hF l t u ht hu hlu hdef d hd _ hh
    rw [(Finset.mem_filter.mp hbit).2] at hon
    contradiction

variable {n : ℕ}

theorem ordinary_upper_component_AExpr_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j)
    (d : ℕ) (hd : d ≤ S.tolerance i) (hq : S.tolerance j ≤ d) (hq8 : S.tolerance j ≤ 8)
    (tj : Fin n) (ht : P.weakUpper d ≤ tj)
    (hstrong : parent S F j=ordinaryParent S F tj (S.guard j) (S.tolerance j))
    (v : Profile n) (hv : Upper F v) :
    ABound (parent S F) i j
      ((ordinaryAExpr n ordinaryCaps10007 (P.weakUpper d).val (S.guard i).val d
        tj.val (S.guard j).val (S.tolerance j)).eval v) := by
  intro x hx
  have hcomp : ordinaryParent S F (P.weakUpper d) (S.guard i) d x=false := by
    cases he : ordinaryParent S F (P.weakUpper d) (S.guard i) d x with
    | false => rfl
    | true =>
      have hh := ordinary_upper_component_accepts S F hF i P.weakLower P.weakUpper P.weakLowerMono
        P.weakUpperMono P.weakLowerUpper P.weakDef d hd x he
      exact False.elim (Bool.false_ne_true (hx.symm.trans hh))
  rw [hstrong]
  exact ordinaryAExpr_bound S hAdj hLabel F hF (P.weakUpper d) tj (S.guard i) (S.guard j)
    ht P.guards ((P.weakGuardTarget d hd).trans (P.weakLowerUpper d hd)) d (S.tolerance j)
    hq hq8 v hv x hcomp

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.ordinary_upper_component_accepts
#print axioms ThreeBoundMinmaxTransfer.ordinary_upper_component_AExpr_bound


