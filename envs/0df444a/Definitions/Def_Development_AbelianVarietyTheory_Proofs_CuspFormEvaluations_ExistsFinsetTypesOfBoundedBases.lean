-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:00.090838+00:00
-- url     : https://prove2.me/theorems/afd09aae-b3b8-4777-92ac-7ec433dcda34
-- title:
--   Exists Finset Types Of Bounded Bases
-- statement:
--   Definitions and structural lemmas for Exists Finset Types Of Bounded Bases, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory
namespace BoundedBasis
section Algebra
variable {E : Type} [Field E] [NumberField E]
end Algebra
section Herm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]
theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp [herm, Finset.mul_sum, mul_assoc]
noncomputable def gramOf (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i k => herm G (v i) (v k)
end Herm
section Lattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
noncomputable def pairing (v : Fin r → Fin r → E) (hv : ∀ i, v i ∈ X.L') :
    X.Λ →ₗ[𝓞 E] (Fin r → 𝓞 E) where
  toFun x k := ⟨herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k),
    X.L'_int _ (X.NA_sub _ x.2) _ (hv k)⟩
  map_add' x y := by
    funext k
    refine RingOfIntegers.ext ?_
    change herm X.Gm ((X.NA : E) • ((x : Fin r → E) + y)) (v k) =
      herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k) +
        herm X.Gm ((X.NA : E) • (y : Fin r → E)) (v k)
    rw [smul_add, herm_add_left]
  map_smul' c x := by
    funext k
    refine RingOfIntegers.ext ?_
    change herm X.Gm ((X.NA : E) • ((c : E) • (x : Fin r → E))) (v k) =
      (c : E) * herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k)
    rw [smul_comm, herm_smul_left]
end Lattice
end BoundedBasis
open BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def IsBoundedBasis (X : DataX E r) (B : ℝ) (v : Fin r → Fin r → E) : Prop :=
  (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
    ∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B
end GlobalTheory


