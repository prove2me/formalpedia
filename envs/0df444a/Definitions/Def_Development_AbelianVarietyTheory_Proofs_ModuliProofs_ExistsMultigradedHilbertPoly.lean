-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:30.001357+00:00
-- url     : https://prove2.me/theorems/579019eb-d5f7-4aee-bb35-34efca49bf93
-- title:
--   Exists Multigraded Hilbert Poly
-- statement:
--   Definitions and structural lemmas for Exists Multigraded Hilbert Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}
def EventuallyPoly (f : (Fin r → ℕ) → ℚ) : Prop :=
  ∃ (Φ : MvPolynomial (Fin r) ℚ) (n₀ : ℕ), ∀ n : Fin r → ℕ, (∀ k, n₀ ≤ n k) →
    f n = MvPolynomial.eval (fun k => (n k : ℚ)) Φ
end GlobalTheory.MultiHilbert
namespace GlobalTheory.MultiHilbert
open MvPolynomial
section
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)
noncomputable def colonX (I : Ideal (MvPolynomial σ K)) (i : σ) : Ideal (MvPolynomial σ K) :=
  Submodule.comap (LinearMap.mulLeft (MvPolynomial σ K) (X i)) I
end
section
variable {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)
end
end GlobalTheory.MultiHilbert
namespace GlobalTheory.MultiHilbert
open MvPolynomial
noncomputable def hilbertFun {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)
    (I : Ideal (MvPolynomial σ K)) (n : Fin r → ℕ) : ℚ :=
  ((Module.finrank K ↥(weightedHomogeneousSubmodule K
    (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) : ℕ) : ℚ) -
  ((Module.finrank K ↥(weightedHomogeneousSubmodule K
    (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ⊓ I.restrictScalars K) : ℕ) : ℚ)
end GlobalTheory.MultiHilbert
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct


