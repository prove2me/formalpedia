-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:22.851004+00:00
-- url     : https://prove2.me/theorems/83b984b4-5cc0-4808-b66a-d2e7bdf1faa4
-- title:
--   Cm Approximation Transference
-- statement:
--   Definitions and structural lemmas for Cm Approximation Transference, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
section CMType
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {σ : ι → K →+* ℂ}
end CMType
section Lattice
variable {K : Type} [Field K] [NumberField K] {r : ℕ}
theorem h_add_left (S : HermForm K r) (x x' y : Fin r → K) :
    S.h (x + x') y = S.h x y + S.h x' y := by
  simp [HermForm.h, add_mul, Finset.sum_add_distrib]
theorem h_add_right (S : HermForm K r) (x y y' : Fin r → K) :
    S.h x (y + y') = S.h x y + S.h x y' := by
  simp [HermForm.h, mul_add, Finset.sum_add_distrib]
theorem h_smul_left (S : HermForm K r) (a : K) (x y : Fin r → K) :
    S.h (a • x) y = S.c a * S.h x y := by
  simp [HermForm.h, Finset.mul_sum, mul_assoc]
theorem h_smul_right (S : HermForm K r) (a : K) (x y : Fin r → K) :
    S.h x (a • y) = a * S.h x y := by
  simp only [HermForm.h, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
noncomputable def traceForm (S : HermForm K r) : LinearMap.BilinForm ℚ (Fin r → K) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ K (S.h x y))
    (fun x x' y => by rw [h_add_left, map_add])
    (fun q x y => by
      rw [← algebraMap_smul K q x, h_smul_left, ← map_smul, Algebra.smul_def]; simp)
    (fun x y y' => by rw [h_add_right, map_add])
    (fun q x y => by
      rw [← algebraMap_smul K q y, h_smul_right, ← map_smul, Algebra.smul_def])
end Lattice
section Embedding
variable {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
omit [Fintype ι] in
theorem embVec_add (τ : K →+* ℂ) (x y : Fin r → K) :
    embVec τ (x + y) = embVec τ x + embVec τ y := by
  ext a; simp [embVec]
noncomputable def emb (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → K) →+ EuclideanSpace ℂ (ι × Fin r) :=
  AddMonoidHom.mk' (fun x => WithLp.toLp 2 fun ik => (Q ik.1 *ᵥ embVec (σ ik.1) x) ik.2)
    (fun x y => by ext ik; simp [embVec_add, mulVec_add])
noncomputable def embDual (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → K) →+ EuclideanSpace ℂ (ι × Fin r) :=
  AddMonoidHom.mk'
    (fun x => WithLp.toLp 2 fun ik => 2 * sgn p ik.2 * (Q ik.1 *ᵥ embVec (σ ik.1) x) ik.2)
    (fun x y => by ext ik; simp [embVec_add, mulVec_add, mul_add])
variable (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
variable {p σ Q}
end Embedding
end GlobalTheory.CMTransference


