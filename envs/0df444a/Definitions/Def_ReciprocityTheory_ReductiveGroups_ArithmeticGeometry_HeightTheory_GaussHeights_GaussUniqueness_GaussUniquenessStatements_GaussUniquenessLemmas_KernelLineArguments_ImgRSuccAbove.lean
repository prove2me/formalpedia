-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:37.25487+00:00
-- url     : https://prove2.me/theorems/eac5f3c6-e145-4dc9-8099-dd7f1af33149
-- title:
--   Img RSucc Above
-- statement:
--   Definitions and structural lemmas for Img RSucc Above, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ImgRSuccAbove.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
import Theorems.Thm_GaussValuationUniqueness_mem_vRing_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
noncomputable def imgR {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (p : TVar D N) : MvPolynomial (SVar D N) R :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) R) j0
    (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (ρ k))
    (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2
section Ker
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))
theorem alg_mem (hv : IsTrivOn K v) (x : K) : algebraMap K Ω x ∈ vRing v := by
  rw [mem_vRing_iff]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [hv x hx]
noncomputable def kap (hv : IsTrivOn K v) : K →+* vRing v :=
  (algebraMap K Ω).codRestrict (vRing v) (alg_mem v hv)
noncomputable def psiT (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (vRing v) :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C : vRing v →+* MvPolynomial (SVar D N) (vRing v)).comp
    (kap v hv)) (imgR j0 ρ)
noncomputable def psiR (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (IsLocalRing.ResidueField (vRing v)) :=
  (MvPolynomial.map (IsLocalRing.residue (vRing v))).comp (psiT (D := D) v hv j0 ρ)
end Ker
end GaussValuationUniqueness


