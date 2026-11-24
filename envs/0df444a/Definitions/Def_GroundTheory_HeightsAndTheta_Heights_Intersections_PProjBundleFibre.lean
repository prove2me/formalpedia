-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:42.033064+00:00
-- url     : https://prove2.me/theorems/5190db52-005d-4d6d-90ba-755e6bbafe58
-- title:
--   PProj Bundle Fibre
-- statement:
--   Definitions and structural lemmas for PProj Bundle Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_imageZ_projBundleIdeal_44be4285848e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
section LinSubst
variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}
def linSubst (ℓ : σ → Fin n → Φ) : MvPolynomial σ Φ →ₐ[Φ] MvPolynomial (Fin n) Φ :=
  aeval fun q => ∑ a, C (ℓ q a) * X a
def linKerForms (ℓ : σ → Fin n → Φ) : Set (MvPolynomial σ Φ) :=
  {f | ∃ μ : σ → Φ, (∀ b, ∑ q, μ q * ℓ q b = 0) ∧ f = ∑ q, C (μ q) * X q}
end LinSubst
section Main
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_genPt_eq_mk (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) := by
  have h : (aeval (genPt P) : MRing ι →ₐ[ℤ] FnField P).toRingHom =
      (algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P) :=
    MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from
      eq_intCast C r, map_intCast, map_intCast])
      (fun p => by simp [genPt])
  exact RingHom.congr_fun h f
def projBundlePt (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    (Σ k, PBlk ι N1 k) → FractionRing (MvPolynomial (Fin n) (FnField P)) :=
  fun p => algebraMap (MvPolynomial (Fin n) (FnField P)) _ (projBundleMap P B (X p))
omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_projBundlePt (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) {_ : Algebra ℤ (FractionRing (MvPolynomial (Fin n) (FnField P)))}
    (f : MRing (PBlk ι N1)) :
    aeval (projBundlePt P B) f = algebraMap (MvPolynomial (Fin n) (FnField P)) _ (projBundleMap P B f) := by
  have h : (aeval (projBundlePt P B) : MRing (PBlk ι N1) →ₐ[ℤ] _).toRingHom =
      (algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp
        (projBundleMap P B) :=
    MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from
      eq_intCast C r, map_intCast, map_intCast])
      (fun p => by simp [projBundlePt])
  exact RingHom.congr_fun h f
def projBundleGenFibre (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    GenFibre (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) where
  Φ := FnField P
  Φ' := FractionRing (MvPolynomial (Fin n) (FnField P))
  x := genPt P
  x' := projBundlePt P B
  ker_x := by
    rw [imageZ_projBundleIdeal]
    ext f
    rw [RingHom.mem_ker]
    exact (Eq.congr_left (aeval_genPt_eq_mk P f)).trans
      ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans Ideal.Quotient.eq_zero_iff_mem)
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · exact fun h => IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb ((aeval_genPt_eq_mk P g).symm.trans h)
    · exact (congrArg₂ (· / ·) (aeval_genPt_eq_mk P f) (aeval_genPt_eq_mk P g)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker]
    exact (Eq.congr_left (aeval_projBundlePt P B f)).trans
      ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans RingHom.mem_ker.symm)
  compat p := by
    obtain ⟨k, i⟩ := p
    simp [projBundlePt, inlV, projBundleMap, IsScalarTower.algebraMap_apply (FnField P)
      (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))]
end Main
section Fibre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)] in

def fibreCoordEquiv (ι : K → Type) (N1 : ℕ) :
    (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) ≃ Fin N1 where
  toFun
    | ⟨⟨.inl k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨.inr _, _⟩, j⟩ => j
  invFun j := ⟨⟨.inr (), by rintro ⟨k, hk⟩; cases hk⟩, j⟩
  left_inv := by
    rintro ⟨⟨k | u, h⟩, j⟩
    · exact absurd ⟨k, rfl⟩ h
    · rfl
  right_inv _ := rfl
end Fibre
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


