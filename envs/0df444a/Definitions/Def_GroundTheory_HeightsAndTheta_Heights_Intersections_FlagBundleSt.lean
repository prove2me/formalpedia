-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:50.223804+00:00
-- url     : https://prove2.me/theorems/0d6428dc-c323-4ef6-9045-3d23ab492424
-- title:
--   Flag Bundle St
-- statement:
--   Definitions and structural lemmas for Flag Bundle St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FlagBundleSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
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
section Gen
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem aeval_comp_X {σ A B : Type} [CommRing A] [CommRing B] {_ : Algebra ℤ B}
    (φ : MvPolynomial σ ℤ →+* A) (e : A →+* B) (f : MvPolynomial σ ℤ) :
    aeval (fun q => e (φ (X q))) f = e (φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (eq_intCast (algebraMap ℤ B) a).trans (eq_intCast ((e.comp φ).comp C) a).symm
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
  | mul_X p q hp => rw [map_mul, hp, aeval_X, map_mul, map_mul]
omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_genPt (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) :=
  aeval_comp_X (Ideal.Quotient.mk P) (algebraMap (MRing ι ⧸ P) (FnField P)) f
omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ker_algebraMap_comp_mk (P : Ideal (MRing ι)) :
    RingHom.ker ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) = P := by
  rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)), Ideal.mk_ker]
omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem flagMap_X_inl (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (p : Σ k, ι k) :
    flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p)) = C (genPt P p) := by
  obtain ⟨k, i⟩ := p
  simp [flagMap, inlV]
omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem imageZ_flagIdeal (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    imageZ (inlV (ι₂ := PluckerBlocks N1 n)) (flagIdeal P B) = P := by
  have h : (flagMap P B).comp (rename (inlV (ι₂ := PluckerBlocks N1 n)) : MRing ι →ₐ[ℤ] _).toRingHom =
      (C : FnField P →+* MvPolynomial (Fin n × Fin n) (FnField P)).comp
        ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) :=
    MvPolynomial.ringHom_ext (fun r => by
      rw [← RingHom.comp_apply _ C r, ← RingHom.comp_apply _ C r, eq_intCast, eq_intCast]) fun p => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
      exact flagMap_X_inl P B p
  rw [imageZ, flagIdeal, RingHom.comap_ker, h, RingHom.ker_comp_of_injective _ (C_injective _ _),
    ker_algebraMap_comp_mk]
def flagGenFibre (P : Ideal (MRing ι)) (hP : P.IsPrime) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    GenFibre (inlV (ι := ι) (ι₂ := PluckerBlocks N1 n)) (flagIdeal P B) :=
  haveI := hP
  { Φ := FnField P
    Φ' := FractionRing (MvPolynomial (Fin n × Fin n) (FnField P))
    x := genPt P
    x' := fun q => algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) _ (flagMap P B (X q))
    ker_x := by
      rw [imageZ_flagIdeal]
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk P) f
    gen := fun c => by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨f, g, ?_, ?_⟩
      · rw [aeval_genPt]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      · rw [aeval_genPt, aeval_genPt]
    genericFibre_ker_target := by
      ext f
      rw [RingHom.mem_ker, aeval_comp_X (flagMap P B), ← RingHom.comp_apply, ← RingHom.mem_ker,
        RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _)]
      rfl
    compat := fun p => by
      show algebraMap _ _ (flagMap P B (X (inlV p))) = _
      rw [flagMap_X_inl, IsScalarTower.algebraMap_apply (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))
        (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P))), algebraMap_eq] }
end Gen
def FlagArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m n → IsKerBasis P c B →
    IsArithVar (flagIdeal P B) (flagDim n + d)
def FlagFibre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hP : IsArithVar P d),
    IsQuotRows P c m n → IsKerBasis P c B →
    ∀ J₀ : IFamily ℚ (PluckerBlocks n n), IsFieldIntersection J₀ →
      ∃ J : IFamily (flagGenFibre P hP.2.1.1 B).Φ (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl),
        IsFieldIntersection J ∧
        ∀ a : Fin (flagDim n) → K ⊕ Fin (n - 1) → ℤ,
          J (fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B)) (flagDim n)
              (fun j => fibreDeg Sum.inl (a j)) =
            J₀ (flagIdealQ n) (flagDim n) (fun i j => a i (Sum.inr j))
def flagGenFibre_inhabited :
    GenFibre (inlV (ι := GlobalTheory 2) (ι₂ := PluckerBlocks 3 3)) (flagIdeal (⊥ : Ideal (MRing (GlobalTheory 2))) (idRows 3)) :=
  flagGenFibre ⊥ Ideal.isPrime_bot (idRows 3)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


