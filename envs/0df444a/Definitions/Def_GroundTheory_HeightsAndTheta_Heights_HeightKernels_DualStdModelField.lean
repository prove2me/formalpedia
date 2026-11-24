-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:59.451575+00:00
-- url     : https://prove2.me/theorems/2438316f-20cb-4530-b837-e59ab32a5635
-- title:
--   Dual Std Model Field
-- statement:
--   Definitions and structural lemmas for Dual Std Model Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/DualStdModelField.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsPrimeSpanXb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial
noncomputable section
abbrev dualStdModelField (K : Type) [Field K] (i : ℕ) : Type :=
  FractionRing (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
def dualStdModelS (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (C (X ()))
def dualStdModelT (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (X ())
def dualStdModelEmb (K : Type) [Field K] (i : ℕ) : ProjField K i →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp
    ((C : MvPolynomial Unit (ProjField K i) →+* _).comp C)
def dualStdModelPt {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) :
    (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → dualStdModelField K i
  | ⟨Sum.inl (), t⟩ => dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i
  | ⟨Sum.inr (), j⟩ =>
    dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i
def GenFibreModelTransport.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type)
    [∀ k, Fintype (ι' k)] (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    (Ω : Type) [Field Ω] (z : (Σ k', ι' k') → Ω), RingHom.ker (eval₂Hom (Int.castRingHom Ω) z : MRing ι' →+* Ω) = P' →
    ∀ (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ Ω], (algebraMap Φ₀ Ω).fieldRange = Subfield.closure (Set.range (z ∘ v)) →
    ∀ (τ : Type) (w : τ → Σ k', ι' k') (q : Σ k', ι' k'),
      (G.x' q = 0 ↔ z q = 0) ∧
      Module.finrank G.Φ (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) =
        Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) ∧
      (Transcendental (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) (G.x' q) ↔
        Transcendental (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) (z q))
def DualStdGraphModel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    RingHom.ker (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) =
      graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
def DualStdModelRank.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) ≠ 0 ∧
      Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) = Module.finrank ℚ K
def DualStdModelTransc.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      Transcendental (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))
        (dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))
example : ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (Φ₀ : Subfield (dualStdModelField ℚ 1)),
    (algebraMap Φ₀ (dualStdModelField ℚ 1)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks Unit) (ι₂ := PBlk 1))) ∧ 1 ≤ 1 :=
  ⟨dualBasisStandard, _, Subfield.fieldRange_subtype _, le_rfl⟩
example : ∃ (_ : GenFibre (ι := PBlk 1) (ι' := PBlk 1) id ⊥) (z : (Σ _ : Unit, Fin 1) → FractionRing (MRing (PBlk 1)))
    (Φ₀ : Subfield (FractionRing (MRing (PBlk 1)))),
    RingHom.ker (eval₂Hom (Int.castRingHom _) z : MRing (PBlk 1) →+* FractionRing (MRing (PBlk 1))) = ⊥ ∧
      (algebraMap Φ₀ (FractionRing (MRing (PBlk 1)))).fieldRange = Subfield.closure (Set.range (z ∘ id)) := by
  have : (⊥ : Ideal (MRing (PBlk 1))).IsPrime := Ideal.isPrime_bot
  refine ⟨Inter.genFibreIdOf ⊥, fun q => algebraMap (MRing (PBlk 1)) _ (X q), _, ?_, Subfield.fieldRange_subtype _⟩
  refine (RingHom.injective_iff_ker_eq_bot _).mp ?_
  have h : (eval₂Hom (Int.castRingHom _) fun q => algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))) (X q) :
      MRing (PBlk 1) →+* _) = algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))) := by
    ext q
    · simp
    · simp
  rw [h]
  exact IsFractionRing.injective _ _
end
end GroundTheory.Heights₂.Heights


