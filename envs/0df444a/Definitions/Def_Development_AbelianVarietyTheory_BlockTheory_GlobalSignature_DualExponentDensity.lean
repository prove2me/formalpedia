-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_DualExponentDensity
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_DualExponentDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:22.548157+00:00
-- url     : https://prove2.me/theorems/82f15cce-28f2-4e50-a5bc-4003887e912a
-- title:
--   Dual Exponent Density
-- statement:
--   Definitions and structural lemmas for Dual Exponent Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/DualExponentDensity.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Places
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def IsInertAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime
def IsSplitAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (v.asIdeal.primesOver (𝓞 E)).ncard = 2
def IsEtaAt (v : HeightOneSpectrum (𝓞 F)) (η : ℤ) : Prop :=
  (IsInertAt F E v ∧ η = -1) ∨ (IsSplitAt F E v ∧ η = 1)
def resCard (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)
abbrev maxOrder (v : HeightOneSpectrum (𝓞 F)) :
    Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)
def IsLocalChar (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) : Prop :=
  Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ∃ t, ψ t ≠ 1
def IsDualExp (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) (c : ℤ) : Prop :=
  ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔
    Valued.v t ≤ WithZero.exp c
def dualIndex (v : HeightOneSpectrum (𝓞 F)) (c : ℤ) : ℝ := (resCard F v : ℝ) ^ c
end Places
section Lattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
def IsSelfDualLattice (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (Fv F v ⊗[F] E) (L : Set (Fin M → Fv F v ⊗[F] E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, hR (Fv F v) σ J x y ∈ maxOrder F E v
def latTup (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) :
    Set (Fin 1 → Fin M → Fv F v ⊗[F] E) := {X | X 0 ∈ L}
def qTup (X : Fin 1 → Fin M → Fv F v ⊗[F] E) : Fv F v := qR (Fv F v) σ J (X 0)
end Lattice
def densityValue (N : ℝ) (q : ℕ) (η : ℤ) (M : ℕ) : ℝ :=
  N ^ ((1 / 2 : ℝ) - M) * (1 - (η : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ)))
def SelfDualLatticeDensity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 1 ≤ M → IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (η : ℤ), IsEtaAt F E v η →
  ∀ (ψ : AddChar (Fv F v) ℂ), IsLocalChar F v ψ →
  AllSome (IsDualExp F v ψ) fun c =>
  ∀ (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)), IsSelfDualLattice σ J v L →
  ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), SdW F E σ M J (Fv F v) ψ 1 μ →
  ∀ (ν : Measure (Fv F v)), SdR (Fv F v) ψ ν →
    μ (latTup v L) = ENNReal.ofReal (dualIndex F v c ^ (-(M : ℤ))) ∧
    ν (v.adicCompletionIntegers F : Set (Fv F v)) =
      ENNReal.ofReal (dualIndex F v c ^ (-(1 / 2 : ℝ))) ∧
    ∀ β : Fv F v, Valued.v β = 1 →
      (∀ (U : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (B : Set (Fv F v))
          (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
          {X | qTup σ J v X ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B →
          IsFibreFamily μ (qTup σ J v) id U ν B fib →
          fib β (latTup v L) =
            ENNReal.ofReal (densityValue (dualIndex F v c) (resCard F v) η M) ∧
          ∀ t : Fv F v, Valued.v (t - β) < 1 → fib t (latTup v L) = fib β (latTup v L)) ∧
      (∀ g : Fv F v → ℂ,
          IsContDensityOn μ (qTup σ J v) id ν {t | t ≠ 0} ((latTup v L).indicator 1) g →
          ∀ t : Fv F v, Valued.v (t - β) < 1 →
            g t = (densityValue (dualIndex F v c) (resCard F v) η M : ℂ))
example : densityValue 1 3 (-1) 1 = 4 / 3 := by
  simp [densityValue]; norm_num
example (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    Valued.v t ≤ WithZero.exp (0 : ℤ) ↔ t ∈ v.adicCompletionIntegers F := by
  rw [WithZero.exp_zero]; rfl
end GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes


