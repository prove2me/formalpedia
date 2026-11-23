-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:52.203794+00:00
-- url     : https://prove2.me/theorems/a73a75bd-95f6-42e8-bca3-341f5e5afd1f
-- title:
--   Self Dual Unramified Places
-- statement:
--   Definitions and structural lemmas for Self Dual Unramified Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualUnramifiedPlaces.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Defs
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def UnramifiedPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal
open Classical in

def eta (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if IsField (Fv F v ⊗[F] E) then -1 else 1
def resCard (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
def intToEv (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
  (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype
def maxOrder (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  letI := (intToEv F E v).toAlgebra
  (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring
variable {F E}
def IsSelfDualLattice (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F))
    (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (Fv F v ⊗[F] E) (L : Set (Fin M → Fv F v ⊗[F] E)) = ⊤ ∧
    ∀ y : Fin M → Fv F v ⊗[F] E, y ∈ L ↔ ∀ x ∈ L, hR (Fv F v) σ J x y ∈ maxOrder F E v
def IsLocalChar (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) : Prop :=
  Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ∃ t, ψ t ≠ 1
def DualExponent (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) (n : ℤ) : Prop :=
  ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔
    Valued.v t ≤ WithZero.exp n
end Defs
def LocalDensity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)), UnramifiedPlace F E v →
  ∀ (ψ : AddChar (Fv F v) ℂ), IsLocalChar v ψ → ∀ n : ℤ, DualExponent v ψ n →
  ∀ (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)), IsSelfDualLattice σ J v L →
  ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), SdW F E σ M J (Fv F v) ψ 1 μ →
  ∀ (ν : Measure (Fv F v)), SdR (Fv F v) ψ ν →
    μ {X | X 0 ∈ L} = ENNReal.ofReal ((resCard F v ^ n) ^ (-(M : ℝ))) ∧
    ν (v.adicCompletionIntegers F : Set (Fv F v)) =
      ENNReal.ofReal ((resCard F v ^ n) ^ (-(1 / 2 : ℝ))) ∧
    ∀ (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib →
    ∀ β : Fv F v, Valued.v β = 1 →
      fib β {X | qR (Fv F v) σ J (X 0) = β ∧ X 0 ∈ L} =
        ENNReal.ofReal ((resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) *
          (1 - eta F E v ^ M * (resCard F v ^ M)⁻¹)) ∧
      ∀ t : Fv F v, Valued.v (t - β) < 1 → fib t {X | X 0 ∈ L} = fib β {X | X 0 ∈ L}
def LocalMeasuresExist : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ), IsLocalChar v ψ →
    (∃ n : ℤ, DualExponent v ψ n) ∧
    ∃ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v))
      (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      SdW F E σ M J (Fv F v) ψ 1 μ ∧ SdR (Fv F v) ψ ν ∧
      IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces


