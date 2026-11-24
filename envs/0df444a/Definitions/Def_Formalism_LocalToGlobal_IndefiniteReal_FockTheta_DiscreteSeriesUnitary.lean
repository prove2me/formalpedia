-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FockTheta_DiscreteSeriesUnitary
-- name    : Formalism_LocalToGlobal_IndefiniteReal_FockTheta_DiscreteSeriesUnitary
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:14.797927+00:00
-- url     : https://prove2.me/theorems/b17730bc-8669-4e2c-8d0b-9644ee64720f
-- title:
--   Discrete Series Unitary
-- statement:
--   Definitions and structural lemmas for Discrete Series Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FockTheta/DiscreteSeriesUnitary.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
namespace Formalism.IndefR.Fock.SquareIntegrableRepresentations
abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
section Rep
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsURepOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Formalism.QuantumDeterminants.IsCRepOn G σ ∧ (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧
    ∀ v : H, ContinuousOn (fun g => σ g v) G
def IsIrredOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤
def coefOn {ε : Fin n → Bool} (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H) :
    Formalism.REAL.UJ ε → ℂ :=
  fun g => ⟪w, σ (umat g) v⟫_ℂ
def IsSqIntOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (Formalism.REAL.muG ε)
def IsFdeg {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => coefOn σ v w g * star (coefOn σ v' w' g)) μ ∧
    ∫ g, coefOn σ v w g * star (coefOn σ v' w' g) ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)
def fdegOf {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (w : H) : ℝ :=
  ‖w‖ ^ 4 / ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ
def IsWtOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ G →
    σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v
def CDom (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
    Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b
def IsKStableOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Prop :=
  ∀ g ∈ Formalism.REAL.Kset ε, ∀ v ∈ S, σ g v ∈ S
def IsKTypeOf (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧
    (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset ε) σ Λ v) ∧
    ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Formalism.REAL.Kset ε) σ μ v → CDom ε μ Λ
def vNormSq (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := Formalism.REAL.nsq (μ + (2 : ℝ) • Formalism.REAL.rhoC ε)
def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | Formalism.REAL.inUJ ε g}
def IsDS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ ∧
    (∃ S : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ vNormSq ε μ
def lowKSub (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Submodule ℂ H :=
  sSup {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}
end Rep
def LowKMultOne0 : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S'
end Formalism.IndefR.Fock.SquareIntegrableRepresentations
end


