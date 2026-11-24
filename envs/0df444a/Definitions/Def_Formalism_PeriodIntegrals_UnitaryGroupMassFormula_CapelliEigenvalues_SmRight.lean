-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_SmRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_SmRight
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:52.527703+00:00
-- url     : https://prove2.me/theorems/6cd112c2-3573-49f1-b49a-6d3cf11b11d0
-- title:
--   Sm Right
-- statement:
--   Definitions and structural lemmas for Sm Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CapelliEigenvalues/SmRight.lean

import Definitions.Def_Formalism_PeriodIntegrals_CapelliEig
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
noncomputable section
namespace PI.UnitaryGroupMassFormula.CapelliEig
def UHGrp : Prop :=
  ∀ (k r : ℕ), ∀ a ∈ UH (Hpk k r), IsUnit a ∧ a⁻¹ ∈ UH (Hpk k r) ∧ ∀ b ∈ UH (Hpk k r), a * b ∈ UH (Hpk k r)
def MulH : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)),
    IsDSHpk k r ε lam σ → ∀ x ∈ UH (Hpk k r), ∀ y ∈ UH (Hpk k r), σ (x * y) = (σ x).comp (σ y)
def SmRight : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)),
    IsDSHpk k r ε lam σ → ∀ v : Hs, v ∈ smoothVecs (k := k) (r := r) σ →
    ∀ c ∈ UH (Hpk k r), σ c v ∈ smoothVecs (k := k) (r := r) σ
def Loc : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H P Q : Matrix (Fin n) (Fin n) ℂ) (F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E) (u : ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → P * Q = 1 → H = Pᴴ * Formalism.REAL.Jm ε * P →
    (∀ x, Formalism.QuantumDeterminants.inUH H x → F₁ x = F₂ x) → Formalism.QuantumDeterminants.inUH H g →
    Formalism.QuantumDeterminants.capelliH H u F₁ g = Formalism.QuantumDeterminants.capelliH H u F₂ g
def CoefSm : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs), (∀ w, Q w ∈ smoothVecs (k := k) (r := r) σ) →
    ∀ Y : ℂ, ∀ g ∈ UH (Hpk k r),
      PI.CapelliEig.capC (k := k) (r := r) Y (fun x => P.comp ((σ x).comp Q)) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • P.comp ((σ g).comp Q)
end PI.UnitaryGroupMassFormula.CapelliEig
end


