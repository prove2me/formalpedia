-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_CapelliEig
-- name    : Formalism_PeriodIntegrals_CapelliEig
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:44.740591+00:00
-- url     : https://prove2.me/theorems/9b12a9ec-d803-4e3c-ba7b-f560053229a2
-- title:
--   Capelli Eig
-- statement:
--   Definitions and structural lemmas for Capelli Eig, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/CapelliEig.lean

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace PI.CapelliEig
open PI.UpqRep
def capC {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V :=
  Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + ((2 * r + k : ℕ) : ℂ) / 2) F
def IsKFinCoefH {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (P : H →L[ℂ] Wp) (Q : Wq →L[ℂ] H), (∀ w, IsKFinHpk (k := k) (r := r) σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) σ (ContinuousLinearMap.adjoint P x)) ∧ ∀ g, f g = P.comp ((σ g).comp Q)
def IsKFinCoefT {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ a ∈ UH (Hpk k r), ∃ b ∈ UH (Hpk k r), IsKFinCoefH σ (fun g => f (a * g * b))
def CapEig : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp), IsKFinCoefT σ f →
    ∀ Y : ℂ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      capC (k := k) (r := r) Y f g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • f g
end PI.CapelliEig
end


