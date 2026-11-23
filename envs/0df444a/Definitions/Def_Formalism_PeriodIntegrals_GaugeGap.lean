-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GaugeGap
-- name    : Formalism_PeriodIntegrals_GaugeGap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:56.15104+00:00
-- url     : https://prove2.me/theorems/bac633a9-453c-4e72-adcf-ab89c9fc6feb
-- title:
--   Gauge Gap
-- statement:
--   Definitions and structural lemmas for Gauge Gap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GaugeGap.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GaugeGap
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
def IsQuadInv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  Module.finrank F E = 2 ∧ ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range
def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∃ G : GaugeFam F E σ, G.IsGauge
def CharAF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ
def HaarEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∃ μ : Measure (HA (AF F) σ J), IsHaarH F E σ M J μ
def Unimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ μ : Measure (HA (AF F) σ J), IsHaarH F E σ M J μ →
    ∀ g : HA (AF F) σ J, μ.map (fun h => h * g) = μ
def FrameIso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ →
    (∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
      J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) →
      ∃ e : HA (AF F) σ J ≃* HA (AF F) σ J',
        (∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ Continuous e ∧ Continuous e.symm) ∧
    (∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
      (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
      IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
      (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
      J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
      ∃ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
        (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) ∧
        Continuous e ∧ Continuous e.symm)
def XbetaEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ →
    ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (β : F),
      3 ≤ M + 1 → IsHermND σ J → β ≠ 0 → (∃ x : Fin (M + 1) → E, hE σ J x x = algebraMap F E β) →
      ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
      ∃ νX : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E), IsXbetaMeasure F E σ (M + 1) J ψ β νX
end PI.GaugeGap


