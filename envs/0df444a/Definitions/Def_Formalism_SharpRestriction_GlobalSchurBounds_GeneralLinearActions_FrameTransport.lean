-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:52:27.772597+00:00
-- url     : https://prove2.me/theorems/5bd4fc4f-1f98-4d19-b885-720f183cc8c2
-- title:
--   Frame Transport
-- statement:
--   Definitions and structural lemmas for Frame Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FrameTransport.lean

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
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
structure GaugeFam (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) where

  μ : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Measure (HA (AF F) σ J)
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
def FrameRel {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E)
    (B : Matrix (Fin M) (Fin M') E) (g : HA (AF F) σ J) (g' : HA (AF F) σ J') : Prop :=
  ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      B.map (inclR (AF F)) =
    B.map (inclR (AF F)) *
      ((HA.mat (AF F) σ J' g' : GL (Fin M') (AF F ⊗[F] E)) : Matrix (Fin M') (Fin M') (AF F ⊗[F] E))
namespace GaugeFam
variable (G : GaugeFam F E σ)
def IsHaar : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHaarH F E σ M J (G.μ M J)
def BasisInv : Prop :=
  ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
    J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) →
    AllSome (fun e : HA (AF F) σ J ≃* HA (AF F) σ J' =>
      ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) fun e =>
      (G.μ M J).map e = G.μ M J'
def StepCompat : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    3 ≤ M + 1 → IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
    AllSome (IsCharAF F) fun ψ =>
    AllSome (IsXbetaMeasure F E σ (M + 1) J ψ β) fun νX =>
    AllSome (fun e : Hstab (AF F) σ J x ≃* HA (AF F) σ J' =>
      ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) fun e =>
      IsCompatible F E σ (M + 1) J x (G.μ (M + 1) J) ((G.μ M J').map e.symm) νX
def IsGauge : Prop := G.IsHaar ∧ G.BasisInv ∧ G.StepCompat
end GaugeFam
def FrameTransport (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
    ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
    ∀ μ'' : Measure (HA (AF F) σ J'), IsHaarH F E σ M J' μ'' →
      (μ''.map e.symm).IsHaarMeasure ∧
      ∀ 𝓕'', IsFDH F E σ M J' μ'' 𝓕'' →
        IsFundamentalDomain (HstabFin (AF F) σ J x) (e ⁻¹' 𝓕'') (μ''.map e.symm) ∧
        μ''.map e.symm (e ⁻¹' 𝓕'') = μ'' 𝓕''
def volHE (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) : ENNReal :=
  covolume (HFinIn (AF F) σ J) (HA (AF F) σ J) (G.μ M J)
def volH (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) : ℝ := (volHE G M J).toReal
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes


