-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:10.384245+00:00
-- url     : https://prove2.me/theorems/32179cb1-1a03-4904-958e-693f76769c80
-- title:
--   Step Transl
-- statement:
--   Definitions and structural lemmas for Step Transl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/StepTransl.lean

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
namespace PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct
section Coe
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
def toHR (g : HA R σ J) : HR R σ J := g
def ofHR (g : HR R σ J) : HA R σ J := g
end Coe
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
def FrameHyp (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E) : Prop :=
  IsHermND σ J ∧ β ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β ∧
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) ∧
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B ∧ IsHermND σ J'
def StepHomeo : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    FrameHyp F E σ M J J' x β B →
    ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
      Continuous e ∧ Continuous e.symm
def StepRat : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    FrameHyp F E σ M J J' x β B →
    ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
      ∀ g : Hstab (AF F) σ J x,
        g ∈ HstabFin (AF F) σ J x ↔ toHR (e g) ∈ HFinIn (AF F) σ J'
def StepTransl : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J),
    Continuous (fun g : HA (AF F) σ J => h * g)
end PI.FT


