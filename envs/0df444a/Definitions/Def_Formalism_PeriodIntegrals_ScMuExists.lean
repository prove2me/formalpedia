-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
-- name    : Formalism_PeriodIntegrals_ScMuExists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:47.547027+00:00
-- url     : https://prove2.me/theorems/49a4f79a-0a98-43b3-9919-4d4883b97899
-- title:
--   Sc Mu Exists
-- statement:
--   Definitions and structural lemmas for Sc Mu Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ScMuExists.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix
namespace PI.ScMuExists
section Real
variable {n r : ℕ}
def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)
def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})
def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r
def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r
end Real
section Inst
variable (I : Formalism.MainNotions.S.AutInst)
def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)
variable {r : ℕ}
def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}
abbrev muInf : Measure I.Ginf := Measure.pi fun v => Formalism.REAL.muG (I.ε v)
def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ
def IsQuotMeasS (μS ν : Measure I.Ginf) : Prop :=
  ∀ f : I.Ginf → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂(muInf I) = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν
def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}
end Inst
def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0 →
    ∃ muN muH nuQ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) muN ∧
      IsHaarOnSet I (Hset I (Set.range e ∪ Set.range f ∪ {z})) muH ∧
      IsQuotMeasS I ((muN.prod muH).map (fun p => p.1 * p.2)) nuQ
end PI.ScMuExists


