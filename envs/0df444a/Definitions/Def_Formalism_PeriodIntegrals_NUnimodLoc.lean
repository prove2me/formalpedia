-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_NUnimodLoc
-- name    : Formalism_PeriodIntegrals_NUnimodLoc
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:27.127818+00:00
-- url     : https://prove2.me/theorems/a65d9439-4b79-4b5b-9efd-484fdec910dc
-- title:
--   NUnimod Loc
-- statement:
--   Definitions and structural lemmas for NUnimod Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/NUnimodLoc.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
namespace PI.NUnimodLoc
abbrev uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
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
structure IsFrameJ {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z0 = 0
  fz : ∀ a, hJ ε (f a) z0 = 0
  zz : hJ ε z0 z0 = -1
  ww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0
  ew : ∀ c a, hJ ε (e c) (wf a) = 0
  fw : ∀ c a, hJ ε (f c) (wf a) = 0
  zw : ∀ a, hJ ε z0 (wf a) = 0
def NUnimodLoc : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 z : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
    IsFrameJ ε e f wf z0 → c ≠ 0 → z0 = c • z →
    ∀ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ → μ ≠ 0 → μ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}ᶜ = 0 →
      (∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => s * x) = μ) →
      ∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => x * s) = μ
end PI.NUnimodLoc


