-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:11.087525+00:00
-- url     : https://prove2.me/theorems/7cb95db1-2b36-41ea-9a27-7a79d2cb7092
-- title:
--   Dens Defs
-- statement:
--   Definitions and structural lemmas for Dens Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DensDefs.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
def hinv (T : Matrix (Fin n) (Fin n) ℂ) : E n := fun i j => (T i j).re + (T i j).im
def ip (y y' : E n) : ℝ := ∑ a, ∑ b, y a b * y' a b
def qX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : E n := hinv (gramX ε x)
def detQ (ε : Fin m → Bool) : PX m n := (Matrix.of fun i j => Qp ε i j).det
def FP (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (y : E n) : ℂ :=
  ∫ x, evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))
def AlgA : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool), (∀ (y : E n) (x : Fin m → Fin n → ℂ),
      (herm y * gramX ε x).trace = (ip y (qX ε x) : ℂ)) ∧
    (∀ x : Fin m → Fin n → ℂ, herm (qX ε x) = gramX ε x) ∧ (∀ y : E n, hinv (herm y) = y) ∧
    (∀ x : Fin m → Fin n → ℂ, evX (detQ ε) x = (gramX ε x).det) ∧ Continuous (qX (n := n) ε)
def IntG : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable (fun x => evX P x * gs c x)
def DerivF : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (P : PX m n) (N : ℕ),
    Continuous (FP ε c t P) ∧
    Delta^[N] (FP ε c t P) = FP ε c t ((MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε) ^ N * P)
def MollId : Prop :=
  ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure X) [SFinite μ] (Ψ : X → ℂ) (qq : X → E n), Integrable Ψ μ →
    Measurable qq → ∀ t : ℝ, t ≠ 0 →
    Integrable (fun y : E n => ∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) →
    ∀ ψ : E n → ℂ, Continuous ψ → HasCompactSupport ψ →
      ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ β, ψ β * (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * Complex.exp (-(Complex.I * t * ip β y)))
end PositivityTheory.Rg.Sw.WR.D


