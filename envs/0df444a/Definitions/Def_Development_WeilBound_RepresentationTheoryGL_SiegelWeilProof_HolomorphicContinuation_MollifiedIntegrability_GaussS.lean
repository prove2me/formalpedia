-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:34.825815+00:00
-- url     : https://prove2.me/theorems/115afaec-dffe-48b4-9792-c53dade97c05
-- title:
--   Gauss S
-- statement:
--   Definitions and structural lemmas for Gauss S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussS.lean

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
open MeasureTheory Matrix MvPolynomial
namespace PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
def Amat (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * t * sgn ε a) • bᵀ
def IntegP : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable fun x : Fin m → Fin n → ℂ => evX P x * gs c x
def Wick : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ (M : PX m n) (a : Fin m) (i : Fin n),
      secN ε c t (X (a, i, true) * M) b = ∑ j, (Amat ε c t b a)⁻¹ j i * secN ε c t (pderiv (a, j, false) M) b
def Rot : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, (∀ k, k.2.2 = true → d k = 0) → d ≠ 0 →
      secN ε c t (monomial d 1) b = 0
def Base : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    secN ε c t 1 b = ∏ a, ((Real.pi : ℂ) ^ n / (Amat ε c t b a).det)
end PositivityTheory.Rg.Sw.WR.G


