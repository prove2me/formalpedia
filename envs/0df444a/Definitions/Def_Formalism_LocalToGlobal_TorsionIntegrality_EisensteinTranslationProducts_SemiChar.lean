-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_SemiChar
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_SemiChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:50:13.935145+00:00
-- url     : https://prove2.me/theorems/d7dd3a6e-113a-4f74-aeea-c7629782e94a
-- title:
--   Semi Char
-- statement:
--   Definitions and structural lemmas for Semi Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/SemiChar.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
def wZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
def wFactor (l z : ℂ) : ℂ := (1 - z / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))
def wSigma (L : PeriodPair) (z : ℂ) : ℂ := z * ∏' l : L.lattice, wFactor (l : ℂ) z
def wEta (L : PeriodPair) : ℂ →ₗ[ℝ] ℂ :=
  L.basis.constr ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)]
def area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|
def s2 (L : PeriodPair) : ℂ :=
  (wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁) / (L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁)
def sgStar (L : PeriodPair) (z : ℂ) : ℂ := wSigma L z * Complex.exp (-(s2 L) * z ^ 2 / 2)
def herm (L : PeriodPair) (z w : ℂ) : ℂ := z * conj w / (area L : ℂ)
def opU (L : PeriodPair) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * herm L z x - (Real.pi : ℂ) * herm L x x / 2)
open Classical in

def semiChar (L : PeriodPair) (ω : ℂ) : ℂ := if ω / 2 ∈ L.lattice then 1 else -1
def th0 (L : PeriodPair) (t : ℂ) (z : ℂ) : ℂ := opU L t (sgStar L) z / opU L t (sgStar L) 0
end Formalism.L2.Th1.F


