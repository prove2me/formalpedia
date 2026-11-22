-- Prove2me | Definitions.Def_MasulloRepair_PoleCells
-- name    : MasulloRepair_PoleCells
-- status  : Definition
-- author  : @ibecca
-- created : 2026-11-21T19:29:29.186686+00:00
-- url     : https://prove2.me/theorems/f425460d-eb62-4342-aba3-4fff029a4e0e
-- title:
--   Explicit reference pole profile and causal cell overlaps
-- statement:
--   For a real cell width $L$, define
--   $$g_k(x)=-\exp\!\left(-\frac{(k+1)L}{2}+\frac{x}{2}\right).$$
--   The causal cell-overlap integrals are
--   $$c_0(t)=\int_t^L g_0(x-t)g_0(x)\,dx,$$
--   $$c_{k+1}(t)=\int_0^t g_k(x-t+L)g_{k+1}(x)\,dx
--   +\int_t^L g_{k+1}(x-t)g_{k+1}(x)\,dx.$$
--   They are defined using real interval integrals for all real $L,t$. Their interpretation as successive causal cells uses $L>0$ and $0\le t\le L$.
--
--   These definitions contain only the exponential profile and the split integrals. The evaluated formulas, normalization, infinite summation, and any identification with an arithmetic projection are not built into the definitions.
-- source:
--   Yi, 'The real half moment on the first global cell, and where its compensation goes', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-d9bf59c5-5600-4dbe-9840-c2ca4f0e4293, the displayed formula g_p(kL+s)=-r^(k+1) exp(s/2) and the paragraph 'For f supported strictly in (0,L)'. The pointwise cell-overlap identity is the elementary integral calculation behind the two displayed reference pole-trace formulas; the global Hardy/theta identification is separate.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MasulloRepair

noncomputable section

/-- The normalized pole profile on the kth cell, in within-cell coordinate x. -/
def poleCell (L : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  -Real.exp (-((k : ℝ) + 1) * L / 2 + x / 2)

/-- Cell contribution to the autocorrelation at a displacement t in [0,L].
The first cell has no predecessor; later cells include the crossing term. -/
def poleCellOverlap (L : ℝ) : ℕ → ℝ → ℝ
  | 0, t => ∫ x in t..L, poleCell L 0 (x - t) * poleCell L 0 x
  | k + 1, t =>
      (∫ x in (0 : ℝ)..t, poleCell L k (x - t + L) * poleCell L (k + 1) x) +
      ∫ x in t..L, poleCell L (k + 1) (x - t) * poleCell L (k + 1) x

end
end MasulloRepair


