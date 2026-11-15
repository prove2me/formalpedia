-- Prove2me | Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_BinomialRatio
-- name    : RandOnlineSetCoverSqrt_LowerBound_Supplement_BinomialRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:12:13.912948+00:00
-- url     : https://prove2.me/theorems/a8f72ed8-4123-4701-baea-ada815f7a093
-- title:
--   The binomial ratio $R_m(\alpha)$
-- statement:
--   For an integer $m\ge0$ and a real $\alpha\ge1$ define
--   $$R_m(\alpha):=\max_{0\le k\le\lfloor m/\alpha\rfloor}\frac{\binom mk}{\binom{\lfloor\alpha k\rfloor}{k}},$$
--   where the term for $k=0$ equals $1$. It measures how many random candidate covers of size $\alpha k$ are needed to contain a fixed optimal cover of size $k$ with constant probability, in the worst case.
--
--   The binary entropy used alongside it is Mathlib's `Real.binEntropy`, $H(x)=-x\log x-(1-x)\log(1-x)$ with natural logarithm and $H(0)=H(1)=0$.
--
--   **Formalization Note** The maximum is a real `sup'` over $k\in\{0,\dots,\lfloor m/\alpha\rfloor\}$, with $\lfloor\cdot\rfloor$ the natural-number floor of a nonnegative real. For $\alpha\ge1$ and $k\ge1$ the denominator is at least $1$.
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, definition of R_m(α), proof of Lemma 6.2 context, printed p. 17 / PDF p. 18; H, printed p. 18 / PDF p. 19

import Mathlib

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement

/-- `R_m(α) := max_{0 ≤ k ≤ ⌊m/α⌋} binom(m,k) / binom(⌊αk⌋,k)` (printed p. 17 / PDF p. 18),
as a real number; the `k = 0` term is `1 / 1 = 1`. Used for real `α ≥ 1`. -/
noncomputable def Rm (m : ℕ) (α : ℝ) : ℝ :=
  (Finset.range (⌊(m : ℝ) / α⌋₊ + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    fun k => (Nat.choose m k : ℝ) / (Nat.choose ⌊α * (k : ℝ)⌋₊ k : ℝ)

end RandOnlineSetCoverSqrt.LowerBound.Supplement


