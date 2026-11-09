-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_Hash
-- name    : SubsetSumPartialMatch_SubsetSum_Hash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:26.420957+00:00
-- url     : https://prove2.me/theorems/979b9086-8c31-4fbd-a8e0-ef1a0afbd975
-- title:
--   The power-of-two affine hash family
-- statement:
--   For a power of two $p$, the family $H_p$ consists of the maps $h_{\alpha,\beta}(k)=(\alpha k+\beta)\bmod p$ on $k\in\mathbb Z$, with $\alpha,\beta\in\mathbb Z_p$. For a power of two $q\le p$ put $I_q=\{0,\dots,q-1\}$. An integer $k$ **survives** if $h(k)\in I_q$. The probability of an event is taken under $\alpha,\beta$ independent and uniform in $\mathbb Z_p$. The multiplier $\alpha$ is not restricted to odd residues.
--
--   **Formalization Note** Residues are natural numbers below $p$ and the probability is the normalized count of pairs $(\alpha,\beta)$. The remainder is Lean's Euclidean remainder on $\mathbb Z$, which lies in $\{0,\dots,p-1\}$ for $p>0$.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, pp. 10–11, §2.2, family $H_p$ and filter $I_q$

import Mathlib

namespace SubsetSumPartialMatch.SubsetSum

/-- `k` survives the hash `h_{α,β}(k) = (αk + β) mod p` and the filter `I_q = {0, …, q-1}`.
The residues `α, β` are natural numbers below `p`. -/
def Survives (p q α β : ℕ) (k : ℤ) : Prop := ((α : ℤ) * k + β) % (p : ℤ) < q

open Classical in
/-- The probability of an event under `α, β` independent and uniform in `Z_p`. -/
noncomputable def hashProb (p : ℕ) (E : ℕ → ℕ → Prop) : ℝ :=
  (((Finset.range p ×ˢ Finset.range p).filter fun ab => E ab.1 ab.2).card : ℝ) / (p : ℝ) ^ 2

end SubsetSumPartialMatch.SubsetSum


