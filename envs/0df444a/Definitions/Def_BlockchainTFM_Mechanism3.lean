-- Prove2me | Definitions.Def_BlockchainTFM_Mechanism3
-- name    : BlockchainTFM_Mechanism3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:43.302671+00:00
-- url     : https://prove2.me/theorems/400b65b9-2795-41cf-9263-cd6c1ab5b0b6
-- title:
--   Mechanism 3: logit sampling allocation, Myerson payment plus quadratic variation term, miner revenue $\tilde r$
-- statement:
--   Fix a block size $k$, a logit parameter $m$, a scaling parameter $h$ and the constant $c=c_\rho$.
--
--   1. **Allocation.** $a_i(\mathbf b)=\sum_{t=1}^k\delta_t(i;\mathbf b)$, the probability that user $i$ is drawn in $k$ rounds of weighted sampling without replacement with weights $w_j=e^{mb_j}$ (§6.1). For $k=1$ this is the logit rule $a_i=e^{mb_i}/\sum_je^{mb_j}$ of Mechanism 1.
--   2. **Auxiliary mechanism** $M=(\mathbf a,\mathbf p,0)$, with $\mathbf p$ the dominant association of $\mathbf a$, written in the equivalent form (EC.137):
--   $$a_i(\mathbf b)\,p_i(\mathbf b)=a_i(\mathbf b)\,b_i-\int_0^{b_i}a_i(t,\mathbf b_{-i})\,dt.$$
--   3. **Variation term** (19)–(20):
--   $$\theta_i(b_i,\mathbf b_{-i})=-\tfrac12hb_i^2\Bigl(\frac{\sum_{j\ne i}b_j^2}{c_\rho(n-1)}-1\Bigr),\qquad \tilde r(\mathbf b)=\tfrac12h\Bigl(\sum_{i=1}^nb_i^2-\frac{\sum_{1\le i<j\le n}b_i^2b_j^2}{c_\rho(n-1)}\Bigr).$$
--   4. **Mechanism 3** $\tilde M=(\mathbf a,\tilde{\mathbf p},\tilde r)$:
--   $$\tilde p_i(\mathbf b)=\frac{1}{a_i(\mathbf b)}\Bigl[a_i(\mathbf b)\,b_i-\int_0^{b_i}a_i(t,\mathbf b_{-i})\,dt-\tfrac12hb_i^2\Bigl(\frac{\sum_{j\ne i}b_j^2}{c_\rho(n-1)}-1\Bigr)\Bigr].$$
--
--   Every $a_i$ is positive when $k\ge1$, so $\tilde p_i$ is well defined (p.29). Theorem 4 is about this mechanism.
--
--   **Formalization Note** The last term of the bracket is $+\theta_i(\mathbf b)$. The mechanism divides by $c(n-1)$; the theorems take $n\ge2$ and $c=c_\rho>0$. The integral $\int_0^{b_i}$ is an interval integral in the own bid with the other bids fixed.
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Mechanism 1 (15)–(17) p.26; (19)–(20) p.26; §6.1 pp.28–29; Mechanism 3 p.29; (EC.137) p.ec24

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Sampling

namespace BlockchainTFM

/-- **Allocation rule of Mechanism 3**, arXiv:2209.13099v7, §6.1 and Mechanism 3, pp.28–29:
`a_i(b) = ∑_{t=1}^{k} δ_t(i; b)` for `k`-round weighted sampling without replacement with
weights `w_j = e^{m b_j}`. For `k = 1` this is the logit rule (15) of Mechanism 1,
`e^{m b_i} / ∑_j e^{m b_j}`. -/
noncomputable def alloc3 {n : ℕ} (k : ℕ) (m : ℝ) (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  inclProb k (fun j => Real.exp (m * b j)) i

/-- **Auxiliary mechanism for block size `k`**, arXiv:2209.13099v7, §6, p.28 (and Mechanism 1,
p.26, for `k = 1`): `M = (a, p, 0)` with `a = alloc3 k m` and `p` its dominant association (7),
written in the equivalent form (EC.137), p.ec24:
`a_i p_i = a_i b_i − ∫₀^{b_i} a_i(t, b_{-i}) dt`, i.e.
`p_i = (1/a_i)(a_i b_i − ∫₀^{b_i} a_i(t, b_{-i}) dt)`.

**Formalization Note.** `a_i > 0` for every bid vector when `k ≥ 1`, so the division is the
paper's; (EC.137) equals (7) by integration by parts. The miner revenue is `0`. -/
noncomputable def auxMech (n k : ℕ) (m : ℝ) : TFM n where
  alloc := alloc3 k m
  pay b i := (alloc3 k m b i)⁻¹ *
    (alloc3 k m b i * b i - ∫ t in (0 : ℝ)..b i, alloc3 k m (Function.update b i t) i)
  rev _ := 0

/-- **Variation term `θ`**, arXiv:2209.13099v7, (19), p.26:
`θ_i(b_i, b_{-i}) = −½ h b_i² ( ∑_{j≠i} b_j² / (c (n−1)) − 1 )`, with `c = c_ρ` in the
mechanism. -/
noncomputable def theta {n : ℕ} (h c : ℝ) (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  -(1 / 2) * h * b i ^ 2 * ((∑ j ∈ Finset.univ.erase i, b j ^ 2) / (c * ((n : ℝ) - 1)) - 1)

/-- **Miner revenue `r̃`**, arXiv:2209.13099v7, (20), p.26:
`r̃(b) = ½ h ( ∑_i b_i² − ∑_{1≤i<j≤n} b_i² b_j² / (c (n−1)) )`, with `c = c_ρ` in the
mechanism. -/
noncomputable def minerRev {n : ℕ} (h c : ℝ) (b : Fin n → ℝ) : ℝ :=
  (1 / 2) * h *
    (∑ i, b i ^ 2 -
      (∑ i, ∑ j ∈ Finset.Ioi i, b i ^ 2 * b j ^ 2) / (c * ((n : ℝ) - 1)))

/-- **Mechanism 3** (TFM for general block size `k`), arXiv:2209.13099v7, p.29:
* `a_i(b) = ∑_{t=1}^{k} δ_t(i; b)` (`alloc3 k m`);
* `p̃_i(b) = (1/a_i(b)) [ a_i(b) b_i − ∫₀^{b_i} a_i(t, b_{-i}) dt
    − ½ h b_i² ( ∑_{j≠i} b_j² / (c_ρ(n−1)) − 1 ) ]`;
* `r̃(b) = ½ h ( ∑_i b_i² − ∑_{1≤i<j≤n} b_i² b_j² / (c_ρ(n−1)) )`.

The parameter `c` is `c_ρ` (`crho V₀`) in every theorem.

**Formalization Note.** The bracket's last term `−½ h b_i²(…)` is `+θ_i(b)` (`theta`). The
mechanism divides by `c(n−1)`; the theorems assume `n ≥ 2` and `c > 0`. -/
noncomputable def mech3 (n k : ℕ) (m h c : ℝ) : TFM n where
  alloc := alloc3 k m
  pay b i := (alloc3 k m b i)⁻¹ *
    (alloc3 k m b i * b i - (∫ t in (0 : ℝ)..b i, alloc3 k m (Function.update b i t) i) +
      theta h c b i)
  rev := minerRev h c

end BlockchainTFM


