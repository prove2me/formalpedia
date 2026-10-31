-- Prove2me | Definitions.Def_TransitoryQueue_Hn
-- name    : TransitoryQueue_Hn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:25.686852+00:00
-- url     : https://prove2.me/theorems/5a25ce6b-dc0d-4d39-8d43-a4b1338b1444
-- title:
--   Gaussian approximation $H_n$ of the arrival process
-- statement:
--   For arrival distributions $F_n$ with limit $G$, a Brownian bridge $B^{\mathrm{br},n}$ and a Brownian motion $\hat B$,
--
--   $$H_n(t)=npF_n(t)+\sqrt n\Bigl(pB^{\mathrm{br},n}_{G(t)}+\sqrt{p(1-p)}\,\hat B_{G(t)}\Bigr).$$
--
--   Under Assumption 2.1 ($F_n=G$) this is the paper's $H_n$. Under Assumption 2.5 ($F_n=G^{(n)}$) it is centred at $npG^{(n)}(t)$.
--
--   **Formalization Note** The paper centres the Assumption 2.5 branch at $np(G(t)+r_n(G))$; that statement is false (at $t=0$ the arrival process is $0$ while the centring is $np\,r_n(G)$, of order $\sqrt n$). $\hat B$ is evaluated at $G(t)\in[0,1]$.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Theorem 2.8, p.6

import Mathlib
open scoped NNReal

namespace TransitoryQueue

/-- The Gaussian approximation of the arrival process,
`H_n(t) = n p F_n(t) + √n (p B^{br,n}_{G(t)} + √(p(1-p)) B̂_{G(t)})`, where `F_n` is the arrival
distribution of the `n`-th system and `G` its limit.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Theorem 2.8, p.6.

**Formalization Note** One formula for both assumptions. Under Assumption 2.1, `F_n = G` and
this is the printed `H_n`. Under Assumption 2.5, `F_n = G^{(n)}`, and the centring is
`n p G^{(n)}(t)` instead of the printed `n p (G(t) + r_n(G))`, which is false (the paper's
statement fails at `t = 0`, where `A_n(0) = 0`). The Brownian motion `B̂` takes times in `ℝ≥0`;
`G(t) ∈ [0, 1]` for a distribution function, so `Real.toNNReal` does not truncate. -/
noncomputable def Hn {Ω : Type*} (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (p : ℝ) (n : ℕ)
    (Bbr : ℝ → Ω → ℝ) (Bh : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  n * p * F n t + Real.sqrt n * (p * Bbr (G t) ω + Real.sqrt (p * (1 - p)) * Bh (G t).toNNReal ω)

end TransitoryQueue


