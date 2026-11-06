-- Prove2me | Definitions.Def_BilateralProfit_MWU
-- name    : BilateralProfit_MWU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:30.697673+00:00
-- url     : https://prove2.me/theorems/f0891e3a-6422-48d2-87c8-69169c696492
-- title:
--   The Multiplicative Weights Algorithm with linear update
-- statement:
--   Let $\mathcal X$ be a finite set, $\gamma>0$ a learning rate and $\ell_{i,t}$ ($i\in\mathcal X$, $t=1,2,\dots$) a sequence of losses. The **Multiplicative Weights Algorithm** keeps weights $w_1(i)=1$ and updates
--   $$w_{t+1}(i)=w_t(i)\,(1-\gamma\,\ell_{i,t}),$$
--   playing the distribution $p_t=w_t/\sum_kw_t(k)$ in round $t$.
--
--   This is the algorithm of Proposition 4.7 (Arora, Hazan and Kale, Theorem 2.1); the paper applies it inside OneRound with decisions $(v,a')\in G_K\times\mathcal A$, costs $-h/H$ and learning rate $\eta H$ (p.21).
--
--   **Formalization Note** Rounds are indexed from $0$. Since $p_t$ depends only on earlier losses, a statement for every fixed loss sequence covers losses chosen after $p_t$ is played.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Proposition 4.7, p.21 (PDF 23) (Arora, Hazan, Kale, The Multiplicative Weights Update Method, Theorem 2.1); update rule as used on p.21

import Mathlib

namespace BilateralProfit

/-! # The Multiplicative Weights Algorithm (linear update)

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), Proposition 4.7, p.21
(PDF 23), quoting Arora, Hazan, Kale, *The Multiplicative Weights Update Method*, Theorem 2.1;
the update rule is the one the paper applies on p.21 ("multiplies each weight by
`1 − (ηH)(−h/H)`").

**Formalization Note.** Rounds are `t = 0, 1, …` (round `t + 1` of the paper). The losses are a
sequence `ℓ t i`; the weights are `w_0 ≡ 1` and `w_{t+1}(i) = w_t(i)(1 − γ ℓ_{i,t})`, and `p_t` is
`w_t` normalized. Since `p_t` depends only on `ℓ_0, …, ℓ_{t−1}`, a statement for every fixed
sequence covers losses chosen adaptively after seeing `p_t`. -/

variable {X : Type} [Fintype X]

/-- The weights `w_t` of the Multiplicative Weights Algorithm with learning rate `γ`. -/
noncomputable def mwWeight (γ : ℝ) (ℓ : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun i => mwWeight γ ℓ t i * (1 - γ * ℓ t i)

/-- The distribution `p_t = w_t / Σ_k w_t(k)` played in round `t`. -/
noncomputable def mwDist (γ : ℝ) (ℓ : ℕ → X → ℝ) (t : ℕ) (i : X) : ℝ :=
  mwWeight γ ℓ t i / ∑ k, mwWeight γ ℓ t k

end BilateralProfit


