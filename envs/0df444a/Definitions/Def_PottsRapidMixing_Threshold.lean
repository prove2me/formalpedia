-- Prove2me | Definitions.Def_PottsRapidMixing_Threshold
-- name    : PottsRapidMixing_Threshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:25.3844+00:00
-- url     : https://prove2.me/theorems/72b2ec34-23d5-44d8-bd29-7c8b91d189b9
-- title:
--   Tree uniqueness threshold $\beta_u(q,\mathbb T_\Delta)$ and the parameters of (2.1)
-- statement:
--   The *tree uniqueness threshold* of the $q$-state Potts model on the infinite $\Delta$-regular tree $\mathbb T_\Delta$ is
--   $$\beta_u(q,\mathbb T_\Delta)=\log\Bigl(1+\inf_{x>1}\frac{(x-1)(x^{\Delta-1}+q-1)}{x^{\Delta-1}-x}\Bigr),$$
--   and $p_u=1-e^{-\beta_u}$. Write $d=\Delta-1$ and $B=e^\beta$. The proof uses the parameters
--   $$p=\frac{B-1}{B},\quad \hat p=\frac{B-1}{B+q-1},\quad \theta=\frac{1+d\hat p}{2},\quad \tilde B=1+\frac{q\theta}{1-\theta},\quad r=\frac{B-1}{\tilde B-1},$$
--   the last two being (2.1), together with $s_\infty=r+(1-r)\hat p$ and $b_R=\sum_{j=0}^R d^j$.
--
--   These numbers fix the sprinkling level of the chain $M$ and the subcriticality level of the exploration.
--
--   **Formalization Note** $q$ is real, since Lemmas 2.8 and 3.5 use the formula at real $q\ge1$. The infimum is over the subtype $\{x>1\}$, which is nonempty, and its values are positive for $\Delta\ge3$, $q\ge1$. Verification files prove $\beta_u(2,\mathbb T_3)=\log 3$, $\beta_u>0$, and that $B<1+q/(\Delta-2)$ gives $0<r<1$, $B<\tilde B$ and $s_\infty=\hat p/\theta<1/d$.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, p.1 (β_u), p.9 (p, p̂, θ, (2.1)), p.13 (p_u), p.16 (s_∞, b_R)

import Mathlib

namespace PottsRapidMixing

/-- The tree uniqueness threshold of the `q`-state Potts model on the infinite Δ-regular tree,
`β_u(q, T_Δ) = log(1 + inf_{x>1} (x − 1)(x^{Δ−1} + q − 1)/(x^{Δ−1} − x))`
(Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.1).

**Formalization Note.** `q` is real: the formula is the paper's at every `q ≥ 1`, which Lemmas 2.8
and 3.5 use. The infimum runs over the subtype `{x // 1 < x}`, which is nonempty, and for `Δ ≥ 3`,
`q ≥ 1` the values are positive, so the real `⨅` is the true infimum. -/
noncomputable def betaU (q : ℝ) (Δ : ℕ) : ℝ :=
  Real.log (1 + ⨅ x : {x : ℝ // 1 < x},
    ((x : ℝ) - 1) * ((x : ℝ) ^ (Δ - 1) + q - 1) / ((x : ℝ) ^ (Δ - 1) - (x : ℝ)))

/-- `p_u = 1 − e^{−β_u}` (arXiv:2610.42059, p.13). -/
noncomputable def pU (q : ℝ) (Δ : ℕ) : ℝ := 1 - Real.exp (-betaU q Δ)

/-- The percolation parameter `p = (B − 1)/B = 1 − e^{−β}`, with `B = e^β` (arXiv:2610.42059, p.9). -/
noncomputable def pOf (β : ℝ) : ℝ := 1 - Real.exp (-β)

/-- `p̂ = (B − 1)/(B + q − 1)`, with `B = e^β` (arXiv:2610.42059, p.9). -/
noncomputable def pHat (q β : ℝ) : ℝ := (Real.exp β - 1) / (Real.exp β + q - 1)

/-- `θ = (1 + d p̂)/2`, with `d = Δ − 1` (arXiv:2610.42059, p.9). -/
noncomputable def thetaOf (Δ : ℕ) (q β : ℝ) : ℝ := (1 + ((Δ : ℝ) - 1) * pHat q β) / 2

/-- `B̃ = 1 + qθ/(1 − θ)`, (2.1) (arXiv:2610.42059, p.9). -/
noncomputable def BtildeOf (Δ : ℕ) (q β : ℝ) : ℝ :=
  1 + q * thetaOf Δ q β / (1 - thetaOf Δ q β)

/-- `r = (B − 1)/(B̃ − 1)`, (2.1) (arXiv:2610.42059, p.9): the sprinkling level of the chain `M` that
§§2–3 fix. -/
noncomputable def rOf (Δ : ℕ) (q β : ℝ) : ℝ := (Real.exp β - 1) / (BtildeOf Δ q β - 1)

/-- `s_∞ = r + (1 − r) p̂` (arXiv:2610.42059, p.16). Lemmas 3.4–3.5 fix `s ∈ (s_∞, 1/d)`. -/
noncomputable def sInfty (Δ : ℕ) (q β : ℝ) : ℝ := rOf Δ q β + (1 - rOf Δ q β) * pHat q β

/-- `b_R = ∑_{j=0}^{R} d^j`, with `d = Δ − 1` (arXiv:2610.42059, p.16). -/
noncomputable def bR (Δ R : ℕ) : ℝ := ∑ j ∈ Finset.range (R + 1), ((Δ : ℝ) - 1) ^ j

end PottsRapidMixing


