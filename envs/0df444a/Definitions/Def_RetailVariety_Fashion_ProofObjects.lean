-- Prove2me | Definitions.Def_RetailVariety_Fashion_ProofObjects
-- name    : RetailVariety_Fashion_ProofObjects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:22.361529+00:00
-- url     : https://prove2.me/theorems/bd668091-e341-4849-8948-24b86fdc6b28
-- title:
--   Proof of Theorem 3: the functions $g$, $g^T$ and the vector $w'$
-- statement:
--   These are the auxiliary objects of the proof of Theorem 3 (p. 1506). For a constant $L>0$ (in the proof $L=\sum_{j=1}^r v_j+v_0$) put
--   $$g(x)=\frac{(p-c)\lambda}{L}\,x-\frac{p\sigma\lambda^{\beta}e^{-z^2/2}}{\sqrt{2\pi}\,L^{\beta}}\,x^{\beta},\qquad g^{T}(x)=\frac{\lambda}{L}\,(px-cL)^{+}.$$
--
--   For a category $w\in\mathbb R^n$, an integer $r\le n$, an index $t\le r$ and $0<\delta\le 1$, $w'$ is the $r$-dimensional vector
--   $$w'=(w_1,w_2,\dots,w_{t-1},\ \delta w_t,\ 0,\dots,0).$$
--
--   With $q_j=v_j/L$, the profits $\pi_I(A_r,v)$ and $\pi_T(A_r,v)$ are $\sum_{j\le r}g(v_j)$ and $\sum_{j\le r}g^T(v_j)$; the vector $w'$ is the feasible fractional assortment of category $w$ that the proof compares with $A_r$.
--
--   **Formalization Note.** `wPrime w r t θ hr : Fin r → ℝ` is 0-based: its entry $j$ is $w_j$ for $j<t$, $\theta w_t$ for $j=t$, and $0$ for $j>t$. So the Lean index `t` is the paper's $t-1$ and `θ` is the paper's $\delta$ (the paper reuses the letter $\delta$ of Lemma 1). The hypothesis `hr : r ≤ n` embeds `Fin r` into `Fin n`.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1506, proof of Theorem 3 (g, w′, g^T)

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model

namespace RetailVariety.Fashion

/-- The function `g(x) = ((p − c)λ/L) x − (pσλ^β e^{−z²/2}/(√(2π) L^β)) x^β` of the proof of
Theorem 3, p. 1506 (with `L = ∑_{j=1}^r v_j + v_0` supplied by the caller). -/
noncomputable def gFun (p c lam σ β L : ℝ) (x : ℝ) : ℝ :=
  (p - c) * lam / L * x - safetyCoeff p c lam σ β / L ^ β * x ^ β

/-- The function `g^T(x) = (λ/L)(px − cL)^+` of the proof of Theorem 3, p. 1506. -/
noncomputable def gFunT (p c lam L : ℝ) (x : ℝ) : ℝ :=
  lam / L * max (p * x - c * L) 0

/-- The `r`-dimensional vector `w′ = (w_1, …, w_{t−1}, δ w_t, 0, …, 0)` of p. 1506, 0-based:
for `j : Fin r` (with `r ≤ n`), `w′ j = w j` if `j < t`, `θ · w t` if `j = t`, and `0` if `j > t`.
Here the Lean `t` is the paper's `t − 1` and `θ` is the paper's `δ`. -/
noncomputable def wPrime {n : ℕ} (w : Fin n → ℝ) (r t : ℕ) (θ : ℝ) (hr : r ≤ n) (j : Fin r) : ℝ :=
  if j.val < t then w (Fin.castLE hr j)
  else if j.val = t then θ * w (Fin.castLE hr j)
  else 0

end RetailVariety.Fashion


