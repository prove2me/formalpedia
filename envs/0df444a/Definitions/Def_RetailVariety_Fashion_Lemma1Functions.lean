-- Prove2me | Definitions.Def_RetailVariety_Fashion_Lemma1Functions
-- name    : RetailVariety_Fashion_Lemma1Functions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:13.714605+00:00
-- url     : https://prove2.me/theorems/85e111a4-ee9f-4db6-b7da-38990b95f710
-- title:
--   Lemma 1, (9)–(11): $f(\delta)$, $g_I(\delta)$, $g_T(\delta)$ and the ratios $h_I=g_I/f$, $h_T=g_T/f$
-- statement:
--   These are the functions of Lemma 1 (p. 1503). Fix the model of `RetailVariety.Fashion.Model`, a category $v$ with no-purchase preference $v_0$, and an assortment $S$. For a real $\delta$ (the preference of a variant to be added to $S$) set
--   $$f(\delta)=\sum_{j\in S}v_j+\delta+v_0,\tag{9}$$
--   $$g_I(\delta)=(p-c)\lambda\Big(\sum_{j\in S}v_j+\delta\Big)-\frac{p\sigma\lambda^{\beta}e^{-z^2/2}}{\sqrt{2\pi}}\Big(\sum_{j\in S}v_j^{\beta}+\delta^{\beta}\Big)\Big(\sum_{j\in S}v_j+\delta+v_0\Big)^{1-\beta},\tag{10}$$
--   $$g_T(\delta)=\lambda\Big(\sum_{j\in S}\big(pv_j-cf(\delta)\big)^{+}+\big(p\delta-cf(\delta)\big)^{+}\Big),\tag{11}$$
--   and
--   $$h_I(\delta)=\frac{g_I(\delta)}{f(\delta)},\qquad h_T(\delta)=\frac{g_T(\delta)}{f(\delta)}.$$
--
--   $h_I(\delta)$ and $h_T(\delta)$ are the store profits after adding to $S$ a variant of preference $\delta$; Lemma 1 asserts they are quasi-convex, and the proof of Theorem 3 uses $h_I$ and $h_T$ for the category $w$.
--
--   **Formalization Note.** In (11) as printed, the factor $\lambda$ stands before the sum only; here it multiplies both terms, which is the reading under which $h_T(v_j)=\pi_T(S\cup\{j\},v)$ (p. 1503) holds. Powers are `Real.rpow`, so $\delta^{\beta}=1$ at $\delta=0,\beta=0$.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1503, Lemma 1, (9), (10), (11)

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Structure_Model

namespace RetailVariety.Fashion

/-- `g_I(δ) = (p − c)λ(∑_{j∈S} v_j + δ) − (pσλ^β e^{−z²/2}/√(2π)) (∑_{j∈S} v_j^β + δ^β) f(δ)^{1−β}`,
(10), p. 1503. -/
noncomputable def gNumI (p c lam σ β : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (δ : ℝ) : ℝ :=
  (p - c) * lam * (∑ j ∈ S, v j + δ)
    - safetyCoeff p c lam σ β * (∑ j ∈ S, v j ^ β + δ ^ β) * RetailVariety.Structure.fDen v v0 S δ ^ (1 - β)

/-- `g_T(δ) = λ (∑_{j∈S} (p v_j − c f(δ))^+ + (pδ − c f(δ))^+)`, (11), p. 1503. The factor `λ`
multiplies both terms (the printed (11) closes the sum before the second term; `h_T = g_T/f` equals
`π_T(S ∪ {j}, v)` at `δ = v_j` only with `λ` on both). -/
noncomputable def gNumT (p c lam : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (δ : ℝ) : ℝ :=
  lam * (∑ j ∈ S, max (p * v j - c * RetailVariety.Structure.fDen v v0 S δ) 0 + max (p * δ - c * RetailVariety.Structure.fDen v v0 S δ) 0)

/-- `h_I(δ) = g_I(δ)/f(δ)`, Lemma 1, p. 1503. -/
noncomputable def hI (p c lam σ β : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (δ : ℝ) : ℝ :=
  gNumI p c lam σ β v v0 S δ / RetailVariety.Structure.fDen v v0 S δ

/-- `h_T(δ) = g_T(δ)/f(δ)`, Lemma 1, p. 1503. -/
noncomputable def hT (p c lam : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (δ : ℝ) : ℝ :=
  gNumT p c lam v v0 S δ / RetailVariety.Structure.fDen v v0 S δ

end RetailVariety.Fashion


