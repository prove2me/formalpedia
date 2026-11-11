-- Prove2me | Definitions.Def_TensorBeyond_Main_Polys
-- name    : TensorBeyond_Main_Polys
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:11.658632+00:00
-- url     : https://prove2.me/theorems/90a3f3ef-918d-4bff-ba0d-74655ea8a765
-- title:
--   The polynomials $R_t$, $T_t$, $h_{2e}$, spider polynomials $s_r$, and the constraint systems $\mathcal P_\xi$ and step 1 of Algorithm 1
-- statement:
--   Fix a sample $v_1,\dots,v_m\in\{\pm1\}^n$. All polynomials below are in $x\in\mathbb R^n$.
--
--   - $\langle v_i,x\rangle=\frac1n v_i^\top x$ (normalized) and $v_i^\top x$ (unnormalized).
--   - $R_t(x)=\sum_i\langle v_i,x\rangle^t$ (normalized; §1–6, Appendix B), and $T_t(x)=\sum_i(v_i^\top x)^t$ (unnormalized; §7.4).
--   - The **noise polynomial** $h_{2e}(x)=\sum_{i\ne j}(v_i^\top v_j)(v_i^\top x)^e(v_j^\top x)^e$ with the unnormalized dot product of §7 and Appendix A, so $h_4$ is $e=2$ and $h_6$ is $e=3$.
--   - The **$r$-legged spider polynomial** (Definition 2.1)
--   $$s_r(x)=\binom nr^{-1}\sum_{i\in[m]}\ \sum_{S\subseteq[n],\,|S|=r}v_i[S]\,x[S],\qquad v[S]=\prod_{u\in S}v_u .$$
--   - $\langle T,x^{\otimes k}\rangle=n^{-k}\sum_{u\in[n]^k}T_u\,x_{u_1}\cdots x_{u_k}$ as a polynomial.
--   - The program $\mathcal P_\xi$ of (5.1) is the inequality $\langle T,x^{\otimes k}\rangle\ge1+\xi$ with the Boolean equalities $x_u^2=1$.
--   - Step 1 of Algorithm 1 for $k=3$, in the unnormalized form of §7 and Appendix A with slack $\xi=O(n^{3/2}\sqrt{m\log m})$ written $Kn^{3/2}\sqrt{m\log m}$: the inequality $n^3\langle T,x^{\otimes3}\rangle\ge n^3-Kn^{3/2}\sqrt{m\log m}$, the constraints $(s^\top x)^2\le0.01\,n^2$ (that is, $\langle x,s\rangle^2\le0.01$) for every vector $s$ of the list $S$ found so far, and $x_u^2=1$.
--
--   **Formalization Note.** `R v t`, `Tpow v t`, `hNoise v e`, `spider v r`, `tensorPoly k v`, `progP k v ξ`, `prog3 v K S`. $\log$ is the natural logarithm; $n^{3/2}$ is `Real.rpow`; $\binom nr^{-1}$ is $0$ when $n<r$ (the sum is empty then).
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 4 (PDF 6), (2.3); p. 6 (PDF 8), Definition 2.1; p. 29 (PDF 31), (5.1) and Algorithm 1; p. 41 (PDF 43); p. 54 (PDF 56)

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS

set_option autoImplicit false

/-!
# The polynomials and constraint systems of the analysis

Jha, Mazzali, Xu, *Tensor Decomposition Beyond the Spectral Threshold*, STOC 2027 submission
(held manuscript, sha256 988d801c…): `R_t` and `h_{2t−2}` (p. 4, (2.3)), the spider polynomial
`s_r` (Definition 2.1, p. 6, restated p. 32), the program `𝒫_ξ` (5.1) (p. 29), `h_4` (p. 41),
`T_t` and `h_6` (p. 54), step 1 of Algorithm 1 (p. 29).

Conventions. All polynomials are in `x = (x_u)_{u ∈ [n]}` with coefficients depending on the
sample `v`.
* `linPoly w = ∑_u w_u x_u` is the unnormalized `wᵀx`; `ipPoly w = (1/n) wᵀx` is the normalized
  `⟨w, x⟩`.
* `R v t = ∑_i ⟨v_i, x⟩^t` (normalized, §1–6, Appendix B).
* `Tpow v t = ∑_i (v_iᵀx)^t` is `T_t` of §7.4 (unnormalized, §7 and Appendix A).
* `hNoise v e = ∑_{i ≠ j} (v_iᵀv_j) (v_iᵀx)^e (v_jᵀx)^e` is `h_{2e}` with the unnormalized dot
  product (§7, Appendix A): `h_4 = hNoise v 2`, `h_6 = hNoise v 3`.
* `spider v r = binom(n, r)^{-1} ∑_i ∑_{S ⊆ [n], |S| = r} v_i[S] x[S]` (Definition 2.1).
* `tensorPoly k v = ⟨T, x^{⊗k}⟩ = n^{-k} ∑_{u ∈ [n]^k} T_u x_{u_1} ⋯ x_{u_k}` (normalized).
* `progP k v ξ = [⟨T, x^{⊗k}⟩ − 1 − ξ]`: the inequality of `𝒫_ξ` (5.1); the Boolean equalities
  are part of every system (`Def_TensorBeyond_Main_SoS`).
* `prog3 v K S`: the constraints of step 1 of Algorithm 1 for `k = 3` in the unnormalized form
  of §7 and Appendix A, with slack `ξ = O(n^{3/2} √(m log m))` written `K n^{3/2} √(m log m)`:
  `n³ ⟨T, x^{⊗3}⟩ ≥ n³ − K n^{3/2} √(m log m)`, and `(sᵀx)² ≤ 0.01 n²` (i.e. `⟨x, s⟩² ≤ 0.01`)
  for each vector `s` of the list `S` found so far.
-/

namespace TensorBeyond.Main

open MvPolynomial

/-- `wᵀx = ∑_u w_u x_u` (unnormalized). -/
noncomputable def linPoly {n : ℕ} (w : Fin n → ℝ) : Poly n :=
  ∑ u, C (w u) * X u

/-- `⟨w, x⟩ = (1/n) wᵀx` (normalized). -/
noncomputable def ipPoly {n : ℕ} (w : Fin n → ℝ) : Poly n :=
  C (1 / (n : ℝ)) * linPoly w

/-- `R_t(x) = ∑_i ⟨v_i, x⟩^t` (normalized). -/
noncomputable def R {n m : ℕ} (v : Sample n m) (t : ℕ) : Poly n :=
  ∑ i, ipPoly (vec v i) ^ t

/-- `T_t(x) = ∑_i (v_iᵀx)^t` (unnormalized, §7.4). -/
noncomputable def Tpow {n m : ℕ} (v : Sample n m) (t : ℕ) : Poly n :=
  ∑ i, linPoly (vec v i) ^ t

/-- `h_{2e}(x) = ∑_{i ≠ j} (v_iᵀv_j)(v_iᵀx)^e (v_jᵀx)^e` (unnormalized). -/
noncomputable def hNoise {n m : ℕ} (v : Sample n m) (e : ℕ) : Poly n :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
    C (dot (vec v i) (vec v j)) * linPoly (vec v i) ^ e * linPoly (vec v j) ^ e

/-- The `r`-legged spider polynomial `s_r(x) = binom(n,r)^{-1} ∑_i ∑_{|S| = r} v_i[S] x[S]`. -/
noncomputable def spider {n m : ℕ} (v : Sample n m) (r : ℕ) : Poly n :=
  C (1 / ((n.choose r : ℕ) : ℝ)) *
    ∑ i, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      C (∏ u ∈ S, vec v i u) * ∏ u ∈ S, X u

/-- `⟨T, x^{⊗k}⟩ = n^{-k} ∑_{u ∈ [n]^k} T_u ∏_a x_{u_a}` as a polynomial. -/
noncomputable def tensorPoly (k : ℕ) {n m : ℕ} (v : Sample n m) : Poly n :=
  C (1 / (n : ℝ) ^ k) * ∑ u : Fin k → Fin n, C (tensorEntry k v u) * ∏ a, X (u a)

/-- The inequality of `𝒫_ξ` (5.1): `⟨T, x^{⊗k}⟩ ≥ 1 + ξ`. -/
noncomputable def progP (k : ℕ) {n m : ℕ} (v : Sample n m) (ξ : ℝ) : List (Poly n) :=
  [tensorPoly k v - C (1 + ξ)]

/-- Step 1 of Algorithm 1 for `k = 3`, unnormalized: `n³⟨T, x^{⊗3}⟩ ≥ n³ − K n^{3/2} √(m log m)`
and `(sᵀx)² ≤ 0.01 n²` for every `s ∈ S`. -/
noncomputable def prog3 {n m : ℕ} (v : Sample n m) (K : ℝ) (S : List (Fin n → ℝ)) :
    List (Poly n) :=
  (C ((n : ℝ) ^ 3) * tensorPoly 3 v -
      C ((n : ℝ) ^ 3 - K * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * Real.log m))) ::
    S.map (fun s => C ((1 / 100 : ℝ) * (n : ℝ) ^ 2) - linPoly s ^ 2)

end TensorBeyond.Main


