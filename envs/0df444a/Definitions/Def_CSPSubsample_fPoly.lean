-- Prove2me | Definitions.Def_CSPSubsample_fPoly
-- name    : CSPSubsample_fPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:18:31.451803+00:00
-- url     : https://prove2.me/theorems/f52de115-4b50-4ed4-941e-61c4e97343f4
-- title:
--   Algebraic version of a CSP: $x(\phi)$, $\tilde P_w$, the polynomial $f$, and the empirical mean $Z$
-- statement:
--   An assignment $\phi$ is represented by the vector $x(\phi)=(x_{i,a})_{i\in[n],a\in[q]}\in\mathbb R^{nq}$ with $x_{i,a}=\frac1n\mathbb I\{\phi_i=a\}$; $X=\{x(\phi)\}_{\phi\in[q]^n}$. For a constraint on $w=(i_1,\dots,i_k)\in W$,
--   $$
--   \tilde P_w(x)=n^k\sum_{a_1,\dots,a_k\in[q]}P_w(a_1,\dots,a_k)\prod_{j\in[k]}x_{i_j,a_j},\qquad f(x)=\frac1{n^k}\sum_{w\in W}\tilde P_w(x).
--   $$
--   Let $(i_t,a_t)_{t=1}^N$ be $N$ i.i.d. pairs with $\Pr[(i_t,a_t)=(i,a)]=x_{i,a}$. The empirical counts and mean are $N_{i,a}=\sum_{t=1}^N\mathbb I\{(i_t,a_t)=(i,a)\}$ and $Z_{i,a}=N_{i,a}/N$; $\mathcal D(x,N)$ denotes the law of $Z$.
--
--   $f$ is a multilinear polynomial of degree $k$ with $f(x(\phi))=\mathrm{val}(\phi)$, and with $f(Z)=\mathrm{val}_U(\phi)$ when the sample has no repeated variable; it is the device behind the concentration lemma.
--
--   **Formalization Note** $f$ is defined by the same formula on all of $\mathbb R^{n\times q}$ (the paper declares it on the simplex). For $x=x(\phi)$ a draw is $(i_t,\phi(i_t))$ with $i_t$ uniform, so $Z$ is computed from a uniform index sequence $s\in[n]^N$ with $a_t=\phi(s_t)$.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Definition 4.1 and the paragraph after it, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_CSPSubsample_Instance

set_option autoImplicit false

namespace CSPSubsample

/-- The **algebraic representation** `x(ϕ) = (x_{i,a})_{i ∈ [n], a ∈ [q]}` of an assignment,
`x_{i,a} = (1/n) 𝕀{ϕ_i = a}` (arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 4.1, p.8 =
PDF p.10). The set `X = {x(ϕ)}` is the range of this map. -/
noncomputable def xAlg {n q : ℕ} (ϕ : Fin n → Fin q) : Fin n → Fin q → ℝ :=
  fun i a => if ϕ i = a then 1 / (n : ℝ) else 0

/-- `P̃_w(x) = n^k ∑_{a_1,…,a_k ∈ [q]} P_w(a_1,…,a_k) ∏_{j ∈ [k]} x_{i_j,a_j}` for the
constraint on `w = (i_1, …, i_k)` (arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 4.1, p.8 =
PDF p.10). `n^k` is a power. -/
noncomputable def Ptilde {n k q : ℕ} (I : Instance n k q) (w : Fin k ↪ Fin n)
    (x : Fin n → Fin q → ℝ) : ℝ :=
  (n : ℝ) ^ k * ∑ a : Fin k → Fin q, I.P w a * ∏ j, x (w j) (a j)

/-- The multilinear extension `f(x) = (1/n^k) ∑_{w ∈ W} P̃_w(x)` of the CSP objective
(arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 4.1, p.8 = PDF p.10).

**Formalization Note** The paper declares `f` on the simplex `Δ_{qn}`; the same formula is
defined here on all of `ℝ^{n × q}` (the lemmas only evaluate it at `x(ϕ)` and at empirical means
`Z`, which lie in the simplex). The factor `n^k · … / n^k` is kept as printed. -/
noncomputable def fPoly {n k q : ℕ} (I : Instance n k q) (x : Fin n → Fin q → ℝ) : ℝ :=
  (∑ w : Fin k ↪ Fin n, Ptilde I w x) / (n : ℝ) ^ k

/-- The **empirical mean** `Z = (Z_{i,a})` of `N` pairs `(i_t, a_t)` drawn i.i.d. from the
categorical law `x(ϕ)`: `N_{i,a} = ∑_t 𝕀{(i_t, a_t) = (i, a)}`, `Z_{i,a} = N_{i,a}/N`
(arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 4.1 and the following paragraph, p.8 =
PDF p.10). Its law, for `s` uniform, is `D(x(ϕ), N)`.

**Formalization Note** Under `x(ϕ)` the pair `(i, a)` has probability `1/n` if `a = ϕ_i` and `0`
otherwise, so a draw is `(i_t, ϕ(i_t))` with `i_t` uniform on `[n]`. The sample is therefore the
index sequence `s : Fin N → Fin n` (uniform, see `probWR`, `expWR`), with `a_t = ϕ (s t)`. -/
noncomputable def Zemp {n q N : ℕ} (ϕ : Fin n → Fin q) (s : Fin N → Fin n) :
    Fin n → Fin q → ℝ :=
  fun i a => ((Finset.univ.filter fun t => s t = i ∧ ϕ (s t) = a).card : ℝ) / (N : ℝ)

end CSPSubsample


