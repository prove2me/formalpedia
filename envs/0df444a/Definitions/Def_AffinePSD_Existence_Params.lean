-- Prove2me | Definitions.Def_AffinePSD_Existence_Params
-- name    : AffinePSD_Existence_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:22.905675+00:00
-- url     : https://prove2.me/theorems/3408b0c1-7743-43c2-bfc6-7771458e764d
-- title:
--   Truncation function, admissible parameter set (α, b, β^{ij}, c, γ, m, μ) and the functions F, R of (2.16)–(2.17) (Definition 2.3)
-- statement:
--   A **truncation function** is a bounded continuous map $\chi:S_d\to S_d$ with $\chi(\xi)=\xi$ in a neighbourhood of $0$.
--
--   A **parameter set** $(\alpha,b,\beta^{ij},c,\gamma,m,\mu)$ consists of matrices $\alpha,b,\gamma$, a family $\beta^{ij}$ ($1\le i,j\le d$), a number $c$, a Borel measure $m$ on $S_d^+\setminus\{0\}$ and a $d\times d$ matrix $\mu=(\mu_{ij})$ of finite signed measures on $S_d^+\setminus\{0\}$. With it come
--   $$B(x)=\sum_{i,j}\beta^{ij}x_{ij},\qquad B^\top_{ij}(u)=\langle\beta^{ij},u\rangle,\qquad M(x,d\xi)=\frac{\langle x,\mu(d\xi)\rangle}{\|\xi\|^2\wedge1},$$
--   $$A_{ijkl}(x)=x_{ik}\alpha_{jl}+x_{il}\alpha_{jk}+x_{jk}\alpha_{il}+x_{jl}\alpha_{ik},$$
--   $$F(u)=\langle b,u\rangle+c-\int_{S_d^+\setminus\{0\}}\big(e^{-\langle u,\xi\rangle}-1\big)\,m(d\xi),$$
--   $$R(u)=-2u\alpha u+B^\top(u)+\gamma-\int_{S_d^+\setminus\{0\}}\frac{e^{-\langle u,\xi\rangle}-1+\langle\chi(\xi),u\rangle}{\|\xi\|^2\wedge1}\,\mu(d\xi).$$
--
--   The parameter set is **admissible** (Definition 2.3) if
--   1. $\alpha\in S_d^+$ (2.3) and $b\succeq(d-1)\alpha$ (2.4), with $b\in S_d$;
--   2. $c\ge0$ (2.5) and $\gamma\in S_d^+$ (2.6);
--   3. $\int(\|\xi\|\wedge1)\,m(d\xi)<\infty$ (2.7);
--   4. $\mu(E)\in S_d^+$ for every Borel $E$, and $\int\langle\chi(\xi),u\rangle\,M(x,d\xi)<\infty$ for all $x,u\in S_d^+$ with $\langle x,u\rangle=0$ (2.9);
--   5. $\beta^{ij}=\beta^{ji}\in S_d$, and $\langle B(x),u\rangle-\int\langle\chi(\xi),u\rangle\,M(x,d\xi)\ge0$ for all $x,u\in S_d^+$ with $\langle x,u\rangle=0$ (2.11).
--
--   The predicate `AdmissibleCore` collects every condition except the drift condition (2.4); `Admissible` adds (2.4). The file also defines `RiccatiIntegrable`: for every $u\in S_d^+$ the integrands of $F(u)$ and $R(u)$ are integrable.
--
--   These objects are the input of the existence theorem: every admissible parameter set is the characteristic of exactly one affine process.
--
--   **Formalization Note** The matrix measure $\mu$ is encoded as $\mu_{ij}(d\xi)=H_{ij}(\xi)\,\nu(d\xi)$ with a finite measure $\nu$, $\nu\{0\}=0$, and a measurable density $H$ with values in $S_d^+$ and integrable entries. This loses nothing: take $\nu=\sum_i\mu_{ii}$; then $|\mu_{ij}(E)|\le\tfrac12(\mu_{ii}(E)+\mu_{jj}(E))$ gives $\mu_{ij}\ll\nu$. The measures live on the cone and are required to give no mass to $\{0\}$. The norm is the trace norm, and $\chi$ is given on $M_d$ and maps $S_d$ to $S_d$. Integrals are Bochner integrals, so every theorem that concludes a formula involving them also concludes integrability of the integrands.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §2, Definition 2.3, (2.3)–(2.11), (2.13), (2.16)–(2.17), pp. 8–10

import Mathlib
import Definitions.Def_AffinePSD_Existence_Cone
import Definitions.Def_AffinePSD_Necessity_Params

open MeasureTheory
open scoped ENNReal

namespace AffinePSD.Existence

/-- The integrands of (2.16) and (2.17) are integrable at every `u ∈ S_d^+`: `ξ ↦ e^{−⟨u,ξ⟩} − 1`
against `m`, and every entry of `ξ ↦ (e^{−⟨u,ξ⟩} − 1 + ⟨χ(ξ),u⟩)/(‖ξ‖² ∧ 1) H(ξ)` against `ν`.
Formalization Note: concluded alongside every formula for `F` or `R`, so that the Bochner integrals
in `Fpar` and `Rpar` are the page's integrals and not Lean's junk value `0`. -/
def RiccatiIntegrable {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) : Prop :=
  ∀ u, PSD u →
    Integrable (fun ξ : Cone d => Real.exp (- tr u (ξ : Mat d)) - 1) P.m ∧
    ∀ i j, Integrable (fun ξ : Cone d =>
      (Real.exp (- tr u (ξ : Mat d)) - 1 + tr (χ.χ ξ) u) / min (fnorm (ξ : Mat d) ^ 2) 1 *
        P.H ξ i j) P.ν

end AffinePSD.Existence


