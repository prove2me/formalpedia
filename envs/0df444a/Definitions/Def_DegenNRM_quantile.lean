-- Prove2me | Definitions.Def_DegenNRM_quantile
-- name    : DegenNRM_quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:35.159728+00:00
-- url     : https://prove2.me/theorems/6f73c37d-e1f1-45d5-aadb-d6d4137e3341
-- title:
--   The quantile function $F_j^{-1}$ and $G_j(q)=\int_{1-q}^1F_j^{-1}$
-- statement:
--   For a type $j$ and $q\in\mathbb R$,
--   $$F_j^{-1}(q)=\inf\{r\in[l_j,u_j]\;:\;F_j((-\infty,r])\ge q\},\qquad G_j(q)=\int_{1-q}^1F_j^{-1}(q')\,dq'.$$
--   $F_j^{-1}$ is the generalized inverse of the distribution function of $F_j$, and $G_j(q)$ is the expected reward collected from one type-$j$ query by accepting exactly the top $q$-fraction of its rewards. Both enter the quantile programs (12) and (13) and Algorithm 2.
--
--   **Formalization Note** The paper does not define $F_j^{-1}$; this is the standard left-continuous inverse. Under Assumption 1 the set is nonempty for $q\le1$ and $F_j^{-1}(q)\in[l_j,u_j]$.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, (12)–(13), p.14; Algorithm 2, p.15; proof of Lemma 4, p.41

import Mathlib
import Definitions.Def_DegenNRM_Instance

open MeasureTheory

namespace DegenNRM

/-- **The quantile function `F_j⁻¹`** (Jiang, Ma & Zhang, arXiv:2210.07996v5, (12), p.14, and
Algorithm 2, p.15).

`F_j⁻¹(q) = inf {r ∈ [l_j, u_j] : F_j((-∞, r]) ≥ q}`, the generalized inverse of the
distribution function of `F_j` restricted to the reward interval.

**Formalization Note.** The paper uses `F_j⁻¹` without defining it; this is the standard
left-continuous generalized inverse. Under Assumption 1 the set is nonempty for `q ≤ 1` (it
contains `u_j`) and `F_j⁻¹(q) ∈ [l_j, u_j]`; for `q ≤ 0` it is `l_j`. -/
noncomputable def quantile {m n : ℕ} (inst : Instance m n) (j : Fin n) (q : ℝ) : ℝ :=
  sInf {r | r ∈ Set.Icc (inst.l j) (inst.u j) ∧ q ≤ (inst.F j).real (Set.Iic r)}

/-- **The function `G_j(q) = ∫_{1-q}^1 F_j⁻¹(q′) dq′`** (arXiv:2210.07996v5, proof of Lemma 4,
p.41; the integrand of (12) and (13), p.14).

`G_j(q)` is the expected reward collected from a type-`j` query by accepting exactly its top
`q`-fraction of rewards. -/
noncomputable def Gfun {m n : ℕ} (inst : Instance m n) (j : Fin n) (q : ℝ) : ℝ :=
  ∫ x in (1 - q)..1, quantile inst j x

end DegenNRM


