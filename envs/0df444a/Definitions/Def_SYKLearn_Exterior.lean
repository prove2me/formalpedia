-- Prove2me | Definitions.Def_SYKLearn_Exterior
-- name    : SYKLearn_Exterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:11.540369+00:00
-- url     : https://prove2.me/theorems/a07bc185-b3a5-4fc4-8c48-ad9b68d51181
-- title:
--   Wedge product, annihilation operators $a_i$, $a_I$ and the contraction operator $\mathsf O_r(u)=\sum_{|I|=r}a_Iu\wedge a_I$
-- statement:
--   On the exterior algebra $\bigoplus_k\Lambda^k\mathbb R^n$ with basis $e_S$:
--
--   1. The **wedge product** is bilinear with $e_S\wedge e_T=0$ when $S\cap T\neq\emptyset$ and $e_S\wedge e_T=\varepsilon(S,T)\,e_{S\cup T}$ otherwise, where $\varepsilon(S,T)=(-1)^{\#\{(s,t)\in S\times T:\ t<s\}}$ is the sign that sorts the concatenation of $S$ and $T$. In particular $e_i\wedge e_j=\mathbb 1_{i\neq j}(-1)^{[i>j]}e_{\{i,j\}}$.
--   2. The **annihilation operator** $a_i:\mathbb M_k\to\mathbb M_{k-1}$ acts by
--   $$a_ie_I=\begin{cases}\varepsilon_{I,i}\,e_{I\setminus i}&i\in I,\\0&i\notin I,\end{cases}\qquad \varepsilon_{I,i}=(-1)^{|\{j<i:\ j\in I\}|},$$
--   the adjoint of the creation operator $c_i=e_i\wedge\cdot$. For $I=\{I_1<\dots<I_k\}$, $a_I=a_{I_k}\cdots a_{I_1}$.
--   3. The **contraction operator** (Definition 3) is, for $u\in\mathbb M_d$ and $r\le d$,
--   $$\mathsf O_r(u)\,h=\sum_{|I|=r}(a_Iu)\wedge(a_Ih),$$
--   and $\mathsf O_{r,k}(u)$ is its restriction to inputs $h\in\mathbb M_k$.
--
--   The operator $\mathsf O_r$ is how the paper writes the degree-six part of a commutator of two Majorana Hamiltonians as a linear map of the coupling vector (Lemma A.4).
--
--   **Formalization Note** A vector is its coefficient function on finsets of `Fin n`. The wedge product is the published `PathCount2k.wedge` over $\mathbb R$, whose sign $(-1)^{\mathrm{inv}(S,T)}$, $\mathrm{inv}(S,T)=\#\{(s,t)\in S\times T:s>t\}$, is the sign $\varepsilon(S,T)$ above. $a_I$ applies $a_{I_1}$ first. The page's sign convention for $e_i\wedge e_j$ is checked in the sanity file.
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), §2.1, (13), pp.11–12; Definition 3, p.13

import Mathlib
import Definitions.Def_SYKLearn_Basic
import Definitions.Def_PathCount2k_Exterior

noncomputable section

namespace SYKLearn

/-!
# Wedge product, annihilation operators and the contraction operator `O_r`

A. Anshu, S. Arunachalam, S. Chen, Y. Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission (held file sha256 5d7d199a…), §2.1, (13), pp.11–12; Definition 3, p.13.

**Formalization Note.**
* A vector of `Ext N` is its coefficient function on the basis `e_S`, `S ⊆ Fin N`.
* The wedge product is the published `PathCount2k.wedge` (over `ℝ`): bilinear with
  `e_S ∧ e_T = 0` if `S ∩ T ≠ ∅` and `e_S ∧ e_T = (−1)^{inv(S,T)} e_{S∪T}` otherwise,
  `inv(S,T) = #{(s,t) ∈ S × T : s > t}`. On singletons this is the page's
  `e_i ∧ e_j = 1_{i≠j}·(−1)^{[i>j]}·e_{\{i,j\}}` (p.11); `Ext N` is `PathCount2k.Ext ℝ N`.
* `ann i` is the annihilation operator `a_i` of (13): `a_i e_I = ε_{I,i} e_{I∖i}` for `i ∈ I` and
  `0` otherwise, with `ε_{I,i} = (−1)^{#{j ∈ I : j < i}}`; it is the adjoint of `c_i = e_i ∧ ·`.
* `annSet I = a_I = a_{I_k} ⋯ a_{I_1}` for `I = {I_1 < ⋯ < I_k}` (p.12): `a_{I_1}` acts first.
* `contr r u h = O_r(u) h = Σ_{|I|=r} (a_I u) ∧ (a_I h)` (Definition 3, p.13); for `h ∈ M_k` this
  is the paper's `O_{r,k}(u) h`.
-/

/-- The wedge product on `Ext N` (§2.1, p.11): the published `PathCount2k.wedge` over `ℝ`. -/
abbrev wedge {N : ℕ} (u v : Ext N) : Ext N := PathCount2k.wedge u v

/-- The annihilation operator `a_i` of (13), p.12. -/
def ann {N : ℕ} (i : Fin N) (u : Ext N) : Ext N :=
  fun R => if i ∈ R then 0 else
    (-1) ^ (R.filter (fun j => j < i)).card * u (insert i R)

/-- `a_I = a_{I_k} ⋯ a_{I_1}` for `I = {I_1 < ⋯ < I_k}` (p.12). -/
def annSet {N : ℕ} (I : Finset (Fin N)) (u : Ext N) : Ext N :=
  (I.sort (· ≤ ·)).foldl (fun acc i => ann i acc) u

/-- The contraction operator `O_r(u) h = Σ_{|I|=r} (a_I u) ∧ (a_I h)` (Definition 3, p.13). -/
def contr {N : ℕ} (r : ℕ) (u h : Ext N) : Ext N :=
  ∑ I ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun I => I.card = r),
    wedge (annSet I u) (annSet I h)

end SYKLearn


