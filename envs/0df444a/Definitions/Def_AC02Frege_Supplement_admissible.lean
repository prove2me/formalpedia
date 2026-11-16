-- Prove2me | Definitions.Def_AC02Frege_Supplement_admissible
-- name    : AC02Frege_Supplement_admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:57:25.636504+00:00
-- url     : https://prove2.me/theorems/41705957-347e-4895-b428-e730e66c3f6b
-- title:
--   $D$-admissible target spaces, approximators, $Z_P(j)$ and $c_P(j)$
-- statement:
--   Let $V_n$ be the space of multilinear polynomials over $\mathbb F_2$ in $y_1,\dots,y_n$ and $D\in\mathbb N\cup\{\infty\}$. An $\mathbb F_2$-subspace $C\subseteq V_n$ is **$D$-admissible** if
--   $$
--   u\in C,\quad v\in V_n,\quad \deg u+\deg v\le D\ \Longrightarrow\ uv\in C,
--   $$
--   with products multilinearized.
--
--   Fix a line $L=\bigvee_{i=1}^s(u_i=1)$ with $u_i\in V_n$, and an **approximator** $P=\prod_\nu q_\nu$ (multilinearized), each factor an affine combination $q_\nu=1+\sum_i a_{\nu i}u_i$ with $a_\nu\in\mathbb F_2^s$ (with no factors, $P=1$). For $j\ge0$ put
--   $$
--   Z_P(j)=\{f\in V_j:\ fPu_i\in C\ \text{for every } i\},\qquad c_P(j)=\dim V_j-\dim Z_P(j),
--   $$
--   where $V_j$ is the space of multilinear polynomials of degree at most $j$, of dimension $M_n(j)=\sum_{i\le j}\binom ni$.
--
--   $Z_P(j)$ is the space of multipliers that are good for $P$ up to degree $j$, and $c_P(j)$ the number of independent error conditions. These are the objects of Theorem A.2, the general form of Pang's one-factor gain.
--
--   **Formalization Note** $C$ is a `Submodule` of `MvPolynomial (Fin n) (ZMod 2)` all of whose elements are multilinear; $D$ is in `ℕ∞`; degrees of multilinear polynomials are total degrees. $\dim Z_P(j)$ is the `finrank` of its span (it is a subspace), via the base `dimSpan`, and $\dim V_j$ is the base `monoCount n j`.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition A.1, p.35; Appendix A, p.36; Definition 2.8, p.11

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_rankCounts

namespace AC02Frege.Supplement

open MvPolynomial

/-- A **`D`-admissible target space** (Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret,
*Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Definition A.1, p.35): an
`𝔽₂`-subspace `C` of the space `V_n` of multilinear polynomials in `y_1, …, y_n`, with
`D ∈ ℕ ∪ {∞}`, such that `u ∈ C`, `v ∈ V_n`, `deg u + deg v ≤ D` imply `ML(uv) ∈ C` ((45),
products multilinearized).

**Formalization Note** `C` is a `Submodule` of `MvPolynomial (Fin n) (ZMod 2)` all of whose elements
are multilinear; `D : ℕ∞` (`⊤` is `∞`). Degrees of multilinear polynomials are their total
degrees. -/
def IsAdmissible {n : ℕ} (D : ℕ∞) (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) :
    Prop :=
  (∀ p ∈ C, IsMultilinear p) ∧
  ∀ u ∈ C, ∀ v : MvPolynomial (Fin n) (ZMod 2), IsMultilinear v →
    ((u.totalDegree + v.totalDegree : ℕ) : ℕ∞) ≤ D → ML (u * v) ∈ C

/-- The **approximator** `P = ∏_ν q_ν` of a line with polynomials `u_1, …, u_s`
(Appendix A, p.36; (3), p.11): each factor is an affine combination
`q_ν = 1 + Σ_i a_{ν,i} u_i`, `a_ν ∈ 𝔽₂^s`, and the product is multilinearized. With `t = 0`
factors, `P = 1`. -/
noncomputable def approxProd {n s t : ℕ} (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (a : Fin t → Fin s → ZMod 2) : MvPolynomial (Fin n) (ZMod 2) :=
  ML (∏ ν : Fin t, (1 + ∑ i : Fin s, a ν i • u i))

/-- `Z_P(j) = {f ∈ V_j : f P u_i ∈ C for every i}` (Appendix A, p.36): the multipliers of degree at
most `j` that are good for `P`, products multilinearized. -/
def ZsolC {n s : ℕ} (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) (P : MvPolynomial (Fin n) (ZMod 2)) (j : ℕ) :
    Set (MvPolynomial (Fin n) (ZMod 2)) :=
  {f | f ∈ AC02Frege.Vdeg (Fin n) j ∧ ∀ i, ML (f * P * u i) ∈ C}

/-- `c_P(j) = dim V_j − dim Z_P(j)` (Appendix A, p.36), with `dim V_j = M_n(j)`
(Definition 2.8, p.11). -/
noncomputable def cErrC {n s : ℕ} (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) (P : MvPolynomial (Fin n) (ZMod 2)) (j : ℕ) : ℕ :=
  AC02Frege.monoCount n j - AC02Frege.dimSpan (ZsolC C u P j)

end AC02Frege.Supplement


