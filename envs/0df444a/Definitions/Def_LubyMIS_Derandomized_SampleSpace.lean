-- Prove2me | Definitions.Def_LubyMIS_Derandomized_SampleSpace
-- name    : LubyMIS_Derandomized_SampleSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:54:02.665989+00:00
-- url     : https://prove2.me/theorems/ed2a92b7-c01a-4928-9e38-84bbad2947ae
-- title:
--   The q²-point pairwise independent sample space of §4.2
-- statement:
--   Let $q$ be a prime with $q \ge n$, and let $A$ be an $n \times q$ matrix whose row $i$ lists the possible values of the random variable $X_i$ ($0 \le i \le n-1$), row $i$ containing exactly $n_{ij}$ entries equal to the value $R_j$. The sample space consists of the $q^2$ points
--   $$b^{x,y} = (b_0, \dots, b_{n-1}), \qquad b_i = A_{i,\,(x + y\cdot i) \bmod q}, \qquad 0 \le x, y \le q-1,$$
--   each with probability $1/q^2$. At the sample point $b^{x,y}$ the random variable $X_i$ takes the value $b_i$.
--
--   This definition provides $X_i$ as a function of the sample point $(x,y)$, and the count $n_{ij}$ of entries of row $i$ equal to a given value. Lemmas 1 and 2 compute the one- and two-dimensional marginals of these variables under the uniform law on the $q^2$ points.
--
--   **Formalization Note** Column indices and sample coordinates live in $\mathbb{Z}/q\mathbb{Z}$ (`ZMod q`), so $(x + y\cdot i) \bmod q$ is the ring expression $x + y\,i$ in `ZMod q`. The vertex index $i$ is the label $0, \dots, n-1$ of an element of `Fin n`, cast into `ZMod q`. Row $i$ is a function $\mathbb{Z}/q\mathbb{Z} \to R$ for an arbitrary value type $R$ with decidable equality.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1044, §4.2 (matrix A, sample points b^{x,y}); §4.1 criterion 1 (n_ij)

import Mathlib

namespace LubyMIS.Derandomized

/-- The random variable `X_i` on the `q²`-point sample space of §4.2 (Luby 1986, p. 1044): at the
sample point `b^{x,y}`, `X_i` takes the value `b_i = A_{i,(x + y·i) mod q}`. Row `i` of the `n × q`
matrix `A` is `A i : ZMod q → R`, and the vertex label is `(i : ℕ) ∈ {0, …, n − 1}`. -/
def Xrv {n q : ℕ} {R : Type*} (A : Fin n → ZMod q → R) (i : Fin n) (p : ZMod q × ZMod q) : R :=
  A i (p.1 + p.2 * ((i : ℕ) : ZMod q))

/-- `n_{ij}`: the number of entries of row `i` of `A` equal to the value `r` (§4.2, p. 1044). -/
def nCount {n q : ℕ} [NeZero q] {R : Type*} [DecidableEq R] (A : Fin n → ZMod q → R) (i : Fin n)
    (r : R) : ℕ :=
  (Finset.univ.filter (fun l => A i l = r)).card

end LubyMIS.Derandomized


