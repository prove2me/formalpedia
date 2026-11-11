-- Prove2me | Definitions.Def_ChowFormsCH_chowOutputPoly
-- name    : ChowFormsCH_chowOutputPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:22.280192+00:00
-- url     : https://prove2.me/theorems/1041d81d-fbaa-414d-bedd-ea18a14a6032
-- title:
--   Input and output layout of the Chow-form circuits $C^{\mathrm{CHOW}}_{n,m,d_1,\dots,d_m,h}$
-- statement:
--   The circuit $C^{\mathrm{CHOW}}_{n,m,d_1,\dots,d_m,h}$ is indexed by the list $(n,m,d_1,\dots,d_m,h)$ and takes $r=5\cdot m\cdot(n+1)^3$ random integers. Its **input** lists, for each form $F_i$ in turn and each monomial of degree $d_i$ in $x_0,\dots,x_n$, the numerator $p$ and then the denominator $q$ of the rational coefficient $p/q$, and then the integers $a_1,\dots,a_r$; every integer uses a sign bit and $h+1$ magnitude bits. Its **output** consists of $n+1$ polynomials: for $k=0,\dots,n$, the coefficients of all monomials of degree at most $N$ in the $(k+1)(n+1)$ variables $u_{i,j}$ ($0\le i\le k$, $0\le j\le n$), each an integer with a sign bit and $w$ magnitude bits.
--
--   **Formalization Note** The degree bound $N$ and the width $w$ are chosen by the circuit family and must be computable from the index in polylogarithmic time (Definition 2.9, item 2); the decoder is otherwise fixed, so it cannot do any of the work. The variables $u_{i,j}$ are enumerated $u_{0,0},\dots,u_{0,n},u_{1,0},\dots$.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 4.9, p.34; §2.4, p.13

import Mathlib
import Definitions.Def_ChowFormsCH_expList

set_option autoImplicit false

namespace ChowFormsCH

/-- The index `(n, m, d₁, …, d_m, h)` of the circuit `C^CHOW_{n,m,d₁,…,d_m,h}` as a list
(Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow forms*,
arXiv:2611.05289, held version, sha256 75e796c6…, Theorem 4.9, p.34; Remark 2.10, p.12: the number
of indices is a function of the first ones). Degrees are 0-based: `ds i` is `d_{i+1}`. -/
def chowIndex (n m : ℕ) (ds : Fin m → ℕ) (h : ℕ) : List ℕ :=
  n :: m :: (List.ofFn ds ++ [h])

/-- The number `r = 5 · m · (n + 1)³` of random integer inputs `a₁, …, a_r` of Theorem 4.9
(p.34). -/
def numRandom (n m : ℕ) : ℕ := 5 * m * (n + 1) ^ 3

/-- The form `F ∈ ℚ[x₀, …, xₙ]` of degree `d` in the dense representation with coefficient data
`coef`: the `j`-th monomial of degree `d` (in the order of `homExps (n+1) d`) has the rational
coefficient `p / q`, `(p, q) = coef j` (Theorem 4.9, p.34; §2.4, p.13: "We represent rational
numbers as pairs of integers (p, q) with q ≠ 0"). -/
noncomputable def formOfData (n d : ℕ) (coef : Fin (homExps (n + 1) d).length → ℤ × ℤ) :
    MvPolynomial (Fin (n + 1)) ℚ :=
  ∑ j : Fin (homExps (n + 1) d).length,
    MvPolynomial.monomial (expToFinsupp ((homExps (n + 1) d).get j))
      (((coef j).1 : ℚ) / ((coef j).2 : ℚ))

/-- The input bits of `C^CHOW_{n,m,d₁,…,d_m,h}` (Theorem 4.9, p.34): for each form `F_i` in turn,
for each monomial of degree `d_i` (order of `homExps`), the numerator and then the denominator of
its coefficient; then the random integers `a₁, …, a_r`. Every integer is written by `intBits` with
`h + 1` magnitude bits. -/
def chowInput (n m : ℕ) (ds : Fin m → ℕ) (h : ℕ)
    (coef : (i : Fin m) → Fin (homExps (n + 1) (ds i)).length → ℤ × ℤ)
    (a : Fin (numRandom n m) → ℤ) : List Bool :=
  (List.ofFn fun i : Fin m =>
      (List.ofFn fun j : Fin (homExps (n + 1) (ds i)).length =>
        intBits (h + 1) (coef i j).1 ++ intBits (h + 1) (coef i j).2).flatten).flatten
    ++ (List.ofFn fun e : Fin (numRandom n m) => intBits (h + 1) (a e)).flatten

/-- The number of input bits of `C^CHOW_{n,m,d₁,…,d_m,h}`, the length of `chowInput`. -/
def chowInputLength (n m : ℕ) (ds : Fin m → ℕ) (h : ℕ) : ℕ :=
  (∑ i : Fin m, (homExps (n + 1) (ds i)).length) * (2 * (h + 2)) + numRandom n m * (h + 2)

/-- The offset of the `k`-th output polynomial (`0 ≤ k ≤ n`): the `k`-th polynomial lists the
coefficients of all monomials of degree at most `N` in the `(k+1)(n+1)` variables `u_{i,j}`, each
coefficient an integer with `w` magnitude bits. -/
def chowBlockOffset (n N w k : ℕ) : ℕ :=
  ∑ k' ∈ Finset.range k, (expList ((k' + 1) * (n + 1)) N).length * (w + 1)

/-- The number of output bits of `C^CHOW` for degree bound `N` and width `w`: `n + 1` polynomials
in the layout of `chowBlockOffset`. -/
def chowOutputLength (n N w : ℕ) : ℕ := chowBlockOffset n N w (n + 1)

/-- The `k`-th output polynomial of `C^CHOW` in the dense representation (Theorem 4.9, p.34: "The
output … is a set of n + 1 polynomials in the dense representation"), read from the output bits
`y`: a polynomial in the variables `u_{i,j}`, `0 ≤ i ≤ k`, `0 ≤ j ≤ n`, with integer coefficients.

**Formalization Note** The variables `u_{i,j}` are enumerated as `Fin ((k+1)(n+1))` through
`finProdFinEquiv`, i.e. `u_{0,0}, …, u_{0,n}, u_{1,0}, …`; monomials of total degree at most `N` in
the order of `expList`; coefficient `j` occupies bits `off + j(w+1), …, off + j(w+1) + w`
(`intBits` format). The degree bound `N` and width `w` are chosen by the circuit family and
computable from the index. -/
noncomputable def chowOutputPoly (n N w : ℕ) (y : ℕ → Bool) (k : ℕ) :
    MvPolynomial (Fin (k + 1) × Fin (n + 1)) ℤ :=
  ∑ j : Fin (expList ((k + 1) * (n + 1)) N).length,
    MvPolynomial.monomial
      (expToFinsupp fun p : Fin (k + 1) × Fin (n + 1) =>
        ((expList ((k + 1) * (n + 1)) N).get j) (finProdFinEquiv p))
      (decodeInt w y (chowBlockOffset n N w k + (j : ℕ) * (w + 1)))

end ChowFormsCH


