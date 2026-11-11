-- Prove2me | Definitions.Def_ChowFormsCH_expList
-- name    : ChowFormsCH_expList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:56:32.007918+00:00
-- url     : https://prove2.me/theorems/b1d979e2-4801-441f-ac99-836dfaa4957e
-- title:
--   Dense representation: integer bit encoding and monomial enumerations
-- statement:
--   Integers are written in binary with a sign bit: the encoding of $z$ with $w$ magnitude bits is the sign bit followed by the $w$ least significant binary digits of $|z|$, least significant first; it is faithful when $|z|<2^w$. An integer of **height at most $h$** satisfies $|z|\le 2^h$ and is written with $h+1$ magnitude bits.
--
--   A polynomial of degree at most $D$ in $N$ variables is given in the **dense representation** by its $\binom{D+N}{N}$ coefficients, listed along a fixed enumeration of the exponent vectors $\alpha\in\mathbb N^N$ with $|\alpha|\le D$; a form of degree $d$ by the coefficients of the monomials of degree exactly $d$.
--
--   These fix the input and output layouts of the circuits of Lemmas 2.13, 2.18 and Theorem 4.9.
--
--   **Formalization Note** The enumeration `expList` lets the first exponent run over $0,\dots,D$ and recurses on the remaining variables. The paper counts $h+1$ bits including the sign, which misses $|z|=2^h$; one more magnitude bit is used.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §2.1, p.9 (height); §2.4, p.13; Theorem 2.12, items 9–11, p.14; Lemma 2.13, p.15

import Mathlib

set_option autoImplicit false

namespace ChowFormsCH

/-- The bits of an integer `z` in sign-magnitude binary with `w` magnitude bits: a sign bit
(`true` for negative), then the `w` least significant binary digits of `|z|`, least significant
first (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow
forms*, arXiv:2611.05289, held version, sha256 75e796c6…, §2.4, p.13: "integers will be represented
in base two with a sign bit"). It represents `z` faithfully when `|z| < 2^w`.

**Formalization Note** An integer of height at most `h` satisfies `|z| ≤ 2^h`, so the inputs of
the theorems use `w = h + 1` magnitude bits (one more than the paper's count, which misses
`|z| = 2^h`). -/
def intBits (w : ℕ) (z : ℤ) : List Bool :=
  decide (z < 0) :: List.ofFn (fun i : Fin w => z.natAbs.testBit i)

/-- The integer read from the bits `y off, y (off+1), …, y (off+w)` in the format of `intBits`:
sign bit first, then `w` magnitude bits, least significant first. -/
def decodeInt (w : ℕ) (y : ℕ → Bool) (off : ℕ) : ℤ :=
  (if y off then -1 else 1) * ((∑ i : Fin w, if y (off + 1 + i) then 2 ^ (i : ℕ) else 0 : ℕ) : ℤ)

/-- A fixed enumeration of all exponent vectors `α ∈ ℕ^N` with `α₀ + ⋯ + α_{N−1} ≤ D`, i.e. of the
monomials of degree at most `D` in `N` variables; it has `C(D+N, N)` entries (§2.4, Theorem 2.12
items 9–11 and Lemma 2.13, p.15: "C(d+m, d) integers representing the coefficients" of a
polynomial of degree at most `d` in `m` variables). The first exponent runs over `0, …, D`. -/
def expList : (N : ℕ) → ℕ → List (Fin N → ℕ)
  | 0, _ => [fun _ => 0]
  | N + 1, D => (List.range (D + 1)).flatMap
      (fun e => (expList N (D - e)).map (fun α => Fin.cons (α := fun _ => ℕ) e α))

/-- The exponent vectors of degree exactly `d` in `N` variables, in the order of `expList`: the
monomials of a form of degree `d` in the dense representation (Theorem 4.9, p.34). -/
def homExps (N d : ℕ) : List (Fin N → ℕ) :=
  (expList N d).filter (fun α => decide ((∑ i, α i) = d))

/-- An exponent vector as a finitely supported function, i.e. as a monomial. -/
noncomputable def expToFinsupp {σ : Type*} [Finite σ] (α : σ → ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm α

/-- The polynomial in `N` variables with coefficient list `c` in the dense representation of
`expList N D` (the `j`-th coefficient multiplies the `j`-th monomial). -/
noncomputable def densePoly {R : Type*} [CommSemiring R] (N D : ℕ)
    (c : Fin (expList N D).length → R) : MvPolynomial (Fin N) R :=
  ∑ j : Fin (expList N D).length, MvPolynomial.monomial (expToFinsupp ((expList N D).get j)) (c j)

end ChowFormsCH


