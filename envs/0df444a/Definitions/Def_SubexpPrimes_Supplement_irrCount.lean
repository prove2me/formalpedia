-- Prove2me | Definitions.Def_SubexpPrimes_Supplement_irrCount
-- name    : SubexpPrimes_Supplement_irrCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:45:26.423945+00:00
-- url     : https://prove2.me/theorems/0cd87097-e6a7-4c4c-8913-63451e74ae31
-- title:
--   Count $I_n(C)$ and rank of constrained irreducibles over $\mathbb F_2$
-- statement:
--   A monic polynomial of degree $n$ over $\mathbb F_2$,
--
--   $$
--   F=X^n+f_{n-1}X^{n-1}+\cdots+f_1X+f_0,
--   $$
--
--   is identified with the $n$-bit string $f_{n-1}\cdots f_0$ of its **free coefficients**, most significant first. For a constraint $C$ on $n$-bit strings, $F$ is an **accepted irreducible** if its free-coefficient string satisfies $C$ and $F$ is irreducible in $\mathbb F_2[X]$. The count $I_n(C)$ is the number of accepted irreducibles of degree $n$. **Coefficient order** orders the polynomials by their free-coefficient strings read as $n$-bit integers, and the **rank** of a string $x$ is the number of accepted irreducibles strictly below $x$ in that order (so ranks start at $0$).
--
--   These are the quantities computed in Theorem 7.2 and in the irreducibles item of Theorem 3.
--
--   **Formalization Note** Strings are lists of booleans; the polynomial of $x$ is `polyOf (true :: x)` from the published `bitsToNat` module, and order is the order of `bitsToNat`.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 7.2, p.31 (PDF p.33); rank, p.33 (PDF p.35); notation, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_SubexpPrimes_bitsToNat

set_option autoImplicit false

namespace SubexpPrimes.Supplement

/-- An `n`-bit string `x = f_{n-1} … f_0` of free coefficients is an **accepted irreducible** for the
constraint `C` if `C x` holds and the monic polynomial `Xⁿ + f_{n-1}X^{n-1} + ⋯ + f_0 = polyOf (true :: x)`
is irreducible in `F₂[X]`. -/
def IrrAccepted (C : List Bool → Prop) (x : List Bool) : Prop :=
  C x ∧ Irreducible (polyOf (true :: x))

open scoped Classical in
/-- **The count `Iₙ(C)` of accepted irreducibles** — Gajulapalli, *Deterministic Construction of
Primes in Subexponential Time* (manuscript, sha256 6ad4d3de…), Theorem 7.2, p.31: the number of
irreducible monic polynomials of degree `n` over `F₂` whose `n` free coefficients satisfy `C`.

**Formalization Note.** The `n` free coefficients `f_{n-1}, …, f_0` of `F = Xⁿ + ∑_{i<n} f_i X^i` form
the `n`-bit string `f_{n-1} … f_0`, most significant first (the convention of p.13 for words as
polynomials), so `F = polyOf (true :: x)`. -/
noncomputable def irrCount (n : ℕ) (C : List Bool → Prop) : ℕ :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => IrrAccepted C (List.ofFn x))).card

open scoped Classical in
/-- **The rank of a string among the accepted irreducibles** — Theorem 7.2, p.33: "the rank of an
accepted irreducible F is the number of accepted irreducibles below it", in coefficient order, i.e.
the order of the free-coefficient strings as `n`-bit integers (`bitsToNat`). Ranks start at `0`. -/
noncomputable def irrRank (n : ℕ) (C : List Bool → Prop) (x : List Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n → Bool)).filter
    (fun y => IrrAccepted C (List.ofFn y) ∧ bitsToNat (List.ofFn y) < bitsToNat x)).card

end SubexpPrimes.Supplement


