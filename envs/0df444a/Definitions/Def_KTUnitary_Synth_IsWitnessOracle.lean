-- Prove2me | Definitions.Def_KTUnitary_Synth_IsWitnessOracle
-- name    : KTUnitary_Synth_IsWitnessOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:45.888971+00:00
-- url     : https://prove2.me/theorems/45e1e281-e3cc-46e8-9a7a-3f2d5d6b0b11
-- title:
--   Witness oracle for a relation
-- statement:
--   A language $W$ is a **witness oracle** for a relation $R$ if, for every $x$ that has some $y$ with $(x,y)\in R$, the bits $W(x,0),W(x,1),\dots$ spell a witness: for some length $\ell$,
--   $$\big(x,\ W(x,0)\,W(x,1)\cdots W(x,\ell-1)\big)\in R.$$
--   On inputs $x$ without a witness, $W(x,\cdot)$ is unconstrained.
--
--   **Formalization Note** The paper writes "the string $y$ defined by $y_i:=W(x,i)$" and leaves the length of $y$ implicit; the reading here is that some prefix is a witness. The query $(x,i)$ is the string `tup [x, bin i]` with `bin i` the binary code of $i$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.3, p. 34

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Witness oracle** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.3, p. 34): "A language `W` is a witness oracle for a
relation `R` if, for every `x` for which `{(x, ·) ∈ R} ≠ ∅`, the string `y` defined by
`y_i := W(x, i)` satisfies `(x, y) ∈ R`. On inputs `x` for which no valid `y` exists, `W(x, i)` is
unconstrained."

Here: for every `x` that has some `y` with `(x, y) ∈ R`, there is a length `ℓ` such that the string
`W(x, 0) W(x, 1) ⋯ W(x, ℓ − 1)` is a witness for `x`.

**Formalization Note** The paper leaves the length of `y` implicit; the reading here is that some
prefix of the bit sequence `i ↦ W(x, i)` is a witness. The query `(x, i)` is `tup [x, bin(i)]`, with
`bin(i) = Nat.bits i` the little-endian binary code of `i`. -/
def IsWitnessOracle (W : Oracle) (R : Set (Str × Str)) : Prop :=
  ∀ x : Str, (∃ y, (x, y) ∈ R) →
    ∃ ℓ : ℕ, (x, (List.range ℓ).map fun i => W (tup [x, Nat.bits i])) ∈ R

end KTUnitary.Synth


