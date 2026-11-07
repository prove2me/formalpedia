-- Prove2me | Definitions.Def_ZKSheafPCP_RSIndex
-- name    : ZKSheafPCP_RSIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:14:51.574903+00:00
-- url     : https://prove2.me/theorems/d6a5b1e8-1e26-46de-a4ac-d92688fcafb9
-- title:
--   The family $\mathrm{RS}^+$ as a pair language
-- statement:
--   An index of $\mathrm{RS}^+$ is a tuple $(\mathbb F,L,d)$ with $\mathbb F$ an extension field of $\mathbb F_2$, $L$ an $\mathbb F_2$-linear subspace and $d\le|L|/8$. The $n$-th code is the Reed–Solomon code $\mathrm{RS}[\mathbb F,L,d]$ of evaluations on $L$ of polynomials of degree at most $d$.
--
--   Here the field is given as $\mathbb F_2[X]/(f)$ by an irreducible polynomial, $L$ by a basis, and $d$ in binary. The string encoding has length polynomial in $k=\dim L$ and $\log|\mathbb F|$, not in $|L|$, which is the setting for a verifier with polylogarithmic running time.
--
--   **Formalization Note** A position $p<2^k$ denotes the sum of the basis elements selected by the bits of $p$. A symbol $a<2^{\deg f}$ denotes the field element with coordinates the bits of $a$. The field of Definition 8.14 is finite, since §8 opens with $\mathbb F=\mathbb F_{2^l}$.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definition 8.14, p.40; Definition 3.21, p.13

import Mathlib
import Definitions.Def_ZKSheafPCP_PCPPFamily

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP

open Classical

/-- A binary field given explicitly, `𝔽₂[X]/(f)` for an irreducible `f`. Every finite extension of `𝔽₂` has this form. -/
structure BinField where
  /-- the irreducible polynomial -/
  poly : Polynomial (ZMod 2)
  /-- it is irreducible -/
  irred : Irreducible poly

instance (B : BinField) : Fact (Irreducible B.poly) := ⟨B.irred⟩

namespace BinField

variable (B : BinField)

/-- The field. -/
abbrev F : Type := AdjoinRoot B.poly

/-- `log₂ |𝔽|`. -/
noncomputable def deg : ℕ := B.poly.natDegree

/-- The field element with symbol `a`: the bits of `a` are its coordinates in the basis `1, X, X², …`. -/
noncomputable def sym (a : ℕ) : B.F :=
  ∑ j ∈ Finset.range B.deg, if a.testBit j then (AdjoinRoot.root B.poly) ^ j else 0

/-- The number whose bits are the coefficients of the polynomial. -/
noncomputable def polyCode : ℕ :=
  ∑ j ∈ Finset.range (B.deg + 1), if B.poly.coeff j = 1 then 2 ^ j else 0

end BinField

/-- An index `(𝔽, L, d)` of the family `RS+` (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission, manuscript sha256
ac5e528f…, Definition 8.14, p.40): `𝔽` a binary field, `L` an `𝔽₂`-linear subspace with a basis, `d ≤ |L|/8`.

**Formalization Note** `L` is given by a basis, so a word on `L` is indexed by the `2^k` bit vectors, and the explicit input has
length polynomial in `k` and `log |𝔽|`. Every subspace has a basis, and every basis is allowed. The field of Definition
8.14 is finite: §8 opens with `𝔽 = 𝔽_{2^l}`, p.36. -/
structure RSIndex where
  /-- the field -/
  B : BinField
  /-- the dimension of `L` -/
  k : ℕ
  /-- the basis of `L`, as symbols -/
  basis : Fin k → ℕ
  /-- the basis elements are symbols -/
  basis_lt : ∀ j, basis j < 2 ^ B.deg
  /-- the basis is `𝔽₂`-linearly independent: distinct subsets have distinct sums -/
  indep : Function.Injective fun T : Finset (Fin k) => ∑ j ∈ T, B.sym (basis j)
  /-- the degree bound -/
  d : ℕ
  /-- `d ≤ |L|/8` -/
  hd : 8 * d ≤ 2 ^ k

namespace RSIndex

variable (i : RSIndex)

/-- The point of `L` at position `p`: the sum of the basis elements selected by the bits of `p`. -/
noncomputable def pt (p : ℕ) : i.B.F :=
  ∑ j : Fin i.k, if p.testBit j.val then i.B.sym (i.basis j) else 0

/-- `|L|`, the parameter `n` of Theorem 8.18. -/
def n : ℕ := 2 ^ i.k

end RSIndex

/-- The pair language `RS+`: the explicit input is `(𝔽, L, d)` and `L[x] = RS[𝔽, L, d]` (Definitions 3.21 and 8.14, pp.13 and
40). A word is over the symbols `Fin (2 ^ deg)`, in which `BinField.sym` reads field elements. -/
noncomputable def rsPlus : PCPPFamily where
  Inst := RSIndex
  enc i := tup [binN i.B.polyCode, tup ((List.finRange i.k).map fun j => binN (i.basis j)), binN i.d]
  N i := i.n
  a i := 2 ^ i.B.deg
  Lang i := {y | ∃ p ∈ Polynomial.degreeLE i.B.F (i.d : ℕ),
    ∀ pos, i.B.sym (y pos).val = p.eval (i.pt pos.val)}

end ZKSheafPCP


