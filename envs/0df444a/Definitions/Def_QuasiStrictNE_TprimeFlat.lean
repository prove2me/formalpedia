-- Prove2me | Definitions.Def_QuasiStrictNE_TprimeFlat
-- name    : QuasiStrictNE_TprimeFlat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:12:18.305853+00:00
-- url     : https://prove2.me/theorems/1dc17cfb-7911-475f-8e4c-8797a48104f9
-- title:
--   $T'$ as a map of $\mathbb R^{m+n}$
-- statement:
--   $T'$ written on $\mathbb R^{m+n}$: split $z$ into $x$ (first $m$ coordinates) and $y$ (last $n$), apply $T'$, and concatenate the two parts of the result.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 5, p.16; (9), p.13

import Mathlib
import Definitions.Def_QuasiStrictNE_Tprime

namespace QuasiStrictNE

/-- **`T′` as a map of `ℝ^{m+n}`** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 5, p.16: "a linear-comparison oracle for
z ∈ R^{m+n} … returns the local formula T′(z)"; (9), p.13).

`TprimeFlat A B p q z` splits `z ∈ ℝ^{m+n}` into `x` (first `m` coordinates) and `y` (last `n`),
applies `Tprime A B p q` to `(x, y)` and concatenates the two parts of the result.

**Formalization Note** The concatenation is `Fin.append`, the splitting its inverse
(`Fin.castAdd n`, `Fin.natAdd m`). -/
noncomputable def TprimeFlat {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (p : Set (Fin m → ℝ) → (Fin m → ℝ)) (q : Set (Fin n → ℝ) → (Fin n → ℝ))
    (z : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  Fin.append (Tprime A B p q (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))).1
    (Tprime A B p q (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))).2

end QuasiStrictNE


