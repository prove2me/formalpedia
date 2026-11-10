-- Prove2me | Definitions.Def_QThermalClassical_IsPauliProd
-- name    : QThermalClassical_IsPauliProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:32.476847+00:00
-- url     : https://prove2.me/theorems/e1d2e610-254e-4f67-b15a-bbad2a956638
-- title:
--   Pauli product up to a phase with term list $C(E)$
-- statement:
--   An operator $E$ is a **Pauli product up to a phase** with term list $C(E)=(c_1,\dots,c_t)$ if
--   $$
--   E=\omega\,P_{c_{\pi(1)}}P_{c_{\pi(2)}}\cdots P_{c_{\pi(t)}},\qquad \omega\in\{1,-1,i,-i\},
--   $$
--   for some reordering $\pi$ of the list. The **order** of $E$ is $t=|C(E)|$; with $t=0$, $E$ is the identity up to a phase. These are the operators returned by the sampling primitive of Lemma 9 and multiplied together in Definition 3.1.
--
--   **Formalization Note** The reordering makes the adjoint $E^\dagger=\bar\omega P_{c_{\pi(t)}}\cdots P_{c_{\pi(1)}}$ again a Pauli product with the same term list, as Algorithm 1 uses it; every statement uses only the length and the set of words of $C(E)$.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 9, p.24; Definition 3.1 and Lemma 10, p.25

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The ordered product `P_{L_1} P_{L_2} ⋯ P_{L_t}` of the Pauli strings of a list of words
(the empty product is `I`). -/
def listProd (L : List (PauliWord Q)) : Op Q :=
  (L.map pauliOp).prod

/-- A phase in `{1, −1, i, −i}` (the phases of products of Pauli matrices, proof of Lemma 10,
p.25). -/
def IsPhase (ω : ℂ) : Prop :=
  ω = 1 ∨ ω = -1 ∨ ω = Complex.I ∨ ω = -Complex.I

/-- `E` is a Pauli product up to a phase with term list `C = C(E)` (Lemma 9, p.24; Definition
3.1, p.25): `E = ω · P_{L_1} ⋯ P_{L_t}` with `ω ∈ {±1, ±i}` and `L` a reordering of `C`.
The order of `E` is the length of `C`. With `C = []`, `E` is the identity up to a phase.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 9, p.24; Definition 3.1 and
Lemma 10, p.25.

**Formalization Note.** The reordering lets the adjoint `E^† = ω̄ · P_{L_t} ⋯ P_{L_1}` of a
Pauli product with term list `C` again be a Pauli product with term list `C`, as Algorithm 1
uses it; every statement that uses `C` uses only its length and its set of words. -/
def IsPauliProd (C : List (PauliWord Q)) (E : Op Q) : Prop :=
  ∃ (ω : ℂ) (L : List (PauliWord Q)), IsPhase ω ∧ L.Perm C ∧ E = ω • listProd L

end QThermalClassical


