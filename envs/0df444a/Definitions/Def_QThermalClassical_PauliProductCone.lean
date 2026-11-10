-- Prove2me | Definitions.Def_QThermalClassical_PauliProductCone
-- name    : QThermalClassical_PauliProductCone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:30.929633+00:00
-- url     : https://prove2.me/theorems/ab1cbba5-67bf-49fc-8c2f-795c7e16cbd2
-- title:
--   Nonnegative combinations of products of single-qubit stabilizer states
-- statement:
--   The six single-qubit stabilizer states are $\tfrac12(I\pm X)$, $\tfrac12(I\pm Y)$, $\tfrac12(I\pm Z)$. An operator $\rho$ on $n$ qubits lies in the **stabilizer-product cone** if
--   $$
--   \rho=\sum_{i=1}^Nw_i\bigotimes_{q}\tfrac12\left(I+s_{i,q}\,\sigma_{i,q}\right),\qquad w_i\ge0,\ \sigma_{i,q}\in\{X,Y,Z\},\ s_{i,q}=\pm1 .
--   $$
--   This is the conclusion "separable into a mixture of stabilizer states" of Lemma 7, in the form of the proof's decomposition (52).
--
--   **Formalization Note** The weights are only nonnegative (not normalized), because Lemma 7 concerns a positive operator.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 7, p.19; eq. (52), p.20

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

/-- The six single-qubit stabilizer states `½(I ± X)`, `½(I ± Y)`, `½(I ± Z)`: axis
`0, 1, 2 ↦ X, Y, Z`, sign `false ↦ +`, `true ↦ −`. -/
noncomputable def stabProj (axis : Fin 3) (neg : Bool) : Matrix Bool Bool ℂ :=
  (1 / 2 : ℂ) • (1 + (if neg then (-1 : ℂ) else 1) • pauli1 ⟨axis.val + 1, by omega⟩)

/-- `ρ` is a nonnegative combination of products of single-qubit stabilizer states: the
conclusion "separable into a mixture of stabilizer states" of Lemma 7, as the proof's
decomposition (52) exhibits it ("every state appearing in the decomposition is a product of
stabilizer states as ½(I ± {X, Y, Z}) is a stabilizer state").

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 7, p.19, and eq. (52), p.20.

**Formalization Note.** The combination is unnormalized (the weights are only nonnegative),
because Lemma 7 is about a positive operator, not a normalized state. -/
def PauliProductCone {Q : Type} [Fintype Q] (ρ : Op Q) : Prop :=
  ∃ (N : ℕ) (w : Fin N → ℝ) (ax : Fin N → Q → Fin 3) (sg : Fin N → Q → Bool),
    (∀ i, 0 ≤ w i) ∧ ρ = ∑ i, ((w i : ℝ) : ℂ) • tensorOp (fun q => stabProj (ax i q) (sg i q))

end QThermalClassical


