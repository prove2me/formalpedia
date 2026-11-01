-- Prove2me | Definitions.Def_BaconThesis_Universality_SUOn
-- name    : BaconThesis_Universality_SUOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:07.264386+00:00
-- url     : https://prove2.me/theorems/596e27dd-682e-454b-9030-70fefdd2b5b3
-- title:
--   $\mathrm{SU}(W)\oplus I$, the special unitary group of a subspace extended by the identity
-- statement:
--   Let $\mathcal H=\mathbb C^{\iota}$ carry its standard inner product and let $W\subseteq\mathcal H$ be a subspace with orthogonal complement $W^\perp$. Define
--   $$
--   \mathrm{SU}(W)\oplus I_{W^\perp}=\{\,U\in\mathrm{SU}(\mathcal H)\;:\; Uv=v\ \text{for every } v\in W^\perp\,\}.
--   $$
--   A unitary that fixes $W^\perp$ pointwise maps $W$ onto itself, and its restriction to $W$ is a unitary of determinant $1$; conversely every $V\in\mathrm{SU}(W)$, extended by the identity on $W^\perp$, belongs to this set. So it is exactly "$\mathrm{SU}(d)$ acting on the subspace $W$" ($d=\dim W$) as an operator on the whole space. For $W=\mathcal H$ it is $\mathrm{SU}(\mathcal H)$; for $W=\{0\}$ it is $\{I\}$.
--
--   This is the object of Lemma 4.3.1: sets of operators which "densely act as $\mathrm{SU}(d_A)$ on a subspace $\mathcal H_A$".
--
--   **Formalization Note** The subspace lives in `EuclideanSpace ℂ ι`, so that $W^\perp$ is the orthogonal complement for the standard inner product; matrices act on it through `Matrix.toEuclideanLin`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Lemma 4.3.1, p.52 (PDF p.69)

import Mathlib

namespace BaconThesis.Universality

/-- **`SU(d)` acting on a subspace, extended by the identity.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§4.3.1, Lemma 4.3.1, p.52 (PDF p.69): "SU(d_A) … on [a] subspace H_A (dimension d_A) of a larger
Hilbert space H".

For a subspace `W` of `ℂ^ι` (with its standard inner product), `SUOn W` is the set of operators
`V ⊕ I_{W^⊥}` with `V ∈ SU(W)`: the special unitary matrices on `ℂ^ι` that fix every vector of the
orthogonal complement `W^⊥`. Such a matrix maps `W` onto itself, its restriction to `W` is unitary
of determinant `1`, and conversely every `V ∈ SU(W)` extended by the identity on `W^⊥` lies in
`SUOn W`. In particular `SUOn ⊤` is `SU(ℂ^ι)` and `SUOn ⊥ = {I}`.

**Formalization Note.** The subspace lives in `EuclideanSpace ℂ ι` so that its orthogonal
complement is the one of the standard inner product; matrices act on it by
`Matrix.toEuclideanLin`. -/
def SUOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) : Set (Matrix ι ι ℂ) :=
  {U | U ∈ Matrix.specialUnitaryGroup ι ℂ ∧ ∀ v ∈ Wᗮ, Matrix.toEuclideanLin U v = v}

end BaconThesis.Universality


