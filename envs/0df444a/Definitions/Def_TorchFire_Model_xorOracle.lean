-- Prove2me | Definitions.Def_TorchFire_Model_xorOracle
-- name    : TorchFire_Model_xorOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:56.518214+00:00
-- url     : https://prove2.me/theorems/2cbcc653-87bd-4bc0-b366-4464684ff7c2
-- title:
--   The superposition oracle $O_f|x,z\rangle=|x,z\oplus f(x)\rangle$ and combined oracle collections
-- statement:
--   For a classical function $f:D\to\kappa$, the oracle queryable in superposition is the unitary
--   $$O_f|x,z\rangle = |x, z\oplus f(x)\rangle,\qquad x\in D,\ z\in\kappa,$$
--   acting as the identity on all other workspace (§3, p.17). Here $D$ is the query register and $\kappa$ the answer register, a finite group of exponent two built from bit strings.
--
--   An **oracle collection** is combined into a single oracle: a query names one component and its input, and the answer register has one slot per component, the answer of component $c$ written into slot $c$ (zero-padded). One query to the combined oracle is one query to one component. An indexed family of oracles of the same shape (the anchor sources $O_{A,\ell}$, $\ell\in\{0,1\}^\lambda$, or the $L$ one-bit components of a long-message scheme) is combined in the same way, the query naming the index.
--
--   **Formalization Note** The single combined oracle is the mission's pinned-down convention for "query access to the collection $O$" (paper.md decision 3); it changes no query count ("each oracle query counts as one gate", p.18).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §3 Classical Oracles Queried in Superposition p.17; p.18

import Mathlib
import Definitions.Def_TorchFire_Model_basisMat

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

namespace TorchFire.Model

/-- **The superposition oracle of a classical function** (Chatterjee–Mukherjee–Pathak–Podder,
*Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593, §3,
p.17):

  `O_f |x, z⟩ = |x, z ⊕ f(x)⟩`,  `x ∈ D`, `z ∈ κ`.

`D` is the query (input) register and `κ` the answer register; `⊕` is the group law of `κ` (bitwise
XOR on a product of bit strings). The remaining workspace is untouched (`liftOn`).

**Formalization Note** Answer types are finite additive groups of exponent two built from
`Bits` (products such as `ZMod 2 × Bits n` for the ⊥-flag encoding of paper.md decision 3). -/
def xorOracle {D κ : Type} [DecidableEq D] [DecidableEq κ] [Add κ] (f : D → κ) :
    Matrix (D × κ) (D × κ) ℂ :=
  basisMat fun p => (p.1, p.2 + f p.1)

/-- **Combining two oracles into one collection** (paper.md decision 3). A query is a query to one
component (`Sum.inl` or `Sum.inr`); the answer register holds one slot per component, and a query to
component `c` writes into slot `c` only (the other slot receives `0`, "zero-padded to the common
width"). One query to the combined oracle is one query to one component (p.18: "each oracle query
counts as one gate"). -/
def combine {D₁ D₂ κ₁ κ₂ : Type} [Zero κ₁] [Zero κ₂] (f₁ : D₁ → κ₁) (f₂ : D₂ → κ₂) :
    D₁ ⊕ D₂ → κ₁ × κ₂ :=
  Sum.elim (fun x => (f₁ x, 0)) (fun x => (0, f₂ x))

/-- A family of oracles with a common shape, indexed by `ι` (e.g. the anchor sources `O_{A,ℓ}`,
`ℓ ∈ {0,1}^λ`, of p.48, or the `L` one-bit components of Construction 4.13): the query names the
index. -/
def indexed {ι D κ : Type} (f : ι → D → κ) : ι × D → κ := fun p => f p.1 p.2

end TorchFire.Model


