-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_copiesState
-- name    : OracleStateHSP_Supplement_copiesState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:11:57.111894+00:00
-- url     : https://prove2.me/theorems/d990a972-1f5c-42a7-841b-bed29a7ebb65
-- title:
--   Input of a $t$-sample algorithm: $|\varphi\rangle^{\otimes t} \otimes |0\rangle_W$ (Definition 5.2)
-- statement:
--   In the sample model a $t$-sample algorithm acts on the Hilbert space $\mathcal H = \mathcal H_S^{\otimes t} \otimes W$, where $\mathcal H_S$ is the space of the input state and the workspace $W$ is initialized to $|0\rangle$. Its input is the vector
--   $$
--   |\varphi\rangle^{\otimes t} \otimes |0\rangle_W ,
--   $$
--   whose amplitude at the basis vector $|z_1\rangle \cdots |z_t\rangle |w\rangle$ is $\varphi(z_1)\cdots\varphi(z_t)$ if $w = 0$ and $0$ otherwise.
--
--   **Formalization Note** The workspace has dimension $b + 1$ for an arbitrary $b \in \mathbb N$, with $|0\rangle$ the first basis vector; this covers every finite workspace, in particular $q$ qubits ($b + 1 = 2^q$).
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 5.2, p.41

import Mathlib

namespace OracleStateHSP

namespace Supplement

/-- The input of a `t`-sample algorithm (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 5.2, p.41): `t` copies of the state
vector `|φ⟩ ∈ H_S` together with a workspace `W` initialized to `|0⟩`, i.e. the vector
`|φ⟩^(⊗t) ⊗ |0⟩_W ∈ H_S^(⊗t) ⊗ W`.

**Formalization Note.** `H_S^(⊗t)` has the basis `Fin t → X` (the amplitude of `|φ⟩^(⊗t)` at `z` is
`∏_i φ(z_i)`), and `W` has the basis `Fin (b + 1)` with `|0⟩` the basis vector `0`, for an arbitrary
`b`; this covers every finite workspace, in particular `q` qubits (`b + 1 = 2^q`). -/
noncomputable def copiesState {X : Type*} (t b : ℕ) (φ : EuclideanSpace ℂ X) :
    EuclideanSpace ℂ ((Fin t → X) × Fin (b + 1)) :=
  WithLp.toLp 2 fun p => if p.2 = 0 then ∏ i, φ (p.1 i) else 0

end Supplement

end OracleStateHSP


