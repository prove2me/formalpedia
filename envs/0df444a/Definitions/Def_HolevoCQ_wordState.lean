-- Prove2me | Definitions.Def_HolevoCQ_wordState
-- name    : HolevoCQ_wordState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:27.096974+00:00
-- url     : https://prove2.me/theorems/c97df4af-b65c-4e8d-a102-aac8d5f346e0
-- title:
--   Word state $S_u=S_{i_1}\otimes\cdots\otimes S_{i_n}$ (eq. 2)
-- statement:
--   Let $A$ be a finite input alphabet and $i\mapsto S_i$ a family of operators on $\mathcal H=\mathbb C^D$. For a word $u=(i_1,\dots,i_n)\in A^n$ the product channel emits the state
--
--   $$
--   S_u = S_{i_1}\otimes\cdots\otimes S_{i_n}
--   $$
--
--   on $\mathcal H^{\otimes n}$; its matrix entries are $\prod_{l} (S_{i_l})_{a_l b_l}$. This is the signal state of the $n$-fold memoryless use of the classical-quantum channel.
--
--   **Formalization Note** Words are `u : Fin n → A` and $\mathcal H^{\otimes n}$ is indexed by `Fin n → D`. The body coincides with the platform's `Dependency50.P07.wordState`, whose module is not available in this workspace.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (2), p.1

import Mathlib

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (2), p.1: for a word `u = (i₁, …, iₙ) ∈ Aⁿ` the density operator
`S_u = S_{i₁} ⊗ ⋯ ⊗ S_{iₙ}` on `H^{⊗n}`.

**Formalization Note.** Words are `u : Fin n → A`, `H^{⊗n}` is `ℂ^{Fin n → D}` and the matrix
entry is `∏_l (S_{u_l})_{a_l b_l}`. The body is the same as the platform's
`Dependency50.P07.wordState`, whose module is not available in this workspace. -/
def wordState {A D : Type} (S : A → Matrix D D ℂ) (n : ℕ) (u : Fin n → A) :
    Matrix (Fin n → D) (Fin n → D) ℂ :=
  Matrix.of fun a b => ∏ l, S (u l) (a l) (b l)

end HolevoCQ


