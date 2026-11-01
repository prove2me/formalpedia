-- Prove2me | Definitions.Def_WildeQIT_QMemory_idTensorChannel
-- name    : WildeQIT_QMemory_idTensorChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:31.934979+00:00
-- url     : https://prove2.me/theorems/aeef1fae-5fe0-4336-a9a0-fdcfacc6ba0e
-- title:
--   Channel on the second system: $(\mathrm{id}_A\otimes\mathcal N)(\rho_{AB})$
-- statement:
--   Let $\mathcal N:\mathcal L(\mathcal H_B)\to\mathcal L(\mathcal H_{B'})$ be a quantum channel with Kraus operators $\{V_l\}$, $\sum_l V_l^\dagger V_l=I_B$. Applied to the $B$ share of a bipartite operator $\rho_{AB}$ it gives
--
--   $$
--   \sigma_{AB'}\equiv\mathcal N_{B\to B'}(\rho_{AB})=\sum_l(I_A\otimes V_l)\,\rho_{AB}\,(I_A\otimes V_l)^\dagger .
--   $$
--
--   **Formalization Note** The channel is the published `WildeQIT.QChannel` (Choi–Kraus form, which by Theorem 4.4.1 represents every quantum channel); $\mathcal H_A\otimes\mathcal H_B$ is indexed by `a × b`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.9.3, p. 351 (with Theorem 4.4.1)

import Mathlib
import Definitions.Def_WildeQIT_QChannel

open scoped Matrix

namespace WildeQIT.QMemory

/-- **A channel acting on the second system** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, Theorem 11.9.3, p. 351): for a quantum channel
`N : L(H_B) → L(H_B′)` with Kraus operators `{V_l}`, `σ_AB′ ≡ N_{B→B′}(ρ_AB) = (id_A ⊗ N)(ρ_AB)
= ∑_l (I_A ⊗ V_l) ρ_AB (I_A ⊗ V_l)†`.

**Formalization Note** The channel is the published `WildeQIT.QChannel` (Choi–Kraus form, which
by Theorem 4.4.1 represents every quantum channel); `H_A ⊗ H_B` is indexed by `a × b`. -/
noncomputable def idTensorChannel {a b b' : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [Fintype b'] (N : WildeQIT.QChannel b b')
    (ρ : Matrix (a × b) (a × b) ℂ) : Matrix (a × b') (a × b') ℂ :=
  ∑ l, Matrix.kronecker (1 : Matrix a a ℂ) (N.K l) * ρ *
    (Matrix.kronecker (1 : Matrix a a ℂ) (N.K l))ᴴ

end WildeQIT.QMemory


