-- Prove2me | Definitions.Def_WildeQIT_AFW_recoverBC
-- name    : WildeQIT_AFW_recoverBC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:58.238522+00:00
-- url     : https://prove2.me/theorems/98b72eba-d2b1-4b4b-9c15-55a94cfbc6c8
-- title:
--   Recovered state $\mathcal R_{C\to AC}(\rho_{BC})$
-- statement:
--   Let $\mathcal R: \mathcal L(\mathcal H_C) \to \mathcal L(\mathcal H_A\otimes\mathcal H_C)$ be a quantum channel and $\omega_{BC}$ an operator on $\mathcal H_B\otimes\mathcal H_C$. The **recovered operator** $\mathcal R_{C\to AC}(\omega_{BC})$ is the result of applying $\mathrm{id}_B\otimes\mathcal R$ to $\omega_{BC}$, an operator on $\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_C$. If $\mathcal R(X) = \sum_i K_i X K_i^\dagger$ is a Kraus decomposition, then
--
--   $$
--   \mathcal R_{C\to AC}(\omega_{BC}) = \sum_i (I_B\otimes K_i)\,\omega_{BC}\,(I_B\otimes K_i)^\dagger ,
--   $$
--
--   with the systems then ordered as $A, B, C$.
--
--   Theorem 11.10.5 compares $\rho_{ABC}$ with $\mathcal R_{C\to AC}(\rho_{BC})$: if some channel on $C$ alone nearly rebuilds $\rho_{ABC}$ from its marginal, the conditional mutual information is small.
--
--   **Formalization Note** $\mathcal R$ is a published `WildeQIT.QChannel C (A × C)` (Choi–Kraus form; by Theorem 4.4.1 every channel has one). The operator $\sum_i (I_B\otimes K_i)\omega(I_B\otimes K_i)^\dagger$ lives on `B × (A × C)`; rows and columns are reindexed to the mission's tripartite convention `A × (B × C)`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.5, (11.283), p. 362; Choi–Kraus form, Theorem 4.4.1, p. 151

import Mathlib
import Definitions.Def_WildeQIT_QChannel

open scoped Kronecker Matrix

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.5,
(11.283), p. 362: the state `R_{C→AC}(ρ_BC)` on `A ⊗ B ⊗ C` obtained by applying a channel
`R : L(H_C) → L(H_A ⊗ H_C)` to the `C` system of an operator on `H_B ⊗ H_C` (the identity acts on
`B`).

**Formalization Note.** `R` is a published `WildeQIT.QChannel C (A × C)` (Choi–Kraus form with
Kraus operators `K_i : Matrix (A × C) C ℂ`; by Theorem 4.4.1 every channel has this form). The
channel `id_B ⊗ R` has Kraus operators `I_B ⊗ K_i`, so
`(id_B ⊗ R)(ω) = Σ_i (I_B ⊗ K_i) ω (I_B ⊗ K_i)†`, an operator on `B × (A × C)`; its rows and
columns are then reordered to the mission's tripartite convention `A × (B × C)` by
`(a, (b, c)) ↦ (b, (a, c))`. -/
noncomputable def recoverBC {A B C : Type} [Fintype A] [Fintype B] [DecidableEq B] [Fintype C]
    [DecidableEq C] (R : WildeQIT.QChannel C (A × C)) (ω : Matrix (B × C) (B × C) ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  let M : Matrix (B × (A × C)) (B × (A × C)) ℂ :=
    ∑ i, ((1 : Matrix B B ℂ) ⊗ₖ R.K i) * ω * ((1 : Matrix B B ℂ) ⊗ₖ R.K i)ᴴ
  M.submatrix (fun abc => (abc.2.1, (abc.1, abc.2.2))) (fun abc => (abc.2.1, (abc.1, abc.2.2)))

end WildeQIT.AFW


