-- Prove2me | Definitions.Def_RandPurIso_Completion_purifiedOracleMat
-- name    : RandPurIso_Completion_purifiedOracleMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:24.876226+00:00
-- url     : https://prove2.me/theorems/d56b5ca2-f5c5-426a-bebf-8a3dcb696fdf
-- title:
--   Purified oracle $PO$ (Theorem 3.17)
-- statement:
--   For $A=\{a_1,\dots,a_\ell\}$ and $\mathsf{St}=\mathcal H(\mathbb Z_t)^{\otimes\ell}$,
--   $$PO|a_i\rangle|c_1,\dots,c_\ell\rangle=|a_i\rangle|c_1,\dots,c_{i-1},c_i+1,c_{i+1},\dots,c_\ell\rangle$$
--   (addition mod $t$), with initial state $|0,\dots,0\rangle$.
--
--   **Formalization Note** $A$ is a finite type, $\mathsf{St}$ has basis $A\to\mathbb Z_t$, and $t\ge1$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 3.17, pp. 24–25

import Mathlib
open Matrix

namespace RandPurIso.Completion

open Classical in
/-- **Purified oracle `PO`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorem 3.17, pp. 24–25): on `H(A) ⊗ St`, `St = H(Z_t)^{⊗ℓ}`,
`PO |a_i⟩|c₁,…,c_ℓ⟩ = |a_i⟩|c₁,…,c_i + 1,…,c_ℓ⟩` (addition modulo `t`).

**Formalization Note.** `A = {a₁, …, a_ℓ}` is a finite type, `St`'s basis is `A → Fin t` (`c_i` is the
value at `a_i`), and `Fin t` addition is modulo `t`; `t ≥ 1` (`NeZero t`) since `Z_0` is empty. -/
noncomputable def purifiedOracleMat (A : Type) [DecidableEq A] (t : ℕ) [NeZero t] :
    Matrix (A × (A → Fin t)) (A × (A → Fin t)) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = Function.update q.2 q.1 (q.2 q.1 + 1) then 1 else 0

open Classical in
/-- The default initial state `|{0, …, 0}⟩ ∈ St` of the purified oracle (Theorem 3.17). -/
noncomputable def purifiedInit (A : Type) (t : ℕ) [NeZero t] : (A → Fin t) → ℂ :=
  fun c => if c = 0 then 1 else 0

end RandPurIso.Completion


