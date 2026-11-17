-- Prove2me | Definitions.Def_SpencerEight_Supplement_Dmat
-- name    : SpencerEight_Supplement_Dmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:48:44.025421+00:00
-- url     : https://prove2.me/theorems/8de54613-5311-4223-a98c-6f76d6bf2953
-- title:
--   The constant $D^{\mathrm{mat}}_n$
-- statement:
--   For $n\ge1$, $D^{\mathrm{mat}}_n$ is the worst case of the matrix signing discrepancy over admissible families:
--   $$
--   D^{\mathrm{mat}}_n:=\sup\Bigl\{\mathrm{disc}_{\mathrm{mat}}(A_1,\dots,A_n)\;:\;1\le d\le n,\ A_i\in\mathbb R^{d\times d}\text{ symmetric},\ \|A_i\|\le1\ (i\in[n])\Bigr\}.
--   $$
--   The constant of interest is $D^{\mathrm{mat}}_n/\sqrt n$; Matrix Spencer bounds it above, and the families of Section 15 bound it below.
--
--   **Formalization Note** A real supremum. For $n\ge1$ the set is nonempty (all $A_i=0$) and bounded above by $n$, so the supremum is genuine; both facts are proved in the mission's sanity file. The admissible matrices are the base mission's symmetric contractions.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 15.1, pp.288-289 (PDF pp.288-289)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_Supplement_discmat

namespace SpencerEight.Supplement

/-- The constant `D^mat_n` (Definition 15.1, Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), pp.288-289 (PDF pp.288-289)): the
supremum of `discmat(A₁, …, A_n)` over all dimensions `1 ≤ d ≤ n` and all families of real symmetric
`d × d` matrices with `‖Aᵢ‖ ≤ 1` for every `i ∈ [n]`.

**Formalization Note** A real `sSup`. For `n ≥ 1` the set is nonempty (`d = 1`, all `Aᵢ = 0`) and bounded
above by `n` (triangle inequality), so the supremum is the true one; both facts are proved in
`Solutions/verification/SpencerEight_Supplement_sanity.lean`. The source defines `D^mat_n` only for
`n ≥ 1`; at `n = 0` the set is empty and the value is `0`, a case no statement uses. The admissible
matrices are the base mission's `IsSymmContraction` (symmetric, operator norm at most one). -/
noncomputable def Dmat (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ d : ℕ, 1 ≤ d ∧ d ≤ n ∧ ∃ A : Fin n → Matrix (Fin d) (Fin d) ℝ,
    (∀ i, IsSymmContraction (A i)) ∧ r = discmat A}

end SpencerEight.Supplement


