-- Prove2me | Definitions.Def_LeblSCV_Levi_leviPosIndex
-- name    : LeblSCV_Levi_leviPosIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:36:27.510071+00:00
-- url     : https://prove2.me/theorems/0a82b1a9-f7b5-458f-8d33-73e2ce8c160f
-- title:
--   Inertia of the Levi form: numbers of positive and negative eigenvalues
-- statement:
--   The Levi form of $r$ at $p$ is a Hermitian form on the finite-dimensional space $T^{(1,0)}_p \partial U$. Its **number of positive eigenvalues** is the largest dimension of a complex subspace $S \subset T^{(1,0)}_p\partial U$ on which $\mathcal{L}(X_p,X_p) > 0$ for every nonzero $X_p \in S$; the **number of negative eigenvalues** is defined with $< 0$. Together with the dimension of $T^{(1,0)}_p\partial U$ they determine the inertia (the numbers of positive, negative and zero eigenvalues).
--
--   **Formalization Note.** `leviPosIndex r p` and `leviNegIndex r p` are the supremum (in `ℕ`) of the set of such dimensions. The set always contains $0$ (take $S = 0$) and is bounded by $n$, so the supremum is attained. This is the variational (Sylvester) characterization of the number of positive/negative eigenvalues of a Hermitian form.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 67–68 (inertia of the Levi form)

import Mathlib
import Definitions.Def_LeblSCV_Levi_holTangent
import Definitions.Def_LeblSCV_Levi_leviForm

namespace LeblSCV.Levi

/-- Number of positive eigenvalues of the Levi form of `r` at `p` (Lebl, p. 67–68, inertia): the
largest dimension of a complex subspace of `T_p^{(1,0)} ∂U` on which the Levi form is positive
definite. The set is nonempty (`S = ⊥`) and bounded by `n`. -/
noncomputable def leviPosIndex {n : ℕ} (r : (Fin n → ℂ) → ℝ) (p : Fin n → ℂ) : ℕ :=
  sSup {d | ∃ S : Submodule ℂ (Fin n → ℂ), S ≤ holTangent r p ∧ Module.finrank ℂ S = d ∧
    ∀ a ∈ S, a ≠ 0 → 0 < (leviForm r p a).re}

/-- Number of negative eigenvalues of the Levi form of `r` at `p`: the largest dimension of a
complex subspace of `T_p^{(1,0)} ∂U` on which the Levi form is negative definite. -/
noncomputable def leviNegIndex {n : ℕ} (r : (Fin n → ℂ) → ℝ) (p : Fin n → ℂ) : ℕ :=
  sSup {d | ∃ S : Submodule ℂ (Fin n → ℂ), S ≤ holTangent r p ∧ Module.finrank ℂ S = d ∧
    ∀ a ∈ S, a ≠ 0 → (leviForm r p a).re < 0}

end LeblSCV.Levi


