-- Prove2me | Definitions.Def_Chi2QEC_SatisfiesKL
-- name    : Chi2QEC_SatisfiesKL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:46.805908+00:00
-- url     : https://prove2.me/theorems/669cfa6c-04d4-448a-a18a-5dcadc84b50b
-- title:
--   Error-correction condition (23)
-- statement:
--   Let $C$ be a subspace of a finite-dimensional Hilbert space and $(E_h)_h$ a family of operators. The code $C$ satisfies the error-correction condition for this family when there are complex numbers $\alpha_{hj}$, independent of the code vectors, with
--   $$
--   \langle E_hu,E_jv\rangle=\alpha_{hj}\,\langle u,v\rangle\qquad\text{for all }h,j\text{ and all }u,v\in C.
--   $$
--   On an orthonormal logical basis $|\tilde a\rangle$ of $C$ this reads $\langle\tilde a|E_h^\dagger E_j|\tilde b\rangle=\alpha_{hj}\delta_{ab}$, which is the paper's (23), the Knill–Laflamme condition.
--
--   The condition includes the cross terms $h\ne j$, which is what makes it a condition on the family and not on each error separately.
--
--   **Formalization Note** The all-vectors form is equivalent to the form on logical basis states by sesquilinearity. The Lean inner product is conjugate-linear in its first argument, matching the bra.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, (23), p.7

import Mathlib

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, (23), p.7: the error-correction condition `⟨ã|Ê_h† Ê_j|b̃⟩ = α_{hj} δ_{ab}`
for all error indices `h, j` (cross terms included), with the `α_{hj}` independent of the logical
basis states `|ã⟩, |b̃⟩`.

**Formalization Note.** The code is a subspace `C` and (23) is stated for all `u, v ∈ C`, with
`⟨u, v⟩` in place of `δ_{ab}`. By sesquilinearity this is equivalent to (23) on an orthonormal
basis of `C`. `inner ℂ` is conjugate-linear in its first argument, matching the bra. -/
def SatisfiesKL {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (E : κ → Matrix ι ι ℂ) : Prop :=
  ∃ α : κ → κ → ℂ, ∀ h j, ∀ u ∈ C, ∀ v ∈ C,
    inner ℂ (Matrix.toEuclideanLin (E h) u) (Matrix.toEuclideanLin (E j) v) = α h j * inner ℂ u v

end Chi2QEC


