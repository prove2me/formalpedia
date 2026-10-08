-- Prove2me | Definitions.Def_AronszajnRK_Inclusion_IsClosedTransformation
-- name    : AronszajnRK_Inclusion_IsClosedTransformation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:49.267303+00:00
-- url     : https://prove2.me/theorems/0f6964f3-990c-4e37-95e0-ef7fd3024ad7
-- title:
--   Closed linear transformation of a (not necessarily closed) subspace
-- statement:
--   Let $F$ and $F_1$ be normed complex vector spaces, $F'$ a linear subspace of $F$ (not necessarily closed) and $T : F'\to F_1$ a linear transformation with image $F_1'$. The transformation $T$ is **closed** if, whenever $\{f_n\}\subset F'$,
--
--   $$f_n\to f\in F \quad\text{and}\quad Tf_n\to f_1\in F_1,$$
--
--   it follows that $f\in F'$, $f_1\in F_1'$ and $Tf = f_1$.
--
--   Closedness is the hypothesis of Banach's closed graph theorem, which the paper applies to the identity correspondence between two reproducing kernel classes.
--
--   **Formalization Note** The subspace $F'$ is a `Submodule`, $T$ a linear map on it; since $F_1'$ is the image of $T$, the condition $f_1\in F_1'$ follows from $Tf=f_1$ and is not written separately.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 382, §13 (C), definition of a closed transformation

import Mathlib

open Filter Topology

namespace AronszajnRK.Inclusion

/-- A linear transformation `T` of a linear subspace `F′` of `F` into `F₁` is **closed**
(Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C), p. 382,
PDF p. 46) if from `{fₙ} ⊂ F′`, `fₙ → f ∈ F` and `T fₙ → f₁ ∈ F₁` it follows that `f ∈ F′`,
`f₁ ∈ F₁′` and `T f = f₁`. Here `F₁′` is the image of `T`, so `f₁ ∈ F₁′` follows from `T f = f₁`.
The subspace `F′` need not be closed. -/
def IsClosedTransformation {F F₁ : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] {F' : Submodule ℂ F} (T : F' →ₗ[ℂ] F₁) : Prop :=
  ∀ (u : ℕ → F') (f : F) (f₁ : F₁),
    Tendsto (fun n => (u n : F)) atTop (𝓝 f) → Tendsto (fun n => T (u n)) atTop (𝓝 f₁) →
      ∃ hf : f ∈ F', T ⟨f, hf⟩ = f₁

end AronszajnRK.Inclusion


