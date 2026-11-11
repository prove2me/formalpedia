-- Prove2me | Definitions.Def_QuadExt_Main_Pure
-- name    : QuadExt_Main_Pure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:02:56.230195+00:00
-- url     : https://prove2.me/theorems/69d90ba4-036a-4b4a-9d2b-da36fe2e710f
-- title:
--   $q$-pure quadratic sources (Definition 3.8)
-- statement:
--   A quadratic source $X = f(U_s)$ is **$q$-pure** if there is no affine subspace $V \subseteq \mathbb F_2^s$ such that $f|_V$ is affine and
--   $$\dim f(V) \ge q.$$
--   Purity depends on the generating map $f$, not only on the distribution of $X$: it says that $f$ has no large affine piece.
--
--   **Formalization Note.** $q$ is a real number. "$f|_V$ is affine" means that $f$ agrees on $V$ with some affine map $x \mapsto \ell(x) + b$ of $\mathbb F_2^s$. $\dim f(V)$ is the dimension of the affine span of $f(V)$, which is $f(V)$ itself when $f|_V$ is affine. A single point is an affine subspace of dimension $0$, so no source is $q$-pure for $q \le 0$, as in the paper.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 8 (PDF 9), Definition 3.8

import Mathlib

namespace QuadExt.Main

/-!
# q-pure quadratic sources

Chandrasekaran, Goodman, Zuckerman, *Quadratic Extractors*, STOC 2027 submission (manuscript
sha256 ddc80a9a…), p. 8 (PDF 9), Definition 3.8: "A quadratic source `X = f(U_s)` is `q`-pure if
there exists no affine subspace `V ⊆ 𝔽₂^s` such that `f|_V` is affine and `dim(f(V)) ≥ q`."
Purity is a property of the generating map `f`, not only of the distribution.
-/

/-- `f` is **`q`-pure**: there is no affine subspace `V` of the generating bits on which `f`
agrees with an affine map and whose image `f(V)` has (affine) dimension at least `q`. `dim(f(V))`
is the dimension of the affine span of `f(V)`, which equals `f(V)` when `f|_V` is affine. -/
def IsPure {σ : Type} {n : ℕ} (q : ℝ) (f : (σ → ZMod 2) → (Fin n → ZMod 2)) : Prop :=
  ¬ ∃ V : AffineSubspace (ZMod 2) (σ → ZMod 2),
      (∃ (ℓ : (σ → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : Fin n → ZMod 2),
          ∀ x ∈ V, f x = ℓ x + b) ∧
      q ≤ (Module.finrank (ZMod 2) (affineSpan (ZMod 2) (f '' (V : Set (σ → ZMod 2)))).direction : ℝ)

end QuadExt.Main


