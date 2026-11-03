-- Prove2me | Definitions.Def_EnvelopeMSLP_IsSmoothCell
-- name    : EnvelopeMSLP_IsSmoothCell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:49.97936+00:00
-- url     : https://prove2.me/theorems/b4fb89bd-4112-4aca-8fb6-ca83b84a5adf
-- title:
--   Smooth cell: a smooth embedded image of an open cube
-- statement:
--   A set $S\subseteq\mathbb R^N$ is a smooth cell when there are $d\le N$ and a diffeomorphism $h:(0,1)^d\to S$, in this sense: $h$ is $C^\infty$ on the open cube, injective, has an injective derivative at every point, and has an inverse continuous on $S$. The paper's proof gives its manifolds in exactly this form.
--
--   **Formalization Note** For $d=0$ the cube is one point.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9

import Mathlib

namespace EnvelopeMSLP

/-- **Smooth cell.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9: "`S_i` are smooth manifolds in `ℝ^N` and there
exist diffeomorphisms `h_i : (0, 1)^{n_i} → S_i`, where `0 ≤ n_i ≤ N`".

**Formalization Note.** `S` is the image of the open cube of some dimension `d ≤ N` under a `C^∞`
map `h` that is injective, has injective derivative at every point of the cube, and has an inverse
that is continuous on `S`. So `h` is a smooth embedding, and `S` an embedded smooth submanifold
diffeomorphic to the cube. For `d = 0` the cube is one point. -/
def IsSmoothCell {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) : Prop :=
  ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ h : (Fin d → ℝ) → (ι → ℝ),
    let cube : Set (Fin d → ℝ) := Set.pi Set.univ fun _ => Set.Ioo 0 1
    S = h '' cube ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h cube ∧ Set.InjOn h cube ∧
      (∀ x ∈ cube, Function.Injective (fderiv ℝ h x)) ∧
      ∃ g : (ι → ℝ) → (Fin d → ℝ), ContinuousOn g S ∧ ∀ x ∈ cube, g (h x) = x

end EnvelopeMSLP


