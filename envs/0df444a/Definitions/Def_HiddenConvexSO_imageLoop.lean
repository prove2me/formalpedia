-- Prove2me | Definitions.Def_HiddenConvexSO_imageLoop
-- name    : HiddenConvexSO_imageLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:31.38619+00:00
-- url     : https://prove2.me/theorems/dfa380fa-1935-4638-8d53-30d98c30fdb4
-- title:
--   Image loop $f_*(\gamma)$ viewed in the punctured plane
-- statement:
--   Let $X$ be a topological space, $f:X\to\mathbb R^2$ continuous, and $\gamma:[0,1]\to X$ a loop based at $x$. If $(0,0)\notin f(\gamma([0,1]))$, then
--
--   $$
--   f_*(\gamma)(t)=f(\gamma(t)),\qquad t\in[0,1],
--   $$
--
--   is a loop in the punctured plane $\mathbb R^2\setminus(0,0)$ based at $f(x)$. This is how Lemma 3 views $f_*(\gamma)$ as an element of $\pi_1(\mathbb R^2\setminus(0,0))$.
--
--   **Formalization Note** The loop is the composite $f\circ\gamma$ with codomain restricted to `{p : ℝ × ℝ // p ≠ 0}`; it takes the continuity of $f$ and the non-vanishing hypothesis as arguments. Nothing else is added.
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, Lemma 3, p.13 ("In this case, we may view f∗(γ) as a loop in R2 \ (0, 0)")

import Mathlib

namespace HiddenConvexSO

/-- **The image loop `f∗(γ)` viewed in the punctured plane.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, Lemma 3, p.13 (PDF p.13): for a continuous
`f : SO(n) → ℝ²` and a loop `γ` such that "(0, 0) is not in the image (f∗(γ))([0, 1]). In this case,
we may view f∗(γ) as a loop in R2 \ (0, 0)."

Given a continuous `f : X → ℝ × ℝ`, a loop `γ` at `x` in `X`, and the hypothesis that `f (γ t) ≠ 0`
for every `t ∈ [0, 1]`, `imageLoop f hf γ hγ` is the loop `t ↦ f (γ t)` in the punctured plane
`{p : ℝ × ℝ // p ≠ 0}`, based at `f x`.

**Formalization Note.** The base point `⟨f x, _⟩` is built from `hγ 0` and `γ 0 = x`. The
construction is the composite `f ∘ γ` with its codomain restricted; nothing else is added. -/
noncomputable def imageLoop {X : Type*} [TopologicalSpace X] {x : X} (f : X → ℝ × ℝ)
    (hf : Continuous f) (γ : Path x x) (hγ : ∀ t, f (γ t) ≠ 0) :
    Path (⟨f x, by simpa using hγ 0⟩ : {p : ℝ × ℝ // p ≠ 0}) ⟨f x, by simpa using hγ 0⟩ where
  toFun t := ⟨f (γ t), hγ t⟩
  continuous_toFun := (hf.comp γ.continuous).subtype_mk _
  source' := by simp
  target' := by simp

end HiddenConvexSO


