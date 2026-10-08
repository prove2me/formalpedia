-- Prove2me | Definitions.Def_ConvexOptAlg_SVRG_Defs
-- name    : ConvexOptAlg_SVRG_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:22:22.082258+00:00
-- url     : https://prove2.me/theorems/714048d9-db8f-4f27-ac2b-7b19999da1a5
-- title:
--   §6.3, pp. 334–336 — finite-sum objective and SVRG epochs
-- statement:
--   Let $m\ge1$ and let $f_1,\ldots,f_m:\mathbb R^n\to\mathbb R$ be differentiable convex functions with declared gradients $g_i=\nabla f_i$. Their finite-sum objective and full gradient are
--
--   $$f(x)=\frac1m\sum_{i=1}^m f_i(x),\qquad G(x)=\frac1m\sum_{i=1}^m g_i(x).$$
--
--   The component family is **$\beta$-smooth** when $\|g_i(x)-g_i(z)\|_2\le\beta\|x-z\|_2$ for every $i,x,z$. For anchor $y$ and sampled component $i$, the SVRG direction is $v_i(x,y)=g_i(x)-g_i(y)+G(y)$. Starting with $x_1=y$, an epoch makes $k$ updates $x_{t+1}=x_t-\eta v_{i_t}(x_t,y)$ and returns $k^{-1}\sum_{t=1}^k x_t$. Repeating this rule defines $y^{(s+1)}$ from $y^{(s)}$.
--
--   Uniform expectation is the arithmetic mean over all index arrays. The arrays contain one independently and uniformly chosen component index per update, so averaging over $s$ epochs means averaging over the $m^{sk}$ possible arrays. These definitions provide the exact algorithm and sample law used by Theorem 6.5.
--
--   **Formalization Note** The inner implementation has zero-based positions internally: position zero is the book's $x_1$. The output averages positions zero through $k-1$, corresponding exactly to $x_1,\ldots,x_k$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.3, pp. 334–336, PDF pp. 107–109; SVRG recursion p. 336

import Mathlib

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- The component assumptions of §6.3: each `fᵢ` is differentiable and convex
on all of `ℝⁿ`, and its declared gradient is `β`-Lipschitz. -/
def SmoothConvexFamily {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) : Prop :=
  (∀ i x, HasGradientAt (fs i) (gs i x) x) ∧
  (∀ i, ConvexOn ℝ Set.univ (fs i)) ∧
  (∀ i x y, ‖gs i x - gs i y‖ ≤ β * ‖x - y‖)

/-- The uniform average over a finite sample space. In this mission all sample spaces
are nonempty: `Fin m` has `m ≥ 1`, and the spaces of index arrays are then nonempty. -/
noncomputable def uniformMean {A : Type*} [Fintype A] (h : A → ℝ) : ℝ :=
  (∑ a, h a) / (Fintype.card A : ℝ)

/-- The objective `f = (1/m) ∑ᵢ fᵢ` of §6.3. -/
noncomputable def objective {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  uniformMean (fun i => fs i x)

/-- The average gradient `∇f = (1/m) ∑ᵢ ∇fᵢ`. -/
noncomputable def fullGradient {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ((m : ℝ)⁻¹) • ∑ i, gs i x

/-- The SVRG direction `∇f_i(x) − ∇f_i(y) + ∇f(y)` at anchor `y`. -/
noncomputable def direction {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  gs i x - gs i y + fullGradient gs y

/-- Zero-based implementation of the inner SVRG iterates. `innerIter 0 = x₁ = y` in
the book's numbering, and sample `idx t` produces `innerIter (t+1) = x_{t+2}`.
The value beyond the first `k` updates is held constant; it is never used. -/
noncomputable def innerIter {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => y
  | t + 1 =>
      if ht : t < k then
        innerIter gs η y idx t - η • direction gs (innerIter gs η y idx t) y (idx ⟨t, ht⟩)
      else innerIter gs η y idx t

/-- The epoch output `y⁽ˢ⁺¹⁾ = (1/k) ∑_{t=1}^k x⁽ˢ⁾_t`.
In particular it does not average the final updated point `x_{k+1}`. -/
noncomputable def epochOut {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) :
    EuclideanSpace ℝ (Fin n) :=
  ((k : ℝ)⁻¹) • ∑ t : Fin k, innerIter gs η y idx t.val

/-- After `s` epochs, with an array of `s` independent index blocks.
`epochOutput 0 = y⁽¹⁾` and `epochOutput s = y⁽ˢ⁺¹⁾`. -/
noncomputable def epochOutput {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y₁ : EuclideanSpace ℝ (Fin n)) :
    (s : ℕ) → (Fin s → Fin k → Fin m) → EuclideanSpace ℝ (Fin n)
  | 0, _ => y₁
  | s + 1, idx =>
      epochOut gs η k (epochOutput gs η y₁ s (fun j => idx j.castSucc)) (idx (Fin.last s))

end ConvexOptAlg.SVRG


