-- Prove2me | Definitions.Def_ConantTerry_Orders_extraction_height
-- name    : ConantTerry_Orders_extraction_height
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:22.167284+00:00
-- url     : https://prove2.me/theorems/6256cc4b-f549-4614-a8d4-49974885d51d
-- title:
--   The extraction dichotomy P and its partial least height T
-- statement:
--   Fix arbitrary sets $X,Y$, a function $f:X\times Y\to[0,1]$ and a real scale $\delta$. For positive integers $k,\ell,t$, the assertion $P(k,\ell,t)$ quantifies over every $(t,2\delta)$-tree witness $(x,y,r)$ for this fixed $f$. At least one of these alternatives must hold:
--
--   1. There are $\alpha:[k]\to B_{<t}$ and $\beta:[k]\to B_t$ such that
--   $$
--   i\le j\Longrightarrow f(x_{\alpha(j)},y_{\beta(i)})\ge r_{\alpha(j)}+\delta,
--   \qquad
--   i<j\Longrightarrow f(x_{\alpha(i)},y_{\beta(j)})\le r_{\alpha(i)}.
--   $$
--   2. There are $\alpha:[\ell]\to B_{<t}$ and $\beta:[\ell]\to B_t$ such that
--   $$
--   i\le j\Longrightarrow f(x_{\alpha(j)},y_{\beta(i)})<r_{\alpha(j)}+\delta,
--   \qquad
--   i<j\Longrightarrow f(x_{\alpha(i)},y_{\beta(j)})\ge r_{\alpha(i)}+2\delta.
--   $$
--   In particular, the first inequality in alternative (II) is strict. Define
--   $$
--   T(k,\ell)=\min\{t\ge1:P(k,\ell,t)\}
--   $$
--   when the set is nonempty. Lean represents the undefined case by $+\infty$ in `WithTop ℕ`: it uses `Nat.find` only in the branch supplied with an actual positive-height existence proof. Thus $T(k,\ell)\ne+\infty$ asserts existence, not an assumed recurrence.
--
--   These computed quantities expose the exact intermediate target in Section 3. All tree witnesses are universally quantified, and $T$ depends on the fixed $f,\delta$ rather than on arbitrary supplied numerical data. `Fin` is the order-preserving reindexing of the source sequences.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.10, Section 3, proof of Theorem 1.11, Statement of P and definition of T before Claim 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree

namespace ConantTerry.Orders

/-- Alternative (I) of P(k,ℓ,t), Section 3, p.10. -/
def ExtractionI {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (k t : ℕ)
    (x : WordsBelow t → X) (y : WordsAt t → Y)
    (r : WordsBelow t → Set.Icc (0 : ℝ) 1) : Prop :=
  ∃ (α : Fin k → WordsBelow t) (β : Fin k → WordsAt t),
    ∀ i j : Fin k,
      (i ≤ j → (r (α j) : ℝ) + δ ≤ (f (x (α j), y (β i)) : ℝ)) ∧
      (i < j → (f (x (α i), y (β j)) : ℝ) ≤ (r (α i) : ℝ))

/-- Alternative (II) of P(k,ℓ,t), Section 3, p.10; the first inequality is strict. -/
def ExtractionII {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (ℓ t : ℕ)
    (x : WordsBelow t → X) (y : WordsAt t → Y)
    (r : WordsBelow t → Set.Icc (0 : ℝ) 1) : Prop :=
  ∃ (α : Fin ℓ → WordsBelow t) (β : Fin ℓ → WordsAt t),
    ∀ i j : Fin ℓ,
      (i ≤ j → (f (x (α j), y (β i)) : ℝ) < (r (α j) : ℝ) + δ) ∧
      (i < j → (r (α i) : ℝ) + 2 * δ ≤ (f (x (α i), y (β j)) : ℝ))

/-- The source's P, universally quantified over every tree witness for fixed f,δ. -/
def ExtractionP {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (k ℓ t : ℕ) : Prop :=
  ∀ (x : WordsBelow t → X) (y : WordsAt t → Y)
    (r : WordsBelow t → Set.Icc (0 : ℝ) 1),
      IsFunctionTree f t (2 * δ) x y r →
        ExtractionI f δ k t x y r ∨ ExtractionII f δ ℓ t x y r

/-- The least POSITIVE height satisfying P, or top when none exists.
The dependent minimum is only evaluated when an actual witness exists.
Section 3, immediately before Claim 1, p.10. -/
noncomputable def extractionHeight {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (k ℓ : ℕ) : WithTop ℕ := by
  classical
  exact if h : ∃ t : ℕ, 1 ≤ t ∧ ExtractionP f δ k ℓ t
    then (Nat.find h : WithTop ℕ) else ⊤

end ConantTerry.Orders


