-- Prove2me | Definitions.Def_ChaChaTree_DynOpt_Rectangles
-- name    : ChaChaTree_DynOpt_Rectangles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:21:46.089591+00:00
-- url     : https://prove2.me/theorems/ba57671a-dade-42b0-8468-1e75b524f074
-- title:
--   Rectangles, independence and the bounds IR (Def. 3) and SIR (Def. 11)
-- statement:
--   A **rectangle** $\square_{p,q}$ on $P$ is given by points $p, q \in P$ with $p.y < q.y$ and $p.x \neq q.x$ (`IsRectOn P (p, q)`, a `Rect` being the ordered pair $(p,q)$). Its **corners** are $p$, $(p.x, q.y)$, $q$, $(q.x, p.y)$. It is **left** if $q.x < p.x$ and **right** if $p.x < q.x$.
--
--   $r$ **contains** $u$ if $p.y \le u.y \le q.y$ and $\min(p.x,q.x) \le u.x \le \max(p.x,q.x)$; it **strictly contains** $u$ if all four inequalities are strict. $r$ is **input-free** if it contains no point of $P$ other than $p$ or $q$.
--
--   **Definition 3.** A set $R$ of rectangles on $P$ is **independent** if every rectangle is input-free and, for any two distinct $r_1, r_2 \in R$, neither strictly contains a corner of the other. $\mathrm{IR}(P)$ is the size of the largest independent set.
--
--   **Definition 11.** $R$ is **strictly independent** if every rectangle is input-free and any two distinct rectangles either share a defining point or neither contains (non-strictly) a corner of the other. $\mathrm{SIR}(P)$ is the size of the largest strictly independent set.
--
--   **Formalization Note.** Both maxima are taken over the subsets of $P \times P$ (every rectangle on $P$ lies there), so they are maxima over a finite nonempty family (the empty set qualifies).
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), §4.1, p. 11 (PDF 12); Definition 3, p. 11 (PDF 12); Definition 11, p. 14 (PDF 15)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-! # Rectangles, independence, `IR` (Definition 3) and `SIR` (Definition 11)

Čech et al., *Dynamic Optimality to within O(log log log n)*, STOC 2027 submission (manuscript,
sha256 9316fbfd…), §4.1, p. 11 (PDF 12) and §4.3, p. 14 (PDF 15).

A rectangle `□_{p,q}` is represented by the ordered pair `(p, q)` of its defining points. -/

/-- A rectangle `□_{p,q}`, given by its defining points `(p, q)`. -/
abbrev Rect := (ℕ × ℕ) × (ℕ × ℕ)

/-- `r = □_{p,q}` is a **rectangle on `P`**: `p, q ∈ P`, `p.y < q.y` and `p.x ≠ q.x`. -/
abbrev IsRectOn (P : Finset (ℕ × ℕ)) (r : Rect) : Prop :=
  r.1 ∈ P ∧ r.2 ∈ P ∧ r.1.2 < r.2.2 ∧ r.1.1 ≠ r.2.1

/-- The four **corners** `p, (p.x, q.y), q, (q.x, p.y)` of `□_{p,q}`. -/
def corners (r : Rect) : List (ℕ × ℕ) :=
  [r.1, (r.1.1, r.2.2), r.2, (r.2.1, r.1.2)]

/-- `□_{p,q}` is a **left** rectangle: `(p, q)` is left (`q.x < p.x`). -/
abbrev IsLeftRect (r : Rect) : Prop := r.2.1 < r.1.1

/-- `□_{p,q}` is a **right** rectangle: `(p, q)` is right (`p.x < q.x`). -/
abbrev IsRightRect (r : Rect) : Prop := r.1.1 < r.2.1

/-- `r` **contains** `u`: `p.y ≤ u.y ≤ q.y` and `min(p.x, q.x) ≤ u.x ≤ max(p.x, q.x)`
(closed rectangle). -/
abbrev RContains (r : Rect) (u : ℕ × ℕ) : Prop :=
  r.1.2 ≤ u.2 ∧ u.2 ≤ r.2.2 ∧ min r.1.1 r.2.1 ≤ u.1 ∧ u.1 ≤ max r.1.1 r.2.1

/-- `r` **strictly contains** `u`: `p.y < u.y < q.y` and `min(p.x, q.x) < u.x < max(p.x, q.x)`
(open rectangle). -/
abbrev RStrictlyContains (r : Rect) (u : ℕ × ℕ) : Prop :=
  r.1.2 < u.2 ∧ u.2 < r.2.2 ∧ min r.1.1 r.2.1 < u.1 ∧ u.1 < max r.1.1 r.2.1

/-- `r` is **input-free** in `P`: it contains no point of `P` other than `p` or `q`. -/
abbrev InputFree (P : Finset (ℕ × ℕ)) (r : Rect) : Prop :=
  ∀ u ∈ P, RContains r u → u = r.1 ∨ u = r.2

/-- **Definition 3.** A set `R` of rectangles on `P` is **independent**: every rectangle of `R`
is input-free, and for any two (distinct) rectangles of `R`, neither strictly contains a corner of
the other. -/
abbrev IsIndependent (P : Finset (ℕ × ℕ)) (R : Finset Rect) : Prop :=
  (∀ r ∈ R, IsRectOn P r ∧ InputFree P r) ∧
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → ∀ c ∈ corners r₂, ¬ RStrictlyContains r₁ c

/-- **The rectangle bound** `IR(P)`: the size of the largest independent set of rectangles on
`P` (every rectangle on `P` lies in `P × P`, so the maximum is over a finite family). -/
def IR (P : Finset (ℕ × ℕ)) : ℕ :=
  ((P ×ˢ P).powerset.filter fun R => IsIndependent P R).sup Finset.card

/-- Two rectangles **share a defining point**. -/
abbrev ShareDefiningPoint (r₁ r₂ : Rect) : Prop :=
  r₁.1 = r₂.1 ∨ r₁.1 = r₂.2 ∨ r₁.2 = r₂.1 ∨ r₁.2 = r₂.2

/-- Neither of `r₁`, `r₂` contains (non-strictly) a corner of the other. -/
abbrev NoCornerContained (r₁ r₂ : Rect) : Prop :=
  (∀ c ∈ corners r₂, ¬ RContains r₁ c) ∧ (∀ c ∈ corners r₁, ¬ RContains r₂ c)

instance (r₁ r₂ : Rect) : Decidable (ShareDefiningPoint r₁ r₂) := by
  unfold ShareDefiningPoint; infer_instance

instance (r₁ r₂ : Rect) : Decidable (NoCornerContained r₁ r₂) := by
  unfold NoCornerContained; infer_instance

/-- **Definition 11.** A set `R` of rectangles on `P` is **strictly independent**: every
rectangle of `R` is input-free, and any two (distinct) rectangles of `R` either share a defining
point, or neither contains a corner of the other. -/
abbrev IsStrictlyIndependent (P : Finset (ℕ × ℕ)) (R : Finset Rect) : Prop :=
  (∀ r ∈ R, IsRectOn P r ∧ InputFree P r) ∧
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → ShareDefiningPoint r₁ r₂ ∨ NoCornerContained r₁ r₂

/-- **The strict rectangle bound** `SIR(P)`: the size of the largest strictly independent set of
rectangles on `P`. -/
def SIR (P : Finset (ℕ × ℕ)) : ℕ :=
  ((P ×ˢ P).powerset.filter fun R => IsStrictlyIndependent P R).sup Finset.card

end ChaChaTree.DynOpt


