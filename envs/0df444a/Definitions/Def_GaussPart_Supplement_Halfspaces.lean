-- Prove2me | Definitions.Def_GaussPart_Supplement_Halfspaces
-- name    : GaussPart_Supplement_Halfspaces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:02:23.187803+00:00
-- url     : https://prove2.me/theorems/258da79a-15e0-49f4-b68b-bd368b437f9a
-- title:
--   Intersections $\mathcal F_k$ and unions of at most $k$ halfspaces, and convex $K$-MIMs $\mathcal C_K$
-- statement:
--   A halfspace indicator takes the value $1$ when $w\cdot x\le t$ and $-1$ otherwise ($w\in\mathbb R^d$, $t\in\mathbb R$; $w=0$ gives a constant).
--
--   - $\mathcal F_k$: the **intersections of at most $k$ halfspaces**, $f(x)=1$ exactly when $w^{(i)}\cdot x\le t_i$ for all $i\le j$, for some $j\le k$; the empty intersection is the constant $1$, so $\mathcal F_k$ contains the constant functions.
--   - The **unions of at most $k$ halfspaces**: $f(x)=1$ exactly when $w^{(i)}\cdot x\le t_i$ for some $i\le j$, $j\le k$; the empty union is the constant $-1$.
--   - $\mathcal C_K$: the Boolean $K$-MIMs on $\mathbb R^d$ whose positive region $\{x:f(x)=1\}$ is convex.
--
--   These are the concrete classes of Theorems 5.12–5.14, 7.3 and Corollary 6.4.
--
--   **Formalization Note** Halfspaces are closed. Under a distribution that is smooth with respect to $\mathcal N(0,I_d)$ the choice is immaterial (hyperplanes are null); Theorem 7.3's proof uses the closed slab $\{|v\cdot x|\le t\}$.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), §5.3, p.53 (PDF p.55); Corollary 4.8, p.43 (PDF p.45); Corollary 6.4, p.62; Theorem 7.3, p.64

import Mathlib
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_Supplement_BoolFn

open scoped RealInnerProductSpace

namespace GaussPart

namespace Supplement

/-- **`F_k`**, the intersections of at most `k` halfspaces, including the constant functions
(arXiv:2611.05264, sha256 7e0ca6d4…, §5.3, p.53, PDF p.55): `f(x) = 1` exactly when
`w⁽ⁱ⁾ · x ≤ tᵢ` for all `i < j`, for some `j ≤ k`, normals `w⁽ⁱ⁾ ∈ ℝᵈ` and thresholds `tᵢ ∈ ℝ`.

**Formalization Note.** Halfspaces are closed (`≤`). A normal `w = 0` gives a constant halfspace, so
for `k ≥ 1` the class contains both constants (`j = 0` gives the constant `1`). -/
def IntersectionClass (d k : ℕ) : Set (Vec d → ℝ) :=
  {f | ∃ j ≤ k, ∃ (w : Fin j → Vec d) (t : Fin j → ℝ),
    f = fun x => if ∀ i, ⟪w i, x⟫ ≤ t i then 1 else -1}

/-- The unions of at most `k` halfspaces (Corollary 6.4, p.62, PDF p.64): `f(x) = 1` exactly when
`w⁽ⁱ⁾ · x ≤ tᵢ` for some `i < j`, `j ≤ k`. The complement of such a union is an intersection of at
most `k` (open) halfspaces. -/
def UnionClass (d k : ℕ) : Set (Vec d → ℝ) :=
  {f | ∃ j ≤ k, ∃ (w : Fin j → Vec d) (t : Fin j → ℝ),
    f = fun x => if ∃ i, ⟪w i, x⟫ ≤ t i then 1 else -1}

/-- **`C_K`** (Corollary 4.8, p.43, PDF p.45; Theorem 5.13, p.54): the Boolean `K`-MIMs on `ℝᵈ` whose
positive region `{x : f(x) = 1}` is convex. -/
def ConvexClass (d K : ℕ) : Set (Vec d → ℝ) :=
  {f | IsBoolFn f ∧ IsKMIM K f ∧ Convex ℝ {x | f x = 1}}

end Supplement

end GaussPart


