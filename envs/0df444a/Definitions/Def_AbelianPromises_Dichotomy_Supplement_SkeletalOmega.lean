-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Supplement_SkeletalOmega
-- name    : AbelianPromises_Dichotomy_Supplement_SkeletalOmega
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:52:48.019907+00:00
-- url     : https://prove2.me/theorems/6d57e61a-ef05-43f1-bb2c-d84c81cab082
-- title:
--   Skeletal affine matrices and the omega construction
-- statement:
--   For a nonempty finite set $X$, a skeletal affine matrix has an arbitrary nonempty finite column set $J$, signed integer entries $M(x,j)$, and column sums one. Its support is the set of rows with a nonzero entry. Every supported row has a unit column:
--
--   $$
--   \sum_{x\in X}M(x,j)=1,\qquad
--   x\in\operatorname{supp}M\Longrightarrow\exists j\in J\ \forall y\in X,
--   \ M(y,j)=\mathbf1_{y=x}.
--   $$
--
--   For an abstract minion $N$, the members of $\omega_{\mathrm{CSinglAIP}}(N)^{(X)}$ are pairs $(M,f)$ with $f\in N^{(\operatorname{supp}M)}$. The $\pi$-minor sums matrix rows over the fibres of $\pi$ and takes the minor of $f$ along the restriction of $\pi$ to the supports. The full matrix and its column set are retained. This is the affine-certificate construction used in the two new results.
--
--   **Formalization Note** Columns use $\operatorname{Fin}(j+1)$ for arbitrary $j$, with no upper bound. Support is redundant data fixed by an exact equality with the nonzero rows. The minor graph imposes equality of column counts, the exact fibre sums, and the exact restricted minor of $f$; it does not identify matrices that merely have the same support.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, STOC 2027 submission #967 (October 2026). Canonical submission artifact; no arXiv pin or acceptance claim. printed p. 19 (PDF p. 20), Definitions C.10 and C.11.

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Supplement_AbstractMinions

set_option autoImplicit false

namespace AbelianPromises.Dichotomy.Supplement

/-- Definition C.10. Fin(cols+1) represents an arbitrary finite nonempty column set.
The support is redundant data determined by support_exact, not an independent parameter.
Signed entries and every column are retained. -/
structure SkeletalMatrix (X : Arity) where
  cols : ℕ
  entry : X → Fin (cols + 1) → ℤ
  column_sum : ∀ j, ∑ x, entry x j = 1
  support : Arity
  support_exact : ∀ a : ℕ, a ∈ support.val ↔
    ∃ (x : X) (j : Fin (cols + 1)), x.val = a ∧ entry x j ≠ 0
  unit_column : ∀ a : support, ∃ j, ∀ x : X,
    entry x j = if x.val = a.val then 1 else 0

/-- Inclusion of the computed support in the original row set. -/
def SkeletalMatrix.row {X : Arity} (M : SkeletalMatrix X) (a : M.support) : X :=
  ⟨a.val, by
    obtain ⟨x, j, hx, hj⟩ := (M.support_exact a.val).mp a.property
    exact hx ▸ x.property⟩

/-- The actual matrix minor: column set is unchanged, rows are summed over fibres. -/
def MatrixMinor {X Y : Arity} (π : X → Y) (M : SkeletalMatrix X)
    (M' : SkeletalMatrix Y) : Prop :=
  ∃ h : M.cols = M'.cols, ∀ (y : Y) (j : Fin (M.cols + 1)),
    M'.entry y (Fin.cast (congrArg (fun n => n + 1) h) j) =
      ∑ x : X, if π x = y then M.entry x j else 0

/-- Definition C.11. The graph of the omega minor uses exactly the matrix fibre sum
and the restriction of π to the actual supports. No quotient by support or column data. -/
def omega (N : MinionPresentation) : MinionPresentation where
  Obj X := (M : SkeletalMatrix X) × N.Obj M.support
  IsMinor π a b := MatrixMinor π a.1 b.1 ∧
    ∃ ρ : a.1.support → b.1.support,
      (∀ x, (ρ x).val = (π (a.1.row x)).val) ∧ N.IsMinor ρ a.2 b.2

end AbelianPromises.Dichotomy.Supplement


