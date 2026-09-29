-- Prove2me | Definitions.Def_ResidueCalcOnRectangles_defs
-- name    : ResidueCalcOnRectangles_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:49:17.696423+00:00
-- url     : https://prove2.me/theorems/94e30930-6235-4c5a-93f2-6deede233acd
-- title:
--   Contour integrals over rectangles in $\mathbb{C}$: horizontal/vertical integrals, $\mathrm{RectangleIntegral}$, $\mathrm{VerticalIntegral}$, and border integrability
-- statement:
--   This bundle defines the contour-integration primitives for residue calculus on axis-parallel rectangles in $\mathbb{C}$, for functions $f : \mathbb{C} \to E$ valued in a complex normed space.
--
--   **Main definitions.**
--
--   - `HIntegral f x₁ x₂ y` — the horizontal contour integral $\int_{x_1}^{x_2} f(x + iy)\,dx$ along the segment at height $y$.
--
--   - `VIntegral f x y₁ y₂` — the vertical contour integral $i\int_{y_1}^{y_2} f(x + iy)\,dy$ along the segment at abscissa $x$ (the factor $i$ accounts for $ds = i\,dy$).
--
--   - `RectangleIntegral f z w` — the counterclockwise contour integral over the rectangle with corners $z, w$: $\oint_{\partial R} f = \int_{z.\mathrm{re}}^{w.\mathrm{re}} f(x + i\,z.\mathrm{im})\,dx - \int_{z.\mathrm{re}}^{w.\mathrm{re}} f(x + i\,w.\mathrm{im})\,dx + i\int_{z.\mathrm{im}}^{w.\mathrm{im}} f(w.\mathrm{re} + iy)\,dy - i\int_{z.\mathrm{im}}^{w.\mathrm{im}} f(z.\mathrm{re} + iy)\,dy$; `RectangleIntegral'` is the same divided by $2\pi i$, so that a simple pole of residue $c$ inside contributes exactly $c$.
--
--   - `VerticalIntegral f σ` — the full vertical line integral $i\int_{-\infty}^{\infty} f(\sigma + it)\,dt$ along $\Re s = \sigma$, and `VerticalIntegral'`, its normalization by $\frac{1}{2\pi i}$ — the standard Mellin/Perron inversion integral $\frac{1}{2\pi i}\int_{(\sigma)} f(s)\,ds$.
--
--   - `HolomorphicOn f s` — abbreviation for $f$ being complex-differentiable on the set $s$ (`DifferentiableOn ℂ f s`).
--
--   - `RectangleBorderIntegrable f z w` — the proposition that $f$ is interval-integrable along each of the four edges of the rectangle with corners $z, w$, the minimal hypothesis for the rectangle integral to be well-behaved.
--
--   **Downstream use.** These primitives support the rectangle residue theorem (the normalized rectangle integral of a function with simple poles equals the sum of the residues at interior poles), contour-shifting lemmas (a vertical integral can be moved from $\Re s = \sigma_1$ to $\Re s = \sigma_2$ picking up rectangle contributions), and the pull-in of the Perron/Mellin contour for $-\zeta'/\zeta$ in the prime number theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean (definitions vendored from this file)

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Rectangle_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)


/-- A `RectangleIntegral` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

/-- A `RectangleIntegral'` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`, divided by `2 * π * I`. -/
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w


noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ


/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s


def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im


/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/


-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.


-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.


-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.


