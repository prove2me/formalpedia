-- Prove2me | Definitions.Def_NNPartTree_Cuts
-- name    : NNPartTree_Cuts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:42.537065+00:00
-- url     : https://prove2.me/theorems/99be0f42-339c-46d0-8ec8-931aa1752796
-- title:
--   Cuts, halfspaces, polynomial threshold functions, $(R,J)$-halfspace functions, cut error and balance
-- statement:
--   Fix $d$. With the convention $\mathrm{sign}(0)=1$, a **halfspace** is $f(x)=\mathrm{sign}(\langle h,x\rangle-\theta)$, and a **degree-$k$ polynomial threshold function** is $f(x)=\mathrm{sign}(A(x))$ with $\deg A\le k$. A **cut** is a measurable function $\mathbb R^d\to\{-1,1\}$.
--
--   A **$J$-wise intersection of halfspaces** is a function $g$ into $\{-1,1\}$ with $g(z)=1$ iff $f_j(z)=1$ for all $j\in[J]$, for $J$ halfspaces $f_j$. An **$(R,J)$-halfspace function** is a function $h$ into $\{-1,1\}$ with $h(z)=1$ iff $g_r(z)=1$ for some $r\in[R]$, for $R$ disjoint $J$-wise intersections $g_r$.
--
--   For a law $\mathcal D$ on pairs $(x,y)\in\mathbb R^d\times\mathbb R^d$ with marginals $\mathcal D_X,\mathcal D_Y$,
--   $$\mathrm{err}_{\mathcal D}(f)=\Pr_{(x,y)\sim\mathcal D}[f(x)\ne f(y)],\qquad \mathrm{bal}_{\mathcal D}(f)=\min\Big\{\Pr_{y\sim\mathcal D_Y}[f(y)=1],\Pr_{y\sim\mathcal D_Y}[f(y)=-1]\Big\},$$
--   and $\mathrm{OPT}_\beta(\mathcal F)=\inf\{\mathrm{err}_{\mathcal D}(f): f\in\mathcal F,\ \mathrm{bal}_{\mathcal D}(f)\ge\beta\}$.
--
--   These are the objects compared throughout: the learner competes with the best balanced cut in a class.
--
--   **Formalization Note** Cuts are real-valued, so that they enter polynomial approximations directly. The printed $\min$ in $\mathrm{OPT}_\beta$ is an infimum here, since it need not be attained on an infinite class.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), §3.1, p.10; Definition 3.1, p.10; Definition 3.2, p.10; Definitions 6.3, 6.4, p.23

import Mathlib
import Definitions.Def_NNPartTree_Machine

open MeasureTheory

namespace NNPartTree

/-!
# Cuts, halfspaces, polynomial threshold functions, cut error and balance

S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (STOC 2027 submission), held copy of 2026-11-03, sha256 d32992f2…, §3.1, p.10,
Definitions 3.1 (p.10), 6.3 and 6.4 (p.23).

**Formalization Note.**
* Cuts are real-valued functions with values in `{−1, 1}`, so that they enter polynomial
  approximations directly. A cut class member is measurable (`IsCut`), which a probability of a cut
  event needs. Halfspaces and polynomial threshold functions are measurable automatically.
* `err` and `bal` are real numbers, read off a probability measure on pairs. On a measure of mass
  different from `1` they have no meaning; every statement takes a probability measure.
-/

variable {d : ℕ}

/-- `sign` with the convention `sign(0) = 1` (§3.1, p.10), real-valued. -/
noncomputable def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

/-- The value `A(x)` of a polynomial on a point of `ℝᵈ`. -/
noncomputable def peval (A : MvPolynomial (Fin d) ℝ) (x : Pt d) : ℝ :=
  MvPolynomial.eval (fun i => x i) A

/-- The threshold cut `g_{F,θ}(x) = sign(F(x) − θ)` (Lemma 5.1, p.16). -/
noncomputable def thresholdCut (F : Pt d → ℝ) (θ : ℝ) : Pt d → ℝ := fun x => sgn (F x - θ)

/-- A cut: a measurable function `ℝᵈ → {−1, 1}` (§5, p.14). -/
def IsCut (f : Pt d → ℝ) : Prop := Measurable f ∧ ∀ x, f x = 1 ∨ f x = -1

/-- A halfspace `f(x) = sign(⟨h, x⟩ − θ)` (§3.1, p.10). `h = 0` is allowed, as printed. -/
def IsHalfspace (f : Pt d → ℝ) : Prop := ∃ (h : Pt d) (θ : ℝ), ∀ x, f x = sgn (inner ℝ h x - θ)

/-- A degree-`k` polynomial threshold function `f(x) = sign(A(x))`, `deg A ≤ k`: the class `P_k`
(§3.1, p.10). -/
def IsPTF (k : ℕ) (f : Pt d → ℝ) : Prop :=
  ∃ A : MvPolynomial (Fin d) ℝ, A.totalDegree ≤ k ∧ ∀ x, f x = sgn (peval A x)

/-- A `J`-wise intersection of halfspaces: `g(z) = 1` iff `f_j(z) = 1` for all `j ∈ [J]`
(Definition 6.3, p.23), and `g` takes values in `{−1, 1}`. -/
def IsJWise (J : ℕ) (g : Pt d → ℝ) : Prop :=
  ∃ fs : Fin J → Pt d → ℝ, (∀ j, IsHalfspace (fs j)) ∧ (∀ z, g z = 1 ∨ g z = -1) ∧
    ∀ z, g z = 1 ↔ ∀ j, fs j z = 1

/-- An `(R, J)`-halfspace function (Definition 6.4, p.23): `h = 1` exactly on the union of `R`
disjoint `J`-wise intersections of halfspaces, and `h` takes values in `{−1, 1}`. -/
def IsRJFunction (R J : ℕ) (h : Pt d → ℝ) : Prop :=
  ∃ gs : Fin R → Pt d → ℝ, (∀ r, IsJWise J (gs r)) ∧ (∀ z, h z = 1 ∨ h z = -1) ∧
    (∀ z r r', gs r z = 1 → gs r' z = 1 → r = r') ∧ ∀ z, h z = 1 ↔ ∃ r, gs r z = 1

/-- The `x`-marginal `D_X` of a law on pairs (§3.1, p.10). -/
noncomputable def marginalX (D : Measure (Pt d × Pt d)) : Measure (Pt d) := D.map Prod.fst

/-- The `y`-marginal `D_Y` of a law on pairs (§3.1, p.10). In §6 this is `D_nn`. -/
noncomputable def marginalY (D : Measure (Pt d × Pt d)) : Measure (Pt d) := D.map Prod.snd

instance (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] :
    IsProbabilityMeasure (marginalX D) :=
  Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

instance (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] :
    IsProbabilityMeasure (marginalY D) :=
  Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- The cut error `err_D(f) = Pr_{(x,y)∼D}[f(x) ≠ f(y)]` (Definition 3.1, p.10). -/
noncomputable def err (D : Measure (Pt d × Pt d)) (f : Pt d → ℝ) : ℝ :=
  (D {z | f z.1 ≠ f z.2}).toReal

/-- The balance `bal_D(f) = min{Pr_{y∼D_Y}[f(y) = 1], Pr_{y∼D_Y}[f(y) = −1]}` (Definition 3.1,
p.10). -/
noncomputable def bal (D : Measure (Pt d × Pt d)) (f : Pt d → ℝ) : ℝ :=
  min ((marginalY D {y | f y = 1}).toReal) ((marginalY D {y | f y = -1}).toReal)

/-- `OPT_β(F) = inf {err_D(f) | f ∈ F, bal_D(f) ≥ β}` (Definition 3.2, p.10, for a general class as
on p.15). The printed `min` need not be attained on an infinite class. -/
noncomputable def opt (D : Measure (Pt d × Pt d)) (β : ℝ) (F : Set (Pt d → ℝ)) : ℝ :=
  sInf {e | ∃ f ∈ F, β ≤ bal D f ∧ e = err D f}

end NNPartTree


