-- Prove2me | Definitions.Def_ContinualHardness_Linear_Dataset
-- name    : ContinualHardness_Linear_Dataset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:11:08.471199+00:00
-- url     : https://prove2.me/theorems/f987aa5a-60d5-4bef-9349-6c01664e90d7
-- title:
--   Finite weighted datasets, the sign with sign(0) = −1, accuracy, linear classifiers, symmetry and separability
-- statement:
--   Feature vectors are real vectors $x\in\mathbb R^\iota$ indexed by a finite set $\iota$ (for $\mathbb R^d$ take $\iota=[d]$; the dictatorship test uses $\iota=[T]\times[M]$). A **finite weighted dataset** $D$ is a finitely supported weight $D:\mathbb R^\iota\times\mathbb Z\to\mathbb R$ on labelled points $(x,y)$ such that every weight is non-negative, the weights sum to $1$, and every point of positive weight has label $y\in\{-1,1\}$ (`IsDataset`); $D$ is thought of as a distribution over a finite set of labelled points, and repeated points have their weights added. The label of a boolean $b$ is $1$ if $b$ is true and $-1$ otherwise (`labelOf`).
--
--   The **sign** is the paper's Eq. (1):
--   $$\operatorname{sign}(a)=\begin{cases}1 & a>0,\\ -1 & \text{otherwise,}\end{cases}$$
--   so $\operatorname{sign}(0)=-1$ (`sgn`). The **accuracy** of a classifier $f:\mathbb R^\iota\to\mathbb Z$ is $\mathrm{Acc}(D,f)=\Pr_{(x,y)\leftarrow D}[f(x)=y]=\sum_{(x,y)} D(x,y)\,[f(x)=y]$ (`acc`). A **linear classifier** is $x\mapsto\operatorname{sign}(r^{\mathsf T}x+c)$ with $r\in\mathbb R^\iota$, $c\in\mathbb R$ (`linClf r c`); it is **homogeneous** when $c=0$.
--
--   $D$ is **symmetric** if $D(x,y)=D(-x,-y)$ for every $(x,y)$, i.e. $(-x,-y)$ is an equally likely sample (`IsSymmetric`). $D$ is **linearly separable** if some homogeneous linear classifier $\operatorname{sign}(r^{\mathsf T}x)$ has accuracy $1$ on $D$ (`IsSeparable`), as in condition 1 of Theorem 3.1.
--
--   **Formalization Note.** Labels are integers and the dataset predicate restricts the support to $\{-1,1\}$; Mathlib's `Real.sign` is not used because it returns $0$ at $0$.
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), pp. 4-5, §2.1 and Eq. (1) (PDF pp. 5-6); p. 7, Theorem 3.1 condition 1 (PDF p. 8)

import Mathlib

namespace ContinualHardness.Linear

/-! # Finite weighted classification datasets, the sign with `sign(0) = -1`, accuracy, linear
classifiers, symmetry and separability (Saket, §2.1, Eq. (1), Theorem 3.1)

Feature vectors are real vectors indexed by a finite type `ι` (`ι = Fin d` for `ℝ^d`, or
`ι = Fin T × Fin M` for the dictatorship test). Labels are integers; a dataset only puts weight on
the labels `1` and `-1`. -/

/-- The paper's sign function, Eq. (1): `sign(a) = 1` if `a > 0`, and `-1` otherwise.
In particular `sign 0 = -1` (unlike `Real.sign` and `SignType.sign`, which give `0`). -/
noncomputable def sgn (a : ℝ) : ℤ := if 0 < a then 1 else -1

/-- The label `±1` encoded by a boolean: `true ↦ 1`, `false ↦ -1`. -/
def labelOf (b : Bool) : ℤ := if b then 1 else -1

/-- A finitely supported weight on labelled data-points `(x, y) ∈ ℝ^ι × ℤ`. A *dataset* is such a
weight satisfying `IsDataset`. -/
abbrev WData (ι : Type) := (ι → ℝ) × ℤ →₀ ℝ

/-- `D` is a finite dataset of labelled data-points from `ℝ^ι × {-1, 1}` with a non-negative
probability weight: every weight is non-negative, the weights sum to `1`, and every point of
positive weight has label `1` or `-1`. -/
def IsDataset {ι : Type} (D : WData ι) : Prop :=
  (∀ p, 0 ≤ D p) ∧ (D.sum fun _ a => a) = 1 ∧ ∀ p ∈ D.support, p.2 = 1 ∨ p.2 = -1

/-- Accuracy `Acc(D, f) = Pr_{(x,y) ← D}[f(x) = y]`: the total weight of the points that `f`
labels correctly. -/
noncomputable def acc {ι : Type} (D : WData ι) (f : (ι → ℝ) → ℤ) : ℝ :=
  D.sum fun p a => if f p.1 = p.2 then a else 0

/-- The linear classifier `x ↦ sign(rᵀx + c)`; it is homogeneous when `c = 0`. -/
noncomputable def linClf {ι : Type} [Fintype ι] (r : ι → ℝ) (c : ℝ) : (ι → ℝ) → ℤ :=
  fun x => sgn ((∑ i, r i * x i) + c)

/-- `D` is symmetric: for each `(x, y)`, the point `(-x, -y)` carries the same weight. -/
def IsSymmetric {ι : Type} (D : WData ι) : Prop :=
  ∀ x : ι → ℝ, ∀ y : ℤ, D (x, y) = D (-x, -y)

/-- `D` is linearly separable (Theorem 3.1, condition 1): some homogeneous linear classifier
`sign(rᵀx)` has accuracy `1` on `D`. -/
def IsSeparable {ι : Type} [Fintype ι] (D : WData ι) : Prop :=
  ∃ r : ι → ℝ, acc D (linClf r 0) = 1

end ContinualHardness.Linear


