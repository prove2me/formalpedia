-- Prove2me | Definitions.Def_ContinualHardness_Linear_Instance
-- name    : ContinualHardness_Linear_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:12:00.224384+00:00
-- url     : https://prove2.me/theorems/09546125-1a9a-4bd9-8d1b-5d251edb4bb4
-- title:
--   Instances of continual linear classification with T tasks, their binary encoding, and the YES / NO sets of Theorem 3.1
-- statement:
--   Fix the number of tasks $T$. An **instance** $I$ consists of a dimension $d\in\mathbb N$ and, for each task $t\in[T]$, a finite list of labelled weighted points $(x,b,w)$ with rational coordinates $x\in\mathbb Q^d$, a label bit $b$ (label $1$ if true, $-1$ if false) and a rational weight $w$ (`CLInstance T`). The real dataset $D_t$ of task $t$ gives each point $(x,y)\in\mathbb R^d\times\mathbb Z$ the total weight of the listed points with these coordinates and this label (`CLInstance.data`).
--
--   The **binary code** of $I$ (`encodeCL`) is the code of $d$, followed, for $t=1,\dots,T$, by the list of points of task $t$, each point written as its $d$ rational coordinates, its label bit and its rational weight (codes of the Encoding definition). $T$ is a constant and is not written.
--
--   $I$ is **valid** (`CLInstance.Valid`) if for every $t$, $D_t$ is a finite weighted dataset (non-negative weights summing to $1$), symmetric, and linearly separable by a homogeneous linear classifier. For $\varepsilon,\delta>0$:
--   $$\mathrm{YES}_\varepsilon:\ I\text{ valid and }\exists r^*\in\mathbb R^d\ \forall t\in[T]:\ \mathrm{Acc}\big(D_t,\operatorname{sign}((r^*)^{\mathsf T}x)\big)\ge 1-\varepsilon,$$
--   $$\mathrm{NO}_\delta:\ I\text{ valid and }\forall r\in\mathbb R^d,\ c\in\mathbb R:\ \big|\{t\in[T]:\mathrm{Acc}(D_t,\operatorname{sign}(r^{\mathsf T}x+c))\ge \tfrac12+\delta\}\big|\le 1$$
--   (`CLYes ε`, `CLNo δ`). Data are rational because instances are inputs to an algorithm; the classifiers $r^*$, $r$, $c$ are real.
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 7, Theorem 3.1 (PDF p. 8); p. 4, §2.1 (PDF p. 5)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Dataset
import Definitions.Def_ContinualHardness_Linear_Encoding

namespace ContinualHardness.Linear

/-! # Instances of continual linear classification with `T` tasks, their binary encoding, and the
YES / NO conditions of Theorem 3.1

An instance consists of a dimension `d` and, for each task `t ∈ [T]` (`Fin T`), a finite list of
labelled weighted data-points `(x, b, w)` with rational coordinates `x ∈ ℚ^d`, label
`y = 1` if `b = true` and `y = -1` if `b = false`, and rational weight `w`. -/

/-- A labelled weighted data-point with rational coordinates in dimension `d`: the feature vector,
the label (`true` ↦ `1`, `false` ↦ `-1`) and the weight. -/
abbrev RatPoint (d : ℕ) := (Fin d → ℚ) × Bool × ℚ

/-- An instance with `T` tasks: a dimension `d` and one finite list of rational data-points per
task. -/
structure CLInstance (T : ℕ) where
  /-- The dimension `d` of the feature space `ℝ^d`. -/
  d : ℕ
  /-- The data-points of task `t`. -/
  task : Fin T → List (RatPoint d)

/-- The real weighted dataset `D_t` of task `t`: the weight of a point `(x, y) ∈ ℝ^d × ℤ` is the
total weight of the listed data-points with these real coordinates and this label (repeated
points add up). -/
noncomputable def CLInstance.data {T : ℕ} (I : CLInstance T) (t : Fin T) : WData (Fin I.d) :=
  ((I.task t).map fun p =>
    Finsupp.single ((fun i => ((p.1 i : ℚ) : ℝ)), labelOf p.2.1) ((p.2.2 : ℚ) : ℝ)).sum

/-- The binary code of one data-point: its `d` coordinates, its label bit, its weight. -/
def encPoint {d : ℕ} (p : RatPoint d) : List Bool :=
  (List.ofFn fun i => encRat (p.1 i)).flatten ++ [p.2.1] ++ encRat p.2.2

/-- The binary code of an instance (the number of tasks `T` is fixed and not written): the
dimension `d`, then for `t = 1, …, T` the list of data-points of task `t`. -/
def encodeCL {T : ℕ} (I : CLInstance T) : List Bool :=
  encNat I.d ++ (List.ofFn fun t => encList encPoint (I.task t)).flatten

/-- The promise shared by both cases of Theorem 3.1: every `D_t` is a finite dataset (non-negative
weights summing to `1`), symmetric, and linearly separable by a homogeneous linear classifier. -/
def CLInstance.Valid {T : ℕ} (I : CLInstance T) : Prop :=
  ∀ t : Fin T, IsDataset (I.data t) ∧ IsSymmetric (I.data t) ∧ IsSeparable (I.data t)

/-- YES instances of Theorem 3.1 (for `ε`): valid, and one homogeneous linear classifier
`sign((r*)ᵀx)`, `r* ∈ ℝ^d`, has accuracy at least `1 - ε` on every task. -/
def CLYes {T : ℕ} (ε : ℝ) (I : CLInstance T) : Prop :=
  I.Valid ∧ ∃ r : Fin I.d → ℝ, ∀ t : Fin T, 1 - ε ≤ acc (I.data t) (linClf r 0)

/-- NO instances of Theorem 3.1 (for `δ`): valid, and every linear classifier `sign(rᵀx + c)`,
`r ∈ ℝ^d`, `c ∈ ℝ`, has accuracy at least `1/2 + δ` on at most one task. -/
def CLNo {T : ℕ} (δ : ℝ) (I : CLInstance T) : Prop :=
  I.Valid ∧ ∀ (r : Fin I.d → ℝ) (c : ℝ),
    (Finset.univ.filter fun t : Fin T => 1 / 2 + δ ≤ acc (I.data t) (linClf r c)).card ≤ 1

end ContinualHardness.Linear


