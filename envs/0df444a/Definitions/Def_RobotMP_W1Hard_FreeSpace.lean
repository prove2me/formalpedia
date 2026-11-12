-- Prove2me | Definitions.Def_RobotMP_W1Hard_FreeSpace
-- name    : RobotMP_W1Hard_FreeSpace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:41:45.940032+00:00
-- url     : https://prove2.me/theorems/9dfae285-0488-4600-b906-e2376ae9616b
-- title:
--   Unit-square robots, free configurations, feasible plans and reachability (§1.1)
-- statement:
--   Let $\square = \{x \in \mathbb R^2 : \|x\|_\infty \le 1\}$ be the closed axis-aligned square of side length $2$ centred at the origin. A robot placed at $p \in \mathbb R^2$ occupies $p + \square$; robots translate and never rotate. The $\ell_\infty$-distance of $p, q \in \mathbb R^2$ is $\|p - q\|_\infty = \max(|p_1 - q_1|, |p_2 - q_2|)$.
--
--   For a workspace $W \subseteq \mathbb R^2$, the **free space of one robot** is
--   $$F = \{x \in W : x + \square \subseteq W\}.$$
--   A configuration $p = (p_1, \dots, p_k) \in (\mathbb R^2)^k$ of $k$ robots is **free** if $p_i \in F$ for every $i$ and $\|p_i - p_j\|_\infty \ge 2$ for every pair $i \ne j$. Robots may touch each other and the boundary of $W$.
--
--   For configurations $s, t$, an **$(s,t)$-plan** is a map $\pi : [0, T] \to (\mathbb R^2)^k$, $T \ge 0$, continuous on $[0, T]$, with $\pi(0) = s$ and $\pi(T) = t$; it is **feasible** if $\pi(u)$ is free for every $u \in [0, T]$. The pair $(s, t)$ is **reachable** in $W$ if a feasible $(s, t)$-plan exists.
--
--   These are the objects of the reachability problem for multi-robot motion planning (MRMP) with unit-square robots.
--
--   **Formalization Note.** Points are `ℝ × ℝ`; a configuration is `Fin k → ℝ × ℝ` with the product topology. The plan is a function `ℝ → (Fin k → ℝ × ℝ)` required to be continuous on `[0, T]` only; its values outside `[0, T]` are irrelevant.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), pp. 1–2, §1.1

import Mathlib

set_option autoImplicit false

namespace RobotMP.W1Hard

open Set

/-- The robot placed at `p ∈ ℝ²`: the closed axis-aligned square `p + □` of side length 2
centred at `p`, where `□ = {x ∈ ℝ² : ‖x‖∞ ≤ 1}` (Agarwal–Holmgren–Stade, §1.1, p. 1). -/
def robotSquare (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | |x.1 - p.1| ≤ 1 ∧ |x.2 - p.2| ≤ 1}

/-- The ℓ∞-distance `‖p - q‖∞ = max (|p₁ - q₁|, |p₂ - q₂|)` of two points of the plane. -/
def linfDist (p q : ℝ × ℝ) : ℝ :=
  max |p.1 - q.1| |p.2 - q.2|

/-- The free space of a single robot in the workspace `W`:
`F = {x ∈ W | x + □ ⊆ W}`. -/
def freeSpace (W : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | x ∈ W ∧ robotSquare x ⊆ W}

/-- A configuration `p = (p₁, …, p_k)` of `k` robots is *free* in `W`: every `pᵢ` lies in the
free space `F` and `‖pᵢ - pⱼ‖∞ ≥ 2` for every pair `i ≠ j` (robots may touch each other and the
boundary of `W`). -/
def IsFreeConfig (W : Set (ℝ × ℝ)) {k : ℕ} (p : Fin k → ℝ × ℝ) : Prop :=
  (∀ i, p i ∈ freeSpace W) ∧ ∀ i j, i ≠ j → 2 ≤ linfDist (p i) (p j)

/-- `π` restricted to `[0, T]` is a feasible `(s, t)`-plan in `W`: `T ≥ 0`, `π` is continuous on
`[0, T]`, `π(0) = s`, `π(T) = t`, and every configuration `π(u)`, `u ∈ [0, T]`, is free. -/
def IsFeasiblePlan (W : Set (ℝ × ℝ)) {k : ℕ} (s t : Fin k → ℝ × ℝ) (T : ℝ)
    (π : ℝ → (Fin k → ℝ × ℝ)) : Prop :=
  0 ≤ T ∧ ContinuousOn π (Icc 0 T) ∧ π 0 = s ∧ π T = t ∧
    ∀ u ∈ Icc 0 T, IsFreeConfig W (π u)

/-- The pair `(s, t)` is *reachable* in `W`: some feasible `(s, t)`-plan exists. -/
def Reachable (W : Set (ℝ × ℝ)) {k : ℕ} (s t : Fin k → ℝ × ℝ) : Prop :=
  ∃ (T : ℝ) (π : ℝ → (Fin k → ℝ × ℝ)), IsFeasiblePlan W s t T π

end RobotMP.W1Hard


