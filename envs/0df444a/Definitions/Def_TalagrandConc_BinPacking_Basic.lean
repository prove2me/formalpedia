-- Prove2me | Definitions.Def_TalagrandConc_BinPacking_Basic
-- name    : TalagrandConc_BinPacking_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:04.439855+00:00
-- url     : https://prove2.me/theorems/cbc6c744-cf6d-4119-ad7f-73ed31cfe45b
-- title:
--   Bin packing number $B_N$, $\|x\|_2$, the level sets $A(a)$, $f_c(A,x)$ under the name of Chapter 6, $\mathbb E X_1^2$ and the median
-- statement:
--   Throughout, $\Omega = [0,1]$ and $N \ge 0$; a point $x = (x_1,\dots,x_N) \in \Omega^N$ is a list of **items**, item $i$ having size $x_i$.
--
--   1. A **packing** of $x$ into $k$ unit bins is a map $\sigma : \{1,\dots,N\} \to \{1,\dots,k\}$ such that for every bin $j$
--   $$\sum_{i : \sigma(i) = j} x_i \le 1 .$$
--   2. The **bin packing number** $B_N(x) = B_N(x_1,\dots,x_N)$ is the minimum number $k$ of unit bins into which the items can be packed. It is well defined since $N$ bins always suffice (one item per bin); $B_N = 0$ when $N = 0$.
--   3. The Euclidean norm $\|x\|_2 = \big(\sum_{i\le N} x_i^2\big)^{1/2}$.
--   4. For a real $a$, the level set $A(a) = \{y \in \Omega^N : B_N(y) \le a\}$.
--   5. For a set $A \subseteq \Omega^N$ and $x \in \Omega^N$, $f_c(A,x)$ is the **convex hull distance** of Section 4.1: the $\ell^2$-distance from $0$ to the convex hull $V_A(x)$ of
--   $$U_A(x) = \{ s \in \{0,1\}^N : \exists y \in A,\ s_i = 0 \Rightarrow x_i = y_i \},$$
--   that is $f_c(A,x) = \inf\{ (\sum_i s_i^2)^{1/2} : s \in V_A(x) \} \in [0,+\infty]$. It equals $+\infty$ when $A = \emptyset$ and $0$ when $x \in A$. This module does not redefine it: it is the shared definition of Section 4.1, re-exported under the name used in Chapter 6.
--   6. For a probability measure $\mu$ on $[0,1]$ (the common law of the items), $\mathbb E X_1^2 = \int_0^1 \omega^2 \, d\mu(\omega)$.
--   7. A real number $M$ is a **median** of a function $Z$ under a measure $P$ if $P(Z \le M) \ge 1/2$ and $P(Z \ge M) \ge 1/2$.
--
--   These are the objects of Talagrand's Chapter 6, where the fluctuations of the random variable $B_N(X_1,\dots,X_N)$ for i.i.d. items are controlled through the convex hull distance of Section 4.1.
--
--   **Formalization Note** $\Omega = [0,1]$ is Mathlib's `unitInterval`; coordinates are indexed by `Fin N` (0-based). $B_N$ is an `sInf` in `ℕ` over a nonempty set, hence a true minimum. `convexDist` is by definition `TalagrandConc.ConvexHull.fc` (imported), valued in `ℝ≥0∞` with the Euclidean norm written out (Mathlib's default norm on `Fin N → ℝ` is the sup norm). The median is not defined in the paper; the definition above is the standard one.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 151, Section 6 (B_N, ‖x‖₂, A(a)); p. 123, Section 4.1 (f_c(A,x))

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.BinPacking

open MeasureTheory
open scoped ENNReal

/-- Talagrand (1995), p. 151: an assignment of the items `x₁, …, x_N` (sizes in `[0, 1]`) to
`k` unit bins such that the sum of the sizes of the items attributed to each bin is at most one. -/
def IsPacking {N : ℕ} (x : Fin N → unitInterval) (k : ℕ) : Prop :=
  ∃ σ : Fin N → Fin k, ∀ j : Fin k,
    ∑ i ∈ Finset.univ.filter (fun i => σ i = j), (x i : ℝ) ≤ 1

/-- Talagrand (1995), p. 151: `B_N(x₁, …, x_N)`, the **minimum** number of unit bins in which the
items can be packed. The set of admissible `k` is nonempty (`k = N`, one item per bin), so the
`sInf` in `ℕ` is attained; for `N = 0` it is `0`. -/
noncomputable def binNumber {N : ℕ} (x : Fin N → unitInterval) : ℕ :=
  sInf {k : ℕ | IsPacking x k}

/-- Talagrand (1995), p. 151: `‖x‖₂ = (∑_{i ≤ N} x_i²)^{1/2}` (Euclidean norm). -/
noncomputable def l2Norm {N : ℕ} (x : Fin N → unitInterval) : ℝ :=
  Real.sqrt (∑ i, (x i : ℝ) ^ 2)

/-- Talagrand (1995), p. 151: `A(a) = {y ∈ Ω^N ; B_N(y) ≤ a}` (the paper uses it for `a > 0`). -/
def levelSet (N : ℕ) (a : ℝ) : Set (Fin N → unitInterval) :=
  {y | (binNumber y : ℝ) ≤ a}

/-- Talagrand (1995), p. 123: `f_c(A, x)`, the `ℓ²`-distance from zero to `V_A(x)`,
`inf { (∑_i s_i²)^{1/2} ; s ∈ V_A(x) }`, valued in `ℝ≥0∞` (it is `⊤ = +∞` when `A = ∅`).
This is the shared definition `TalagrandConc.ConvexHull.fc` of Section 4.1, under the name used
in Chapter 6. -/
noncomputable def convexDist {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) :
    ℝ≥0∞ :=
  TalagrandConc.ConvexHull.fc A x

/-- `E X₁² = ∫ ω² dμ(ω)` for the common law `μ` of the items on `Ω = [0, 1]`. -/
noncomputable def secondMoment (μ : Measure unitInterval) : ℝ :=
  ∫ ω, (ω : ℝ) ^ 2 ∂μ

/-- `M` is a median of the real function `Z` under `P`:
`P(Z ≤ M) ≥ 1/2` and `P(Z ≥ M) ≥ 1/2`. -/
def IsMedian {α : Type*} [MeasurableSpace α] (P : Measure α) (Z : α → ℝ) (M : ℝ) : Prop :=
  (1 / 2 : ℝ≥0∞) ≤ P {x | Z x ≤ M} ∧ (1 / 2 : ℝ≥0∞) ≤ P {x | M ≤ Z x}

end TalagrandConc.BinPacking


