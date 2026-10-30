-- Prove2me | Definitions.Def_GarberOLO_Alg3_Setting
-- name    : GarberOLO_Alg3_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:08.656954+00:00
-- url     : https://prove2.me/theorems/c25b379c-f166-4ee6-b0ed-f98cd39ae565
-- title:
--   Setting of online linear optimization with an approximation oracle (§2.1)
-- statement:
--   A **setting** in dimension $d$ consists of
--
--   1. compact sets $K, \mathcal F \subset \mathbb R^d_+$ (the feasible actions and the loss/payoff vectors),
--   2. real numbers $R, F, C > 0$ with $\|x\| \le R$ for all $x \in K$, $\|f\| \le F$ for all $f \in \mathcal F$, and $0 \le x \cdot f \le C$ for all $x \in K$, $f \in \mathcal F$,
--   3. an approximation parameter $\alpha > 0$.
--
--   Here $\|\cdot\|$ is the Euclidean norm and $x\cdot f$ the standard inner product. The value of $\alpha$ distinguishes loss minimization ($\alpha \ge 1$) from payoff maximization ($\alpha < 1$).
--
--   Every object of the mission (the oracle guarantee, the α-regret, Algorithms 2 and 3) is defined relative to a setting.
--
--   **Formalization Note** $R$ and $F$ are given upper bounds, not the maxima. $K$ need not be convex. Nonemptiness of $K$ is not a field: it follows from the existence of an oracle. The constant $C$ is kept although Theorem 1's proof does not use it.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, §2.1, p. 4 (unnumbered)

import Mathlib

open scoped RealInnerProductSpace

namespace GarberOLO.Alg3

/-- **The setting of online linear optimization with an approximation oracle** (§2.1).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, §2.1, p. 4 (unnumbered):
"Let K, F be compact sets of points in ℝᵈ₊ (non-negative orthant in ℝᵈ) such that
max_{x∈K} ‖x‖ ≤ R, max_{f∈F} ‖f‖ ≤ F, for some R > 0, F > 0 (throughout this work we let ‖·‖
denote the standard Euclidean norm), and for all x ∈ K, f ∈ F it holds that C ≥ x · f ≥ 0, for
some C > 0. We assume K is accessible through an approximated linear optimization oracle
O_K : ℝᵈ₊ → K with parameter α > 0".

A value `S : Setting d` collects the data: the feasible set `S.K` (the paper's K), the set of
loss/payoff vectors `S.Fset` (the paper's 𝓕), the bounds `S.R`, `S.F`, `S.Cb` (the paper's
R, F, C) and the oracle parameter `S.α`. Points of ℝᵈ are `EuclideanSpace ℝ (Fin d)`, whose
inner product `⟪x, y⟫` is the paper's x · y and whose norm is the Euclidean norm.

**Formalization Note.** R and F are given upper bounds on the norms (the page writes
"max ≤ R"), not the maxima themselves. K need not be convex. K is not assumed nonempty: every
theorem of the mission assumes an oracle (`IsApproxOracle`), whose value at `0 ∈ ℝᵈ₊` lies in
K. The constant C is kept although Theorem 1's proof does not use it. Nothing about the oracle
is bundled here; it is a separate hypothesis. -/
structure Setting (d : ℕ) where
  /-- The feasible set K ⊂ ℝᵈ₊. -/
  K : Set (EuclideanSpace ℝ (Fin d))
  /-- The set 𝓕 ⊂ ℝᵈ₊ of loss/payoff vectors. -/
  Fset : Set (EuclideanSpace ℝ (Fin d))
  /-- The bound R on the norms of points of K. -/
  R : ℝ
  /-- The bound F on the norms of vectors of 𝓕. -/
  F : ℝ
  /-- The bound C on the values x · f. -/
  Cb : ℝ
  /-- The approximation parameter α of the oracle. -/
  α : ℝ
  K_compact : IsCompact K
  Fset_compact : IsCompact Fset
  K_nonneg : ∀ x ∈ K, ∀ i, 0 ≤ x i
  Fset_nonneg : ∀ f ∈ Fset, ∀ i, 0 ≤ f i
  R_pos : 0 < R
  F_pos : 0 < F
  Cb_pos : 0 < Cb
  α_pos : 0 < α
  K_norm_le : ∀ x ∈ K, ‖x‖ ≤ R
  Fset_norm_le : ∀ f ∈ Fset, ‖f‖ ≤ F
  inner_nonneg : ∀ x ∈ K, ∀ f ∈ Fset, 0 ≤ ⟪x, f⟫
  inner_le : ∀ x ∈ K, ∀ f ∈ Fset, ⟪x, f⟫ ≤ Cb

end GarberOLO.Alg3


