-- Prove2me | Definitions.Def_ThomsonKS_Char_Setting
-- name    : ThomsonKS_Char_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:28.090028+00:00
-- url     : https://prove2.me/theorems/39ca3d16-ac14-4c29-86bd-a99350c3809f
-- title:
--   §2–§3, pp. 320–322 — division problems Σ^P and Σ̃^P, solutions, the Kalai–Smorodinsky solution, the axioms WPO, PO, An, S. Inv, Cont, Mon, and cch
-- statement:
--   This file sets up the variable-population framework of Thomson (1983) for the fair division of a fixed supply.
--
--   **Agents and groups.** The universe of potential agents is a countably infinite set; a group $P$ is a nonempty finite set of agents. For a group $P$, $\mathbb R^P$ is the space of vectors indexed by the members of $P$ and $\mathbb R^P_+$ its nonnegative orthant. Vector orders: $x > y$ means $x_i > y_i$ for every $i$; $x \geqq y$ means $x_i \ge y_i$ for every $i$; $x \geqslant y$ means $x \geqq y$ and $x \ne y$.
--
--   **Division problems.** $\Sigma^P$ is the class of sets $S \subseteq \mathbb R^P$ such that
--
--   1. (a) $S$ is a compact convex subset of $\mathbb R^P_+$ containing at least one strictly positive vector;
--   2. (b) $S$ is comprehensive: if $x \in S$, $y \in \mathbb R^P_+$ and $y \leqq x$, then $y \in S$.
--
--   $\tilde\Sigma^P \subseteq \Sigma^P$ consists of the problems that moreover satisfy (c): for all $x, y \in S$ with $y \geqslant x$ there is $z \in S$ with $z > x$.
--
--   **Solutions.** A solution $F = \{F^P\}$ assigns to each group $P$ and each $S \in \Sigma^P$ a point $F^P(S) \in S$.
--
--   **The Kalai–Smorodinsky solution.** For $S \in \Sigma^P$ the ideal point is $a(S)$ with $a_i(S) = \max_{x \in S} x_i$, and
--   $$K^P(S) = t^* a(S), \qquad t^* = \max\{t \ge 0 : t\,a(S) \in S\},$$
--   the largest point of $S$ on the segment from the origin to $a(S)$.
--
--   **Auxiliary operations.** For $P \subseteq Q$, a vector $x \in \mathbb R^P$ is extended by zeros to $\mathbb R^Q$; for $T \subseteq \mathbb R^Q$, the slice $T \cap \mathbb R^P$ is the set of $x \in \mathbb R^P$ whose zero-extension lies in $T$. For a bijection $\gamma : P \to P'$, the relabelled problem is $\{x' \in \mathbb R^{P'} : \exists x \in S,\ x'_{\gamma(i)} = x_i \ \forall i \in P\}$. For a vector $c$ with all $c_i > 0$, the scaling $\lambda$ is $\lambda_i(x) = c_i x_i$ and $\lambda(S)$ is the image of $S$. The convex and comprehensive hull $\mathrm{cch}\,A$ of $A \subseteq \mathbb R^P_+$ is the set of $y \in \mathbb R^P_+$ lying below some convex combination of points of $A$.
--
--   **Axioms** on a solution $F$ (each quantifies over problems in $\Sigma^P$ only):
--
--   1. WPO: for all $S \in \Sigma^P$ and $y \in \mathbb R^P_+$, if $y > F^P(S)$ then $y \notin S$.
--   2. PO: for all $S \in \Sigma^P$ and $y \in \mathbb R^P_+$, if $y \geqslant F^P(S)$ then $y \notin S$.
--   3. An: for all $P, P'$, every bijection $\gamma: P \to P'$, every $S \in \Sigma^P$ and $S' \in \Sigma^{P'}$ such that $S'$ is the relabelling of $S$ along $\gamma$, $F^{P'}_{\gamma(i)}(S') = F^P_i(S)$ for all $i \in P$.
--   4. S. Inv: $F^P(\lambda(S)) = \lambda(F^P(S))$ for every $S \in \Sigma^P$ and every positive scaling $\lambda$.
--   5. Cont: if $S^k, S \in \Sigma^P$ and $S^k \to S$ in the Hausdorff metric, then $F^P(S^k) \to F^P(S)$.
--   6. Mon: for $P \subseteq Q$, $S \in \Sigma^P$, $T \in \Sigma^Q$ with $S = T \cap \mathbb R^P$, $F^P_i(S) \ge F^Q_i(T)$ for all $i \in P$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Agents are natural numbers (the paper's $I = \{1, 2, \dots\}$, relabelled) and a group is a `Finset ℕ`. Groups are taken to be **nonempty**: `DivProb P` requires $P \ne \emptyset$, so $\Sigma^\emptyset$ is empty and every axiom and theorem concerns nonempty groups only. The page's $\mathcal P$ is literally "the class of finite subsets of $I$", but for $P = \emptyset$ the space $\mathbb R^\emptyset$ is a single point $p$, $\{p\}$ would satisfy (a) and (b), and WPO would fail for every solution there (the condition $p > F^\emptyset(\{p\})$ is vacuously true), so Theorem 1 and the characterization would be false; nonempty groups are the evident intent. $\mathbb R^P$ is the function type `P → ℝ`, whose Mathlib metric is the sup metric; Hausdorff convergence is stated with the extended Hausdorff distance `Metric.hausdorffEDist` (never the real-valued one, which is $0$ when the distance is infinite), and it coincides with Euclidean Hausdorff convergence since the norms are equivalent. A solution is a total function `Solution`; `IsSolution F` says $F^P(S) \in S$ for $S \in \Sigma^P$, and values off $\Sigma^P$ are irrelevant. The ideal point and $K$ use `sSup`; on $\Sigma^P$ both suprema are attained, so they are the paper's maxima. In comprehensiveness the page's "$x \geqslant y$" is encoded as $y \leqq x$, equivalent since $y = x$ is trivially in $S$. In An, the page's "one-to-one functions $\gamma$ from $P$ to $P'$ with $|P| = |P'|$" are encoded as bijections `P ≃ P'`, which forces $|P| = |P'|$; the page's set-builder "$\{x' \in \Sigma^{P'} \mid \dots\}$" is read as $x' \in \mathbb R^{P'}$ (a typo). The slice $T \cap \mathbb R^P$ uses zero-extension, as the page's "slight abuse of notation" intends.
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), pp. 320–322, §2 (conditions (a), (b), the Kalai–Smorodinsky solution), §3 (solutions; axioms WPO, PO, An, S. Inv., Cont, Mon; Other Notations: cch), condition (c) on p. 322. DOI 10.1287/moor.8.3.319

import Mathlib

namespace ThomsonKS.Char

open Filter Topology

/-- The class `Σ^P` of division problems for the finite group `P` of agents (§2–§3, p. 320):
(a) `S` is a compact convex subset of `R^P_+` containing a strictly positive vector, and
(b) `S` is comprehensive: if `x ∈ S`, `y ∈ R^P_+` and `y ≤ x` then `y ∈ S`.
Groups are nonempty: for `P = ∅` the space `R^P` is a point and WPO could hold for no solution,
so `Σ^∅` is taken to be empty. -/
def DivProb (P : Finset ℕ) : Set (Set (P → ℝ)) :=
  {S | P.Nonempty ∧ (∀ x ∈ S, ∀ i, 0 ≤ x i) ∧ IsCompact S ∧ Convex ℝ S ∧ (∃ x ∈ S, ∀ i, 0 < x i) ∧
    (∀ x ∈ S, ∀ y : P → ℝ, 0 ≤ y → y ≤ x → y ∈ S)}

/-- The class `Σ̃^P` (p. 322): the problems of `Σ^P` that also satisfy
(c) for all `x, y ∈ S`, if `y ⩾ x` (i.e. `x ≤ y`, `x ≠ y`) there is `z ∈ S` with `z > x`
(strictly larger in every coordinate). -/
def DivProbTilde (P : Finset ℕ) : Set (Set (P → ℝ)) :=
  {S | S ∈ DivProb P ∧
    ∀ x ∈ S, ∀ y ∈ S, (x ≤ y ∧ x ≠ y) → ∃ z ∈ S, ∀ i, x i < z i}

/-- A solution assigns to every finite group `P` and every set `S ⊆ R^P` a point of `R^P`.
Only its values on `Σ^P` are meaningful; see `IsSolution`. -/
def Solution : Type := (P : Finset ℕ) → Set (P → ℝ) → (P → ℝ)

/-- A solution selects a point of `S` for every `S ∈ Σ^P` (p. 320). -/
def IsSolution (F : Solution) : Prop :=
  ∀ P : Finset ℕ, ∀ S ∈ DivProb P, F P S ∈ S

/-- The ideal point `a(S)`, `a_i(S) = max_{x ∈ S} x_i` (p. 320). -/
noncomputable def idealPt {P : Finset ℕ} (S : Set (P → ℝ)) : P → ℝ :=
  fun i => sSup ((fun x : P → ℝ => x i) '' S)

/-- The Kalai–Smorodinsky solution `K` (p. 320): the largest point of `S` on the segment
from the origin to `a(S)`, i.e. `t* • a(S)` with `t* = max {t ≥ 0 | t • a(S) ∈ S}`. -/
noncomputable def KS : Solution :=
  fun _ S => sSup {t : ℝ | 0 ≤ t ∧ t • idealPt S ∈ S} • idealPt S

/-- Zero-extension of `x ∈ R^P` to `R^Q` for `P ⊆ Q`; used to read `T ∩ R^P` (p. 321). -/
def zeroExt {P Q : Finset ℕ} (h : P ⊆ Q) (x : P → ℝ) : Q → ℝ :=
  fun j => if hj : (j : ℕ) ∈ P then x ⟨j, hj⟩ else 0

/-- The relabelling of `S ⊆ R^P` along a bijection `γ : P ≃ P'` (axiom An, p. 320). -/
def relabel {P P' : Finset ℕ} (γ : P ≃ P') (S : Set (P → ℝ)) : Set (P' → ℝ) :=
  {x' | ∃ x ∈ S, ∀ i, x' (γ i) = x i}

/-- The coordinatewise scaling `λ(x)_i = c_i x_i` (the class `Λ^P`, p. 320). -/
def scale {P : Finset ℕ} (c : P → ℝ) (x : P → ℝ) : P → ℝ :=
  fun i => c i * x i

/-- The convex and comprehensive hull `cch A` of a subset `A` of `R^P_+` (p. 321): the points
of `R^P_+` lying below some convex combination of points of `A`. -/
def cch {P : Finset ℕ} (A : Set (P → ℝ)) : Set (P → ℝ) :=
  {y | 0 ≤ y ∧ ∃ z ∈ convexHull ℝ A, y ≤ z}

/-- Weak Pareto-optimality (WPO), p. 320. -/
def WPO (F : Solution) : Prop :=
  ∀ P : Finset ℕ, ∀ S ∈ DivProb P, ∀ y : P → ℝ, 0 ≤ y → (∀ i, F P S i < y i) → y ∉ S

/-- Pareto-optimality (PO), p. 320. -/
def PO (F : Solution) : Prop :=
  ∀ P : Finset ℕ, ∀ S ∈ DivProb P, ∀ y : P → ℝ, 0 ≤ y → (F P S ≤ y ∧ F P S ≠ y) → y ∉ S

/-- Anonymity (An), p. 320. -/
def An (F : Solution) : Prop :=
  ∀ P P' : Finset ℕ, ∀ γ : P ≃ P', ∀ S ∈ DivProb P, ∀ S' ∈ DivProb P',
    S' = relabel γ S → ∀ i, F P' S' (γ i) = F P S i

/-- Scale invariance (S. Inv.), p. 320. -/
def SInv (F : Solution) : Prop :=
  ∀ P : Finset ℕ, ∀ S ∈ DivProb P, ∀ c : P → ℝ, (∀ i, 0 < c i) →
    F P (scale c '' S) = scale c (F P S)

/-- Continuity (Cont) for Hausdorff convergence, p. 320. -/
def Cont (F : Solution) : Prop :=
  ∀ P : Finset ℕ, ∀ Sk : ℕ → Set (P → ℝ), ∀ S ∈ DivProb P, (∀ k, Sk k ∈ DivProb P) →
    Tendsto (fun k => Metric.hausdorffEDist (Sk k) S) atTop (𝓝 0) →
    Tendsto (fun k => F P (Sk k)) atTop (𝓝 (F P S))

/-- Monotonicity with respect to changes in the number of agents (Mon), p. 321. -/
def Mon (F : Solution) : Prop :=
  ∀ P Q : Finset ℕ, ∀ h : P ⊆ Q, ∀ S ∈ DivProb P, ∀ T ∈ DivProb Q,
    S = {x | zeroExt h x ∈ T} → ∀ i : P, F Q T ⟨i, h i.2⟩ ≤ F P S i

end ThomsonKS.Char


