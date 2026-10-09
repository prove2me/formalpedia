-- Prove2me | Definitions.Def_OnlineCRS_Submod_Model
-- name    : OnlineCRS_Submod_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:05.720406+00:00
-- url     : https://prove2.me/theorems/81be5c32-6047-4306-91cf-1e6930c722cf
-- title:
--   §1.1 and Theorem 1.10 — relaxations, arrival orders, the greedy run, and E[f(S)], E[f(S(1/2))] against the almighty adversary
-- statement:
--   Let $N$ be a finite ground set and $\mathbf 1_I\in\{0,1\}^N$ the characteristic vector of $I\subseteq N$.
--
--   1. **Relaxation.** A down-closed feasible family $\mathcal F\subseteq 2^N$ and a polytope $P\subseteq[0,1]^N$ form a *relaxation* if $P$ and $P_{\mathcal F}=\operatorname{conv}\{\mathbf 1_I : I\in\mathcal F\}$ contain the same $\{0,1\}$-points, i.e. $\mathbf 1_I\in P \iff I\in\mathcal F$ for every $I\subseteq N$.
--   The polytope condition means $P$ is the convex hull of finitely many vectors.
--
--   2. **Orders.** An arrival order is a list of the elements of $N$ in which every element appears exactly once.
--   3. **Greedy run.** Given a family $\mathcal F_x$, an active set $A$ and an order $\sigma$, the greedy OCRS processes the elements in the order $\sigma$ and selects an arriving element $e$ iff $e\in A$ and $S\cup\{e\}\in\mathcal F_x$, where $S$ is the set selected so far. The output is the final selected set.
--   4. **Expected value against the almighty adversary.** For a randomized greedy OCRS with family distribution $w_x$, a set function $f$ and an adversary $\mathrm{ord}$ choosing the order $\mathrm{ord}(\mathcal F_x, A)$ after seeing both random outcomes,
--   $$\mathbb E[f(S)]=\sum_{\mathcal F_x} w_x(\mathcal F_x)\sum_{A\subseteq N}\Pr[R(x)=A]\, f\big(\mathrm{run}(\mathcal F_x,A,\mathrm{ord}(\mathcal F_x,A))\big).$$
--   5. **The set $S(1/2)$.** Let $C\subseteq N$ be a uniformly random set (each element independently with probability $1/2$), independent of $\mathcal F_x$ and $R(x)$, and $S(1/2)=S\cap C$. The coins are part of the algorithm and known to the adversary, whose order $\mathrm{ord}(\mathcal F_x,A,C)$ may depend on them:
--   $$\mathbb E[f(S(1/2))]=\sum_{\mathcal F_x} w_x(\mathcal F_x)\sum_{A}\Pr[R(x)=A]\sum_{C}2^{-|N|}\, f\big(\mathrm{run}(\mathcal F_x,A,\mathrm{ord}(\mathcal F_x,A,C))\cap C\big).$$
--
--   These objects make the statement of Theorem 1.10 precise: the guarantee holds against an adversary that knows every random outcome before fixing the order.
--
--   **Formalization Note** The almighty adversary is a function from the realized randomness (the family, the active set, and in the second case the coins) to orders; this is the strongest adversary the paper considers. The uniform coin weight is written as the product weight with all coordinates $1/2$.
-- source:
--   arXiv:1508.00142v2, §1.1 and Definition 1.1, p. 2; Definition 1.3 and the almighty adversary, p. 3; Theorem 1.10, p. 5 and its restatement with S(p), p. 16

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics

namespace OnlineCRS.Submod

/-- The characteristic vector `1_I ∈ {0,1}^N` of a set `I ⊆ N` (arXiv:1508.00142v2, §1.1, p. 2). -/
def indicatorVec {α : Type} [DecidableEq α] (I : Finset α) : α → ℝ :=
  fun e => if e ∈ I then 1 else 0

/-- A polytope in the finite-dimensional vector space of real vectors on `α` is the convex hull
of finitely many points. The paper assumes this for every relaxation `P` (§1.1, p. 2). -/
def IsPolytope {α : Type} (P : Set (α → ℝ)) : Prop :=
  ∃ V : Finset (α → ℝ), P = convexHull ℝ (V : Set (α → ℝ))

/-- §1.1 and Definition 1.1 (p. 2), the standing setting of Definition 1.3 (p. 3): the feasible family `𝓕`
is down-closed, and `P ⊆ [0,1]^N` has the integer points of `P_𝓕 = conv{1_I | I ∈ 𝓕}`, i.e. `P` and `P_𝓕`
contain the same `{0,1}`-points. Since the only `{0,1}`-points of `P_𝓕` are the vectors `1_I` with
`I ∈ 𝓕`, this says `1_I ∈ P ↔ I ∈ 𝓕` for every `I ⊆ N`. Polytope status is carried
separately by `IsPolytope` in each theorem that assumes a relaxation. -/
def IsRelaxation {α : Type} [DecidableEq α] (𝓕 : Finset α → Prop) (P : Set (α → ℝ)) : Prop :=
  (∀ I J : Finset α, J ⊆ I → 𝓕 I → 𝓕 J) ∧
    (∀ y ∈ P, ∀ e : α, 0 ≤ y e ∧ y e ≤ 1) ∧
    ∀ I : Finset α, indicatorVec I ∈ P ↔ 𝓕 I

/-- An order in which the adversary reveals the elements of `N` (§1.1, p. 3): a list containing every
element of `N` exactly once. -/
def IsOrder {α : Type} (σ : List α) : Prop :=
  σ.Nodup ∧ ∀ e : α, e ∈ σ

/-- Definition 1.3 (p. 3): the run of a greedy OCRS with family `Fam` when the active set is `A` and the
elements are revealed in the order `σ`. An arriving element `e` is selected iff it is active and, together
with the already selected elements, the obtained set is in `Fam`. The value is the selected set. -/
def greedyRun {α : Type} [DecidableEq α] (Fam : Finset (Finset α)) (A : Finset α) (σ : List α) :
    Finset α :=
  σ.foldl (fun S e => if e ∈ A ∧ insert e S ∈ Fam then insert e S else S) ∅

/-- Theorem 1.10, first part (pp. 5, 16): `E[f(S)]` for the set `S` selected by the randomized greedy
OCRS `w` on input `x` against the almighty adversary `ord`. The family `F_x` is drawn from `w x`, the
active set `A` from `R(x)` independently, and the adversary, who knows both, reveals the elements in the
order `ord F_x A`. -/
noncomputable def expOutput {α : Type} [Fintype α] [DecidableEq α]
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (x : α → ℝ)
    (ord : Finset (Finset α) → Finset α → List α) (f : Finset α → ℝ) : ℝ :=
  ∑ Fam : Finset (Finset α), w x Fam *
    ∑ A : Finset α, OnlineCRS.Matroid.activeProb x A * f (greedyRun Fam A (ord Fam A))

/-- Theorem 1.10, second part (pp. 5, 16): `E[f(S(1/2))]`, where `S(1/2)` keeps every element of the
selected set `S` independently with probability `1/2`. The coins are a uniform random set `C ⊆ N`
(each element with probability `1/2`, independent of `F_x` and of `R(x)`), and `S(1/2) = S ∩ C`. The
coins are part of the algorithm and known to the almighty adversary, so the order `ord F_x A C` may
depend on them as well. -/
noncomputable def expOutputHalf {α : Type} [Fintype α] [DecidableEq α]
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (x : α → ℝ)
    (ord : Finset (Finset α) → Finset α → Finset α → List α) (f : Finset α → ℝ) : ℝ :=
  ∑ Fam : Finset (Finset α), w x Fam *
    ∑ A : Finset α, OnlineCRS.Matroid.activeProb x A *
      ∑ C : Finset α, OnlineCRS.Matroid.activeProb (fun _ => (1 / 2 : ℝ)) C * f (greedyRun Fam A (ord Fam A C) ∩ C)

end OnlineCRS.Submod


