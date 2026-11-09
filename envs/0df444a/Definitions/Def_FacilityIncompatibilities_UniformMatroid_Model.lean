-- Prove2me | Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model
-- name    : FacilityIncompatibilities_UniformMatroid_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:54.997159+00:00
-- url     : https://prove2.me/theorems/306cefe6-dc37-440a-adf4-9a9079587f88
-- title:
--   Definition 1 and §2.1 — FL-MI instances, feasible assignments, A(X), opening cost, OPT and local optimality
-- statement:
--   An instance of **Facility Location with Matroid-based Incompatibilities (FL-MI)** consists of a finite set of clients $V_C$, a finite set of facilities $V_F$, distances $d(x,y)$ for $x,y\in V_C\cup V_F$, opening costs $f_i$ for $i\in V_F$, and one matroid $\mathcal M=(V_C,\mathcal I)$ on the clients. The **standing assumptions** are that $d$ is a (pseudo)metric, $f_i\ge 0$, and the ground set of $\mathcal M$ is exactly $V_C$.
--
--   For $X\subseteq V_F$, an assignment $\sigma:V_C\to X$ is **feasible** if every fiber $\sigma^{-1}(i)$, $i\in X$, is independent in $\mathcal M$; $X$ is **feasible** if it admits a feasible assignment. The connection cost of $\sigma$ is $\sum_{j\in V_C}d(j,\sigma(j))$ and
--
--   $$A(X)=\min\Big\{\sum_{j\in V_C}d(j,\sigma(j)) : \sigma:V_C\to X\text{ feasible}\Big\},\qquad A(X)=\infty\text{ if }X\text{ is infeasible}.$$
--
--   The opening cost is $F(X)=\sum_{i\in X}f_i$, $\mathrm{cost}(X)=F(X)+A(X)$, and $\mathrm{OPT}=\min_{X\subseteq V_F}\mathrm{cost}(X)$, the minimum objective $\sum_{i\in X}f_i+\sum_j d(j,\sigma(j))$ over all feasible solutions $(X,\sigma)$.
--
--   Opening costs are **uniform** if all $f_i$ are equal. A feasible $S$ is **locally optimal** (a local minimum for the add/delete neighbourhood of §1.2) if $\mathrm{cost}(S)\le\mathrm{cost}(S\cup\{i\})$ for every $i\notin S$ and $\mathrm{cost}(S)\le\mathrm{cost}(S\setminus\{s\})$ for every $s\in S$ with $S\setminus\{s\}$ feasible; the two halves are named separately (add- and delete-local optimality). A minimum-cost feasible assignment to $X$ is the $\sigma_S$, $\sigma_O$ of §2.1. Finally $\max_{I\in\mathcal I}\sum_{j\in I}z_j$ denotes the largest weight of an independent set under real weights $z$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Clients and facilities are types `C`, `F` (finite in every statement), distances one function on `C ⊕ F`, facility sets `Finset F`. $A$, $\mathrm{cost}$ and $\mathrm{OPT}$ take values in $\mathbb R_{\ge0}\cup\{\infty\}$ (`ℝ≥0∞`), so infeasibility is $\infty$ and never a junk $0$. The metric is a pseudometric (co-location allowed). The maximum-weight independent set value is a supremum over the finite nonempty type of independent finite sets, hence attained.
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Definition 1, printed p.1 / PDF p.2; standing assumptions printed p.2 / PDF p.3; local search §1.2, printed p.3 / PDF p.4; notation §2.1, printed p.5 / PDF p.6

import Mathlib

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid

/-- **Facility Location with Matroid-based Incompatibilities (FL-MI)**, data of an instance.
Wu–Friggstad, *Facility Location with Customer Incompatibilities*, STOC 2027 submission #664
(October 2026), Definition 1, printed p.1 / PDF p.2.

* clients `C` and facilities `F` (finite types in every statement);
* `d`, the distances between all points of the disjoint union `C ⊕ F`
  (clients `Sum.inl j`, facilities `Sum.inr i`);
* `f i`, the opening cost of facility `i`;
* `M`, the single matroid on the clients describing which client sets one facility may serve.

The standing assumptions (metric distances, `f ≥ 0`, matroid on exactly the clients) are the
separate predicate `Instance.Valid`. -/
structure Instance (C F : Type*) where
  /-- distances on `C ⊕ F` -/
  d : C ⊕ F → C ⊕ F → ℝ
  /-- opening costs -/
  f : F → ℝ
  /-- the common client matroid -/
  M : Matroid C

/-- The largest weight `max_{I ∈ ℐ} ∑_{j ∈ I} z_j` of an independent set of the matroid `M`
under the real weights `z` (the inner maximum of (2), printed p.6, and the left side of (5),
printed p.7).

**Formalization Note** The supremum ranges over the finite, nonempty (it contains `∅`) type of
independent finite sets, so it is attained: it is the maximum, not a junk value. -/
noncomputable def matroidMaxWeight {C : Type*} (M : Matroid C) (z : C → ℝ) : ℝ :=
  ⨆ T : {T : Finset C // M.Indep (T : Set C)}, ∑ j ∈ T.1, z j

namespace Instance

variable {C F : Type*} (I : Instance C F)

/-- **Standing assumptions** of the paper (Definition 1, printed p.1 / PDF p.2): `d` is a
(pseudo)metric on `V_C ∪ V_F` (`d(x,x) = 0`, symmetry, triangle inequality), every opening cost is
nonnegative, and the matroid `M = (V_C, ℐ)` has exactly the clients as ground set.

**Formalization Note** A pseudometric: distinct points may be at distance `0` (co-located
facilities and clients); every metric instance is covered. Nonnegativity of `d` follows from
the three axioms. Feasibility of `V_F` is not part of this predicate; it is a hypothesis where
the paper needs it. -/
structure Valid : Prop where
  d_self : ∀ x, I.d x x = 0
  d_comm : ∀ x y, I.d x y = I.d y x
  d_triangle : ∀ x y z, I.d x z ≤ I.d x y + I.d y z
  f_nonneg : ∀ i, 0 ≤ I.f i
  ground : I.M.E = Set.univ

/-- Client–facility distance `d(j, i)`. -/
def dist (j : C) (i : F) : ℝ := I.d (Sum.inl j) (Sum.inr i)

/-- Facility–facility distance `d(i, i')`. -/
def fdist (i i' : F) : ℝ := I.d (Sum.inr i) (Sum.inr i')

/-- **Feasible assignment** (Definition 1): `σ : V_C → X` (every client goes to a facility of
`X`) such that every fiber `σ⁻¹(i)`, `i ∈ X`, is independent in `M`. -/
def IsFeasibleAssignment (X : Finset F) (σ : C → F) : Prop :=
  (∀ j, σ j ∈ X) ∧ ∀ i ∈ X, I.M.Indep (σ ⁻¹' {i})

/-- **Feasible facility set** (Definition 1): `X` admits a feasible assignment. -/
def IsFeasible (X : Finset F) : Prop := ∃ σ, I.IsFeasibleAssignment X σ

/-- The connection cost `∑_{j ∈ V_C} d(j, σ(j))` of an assignment. -/
def connCost [Fintype C] (σ : C → F) : ℝ := ∑ j, I.dist j (σ j)

/-- **`A(X)`** (§1.2, printed p.4, and §2.1, printed p.5): the minimum connection cost of a
feasible assignment to `X`, with `A(X) = ∞` if `X` is not feasible.

**Formalization Note** Valued in `ℝ≥0∞`; the infimum over the empty set of feasible
assignments is `⊤ = ∞`, exactly the paper's convention. Distances are nonnegative under `Valid`,
so `ENNReal.ofReal` loses nothing. -/
noncomputable def A [Fintype C] (X : Finset F) : ℝ≥0∞ :=
  ⨅ (σ : C → F) (_ : I.IsFeasibleAssignment X σ), ENNReal.ofReal (I.connCost σ)

/-- The opening cost `F(X) = ∑_{i ∈ X} f_i`. -/
def openCost (X : Finset F) : ℝ := ∑ i ∈ X, I.f i

/-- `cost(X) = F(X) + A(X)`, the objective of the local search (§1.2), `∞` on infeasible sets. -/
noncomputable def cost [Fintype C] (X : Finset F) : ℝ≥0∞ := ENNReal.ofReal (I.openCost X) + I.A X

/-- The objective `∑_{i ∈ X} f_i + ∑_j d(j, σ(j))` of a solution `(X, σ)` (Definition 1). -/
def solCost [Fintype C] (X : Finset F) (σ : C → F) : ℝ := I.openCost X + I.connCost σ

/-- **`OPT`**: the minimum of `F(X) + A(X)` over all facility sets, i.e. the minimum objective over
all feasible solutions; `∞` if there is none. -/
noncomputable def OPT [Fintype C] [Fintype F] : ℝ≥0∞ := ⨅ X : Finset F, I.cost X

/-- `σ` is a minimum-cost feasible assignment to `X` (the assignments `σ_S`, `σ_O` of §2.1). -/
def IsOptAssignment [Fintype C] (X : Finset F) (σ : C → F) : Prop :=
  I.IsFeasibleAssignment X σ ∧
    ∀ σ', I.IsFeasibleAssignment X σ' → I.connCost σ ≤ I.connCost σ'

/-- **Uniform opening costs** (§1, printed p.2): all `f_i`, `i ∈ V_F`, are the same value. -/
def IsUniform : Prop := ∀ i i', I.f i = I.f i'

/-- `S` is feasible and no `add(i)` move, `i ∉ S`, strictly lowers `cost` (§1.2, printed p.3). -/
def IsAddLocalOpt [Fintype C] [DecidableEq F] (S : Finset F) : Prop :=
  I.IsFeasible S ∧ ∀ i ∉ S, I.cost S ≤ I.cost (insert i S)

/-- `S` is feasible and no feasible `delete(s)` move, `s ∈ S`, strictly lowers `cost`
(§1.2, printed p.3: "provided the resulting facility set is feasible"). -/
def IsDeleteLocalOpt [Fintype C] [DecidableEq F] (S : Finset F) : Prop :=
  I.IsFeasible S ∧ ∀ s ∈ S, I.IsFeasible (S.erase s) → I.cost S ≤ I.cost (S.erase s)

/-- **Local minimum** for the uniform-opening-cost neighbourhood (§1.2, printed p.3): `S` is
feasible and every `S' ∈ N(S)`, `N(S)` the feasible sets reached by one add or one delete move,
has `cost(S') ≥ cost(S)`. -/
def IsLocalOpt [Fintype C] [DecidableEq F] (S : Finset F) : Prop :=
  I.IsAddLocalOpt S ∧ I.IsDeleteLocalOpt S

end Instance

end FacilityIncompatibilities.UniformMatroid


