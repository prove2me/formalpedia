-- Prove2me | Definitions.Def_StationarityTest_Geometry
-- name    : StationarityTest_Geometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:56.442231+00:00
-- url     : https://prove2.me/theorems/d395a819-6ad1-482f-94b8-ccfb6b34615a
-- title:
--   Interaction graphs, clause balls $B_H[x,r]$, $(d,D,c_{gr})$ Hamiltonians, $CC_{i,t}$ and $\mathrm{Grid}(\Lambda)$
-- statement:
--   Let $\Gamma\subseteq S^k_{[n]}$ be a set of clauses. Its **interaction graph** has vertex set $\Gamma$ and an edge between two distinct clauses whenever their site supports overlap. Write $\operatorname{dist}_\Gamma(\gamma_1,\gamma_2)$ for the graph distance, with value $\infty$ between disconnected clauses, and for a site $i$
--
--   $$\operatorname{dist}_\Gamma(i,\gamma)=\min_{\gamma_0\in\Gamma,\ \gamma_0\ni i}\operatorname{dist}_\Gamma(\gamma_0,\gamma),$$
--
--   which is $\infty$ if no clause contains $i$. For $x\in[n]\cup\Gamma$ and $r\ge0$ the **clause ball** is $B[x,r]=\{\gamma\in\Gamma:\operatorname{dist}_\Gamma(x,\gamma)\le r\}$.
--
--   $\Gamma$ is the clause set of a **$(d,D,c_{gr})$ Hamiltonian** if:
--
--   1. every clause of $\Gamma$ overlaps at most $d$ clauses of $\Gamma$, itself included;
--   2. $|B[x,r]|\le c_{gr}\,r^D$ for every $x\in[n]\cup\Gamma$ and every $r\ge1$.
--
--   A set $\Lambda$ is **$t$-connected** to a site $i$ ($\Lambda\in CC_{i,t}$) if every $e\in\Lambda$ is joined to a clause of $\Lambda$ containing $i$ by a path of overlapping clauses inside $\Lambda$ of length at most $t$. The empty set belongs to $CC_{i,t}$. For a grid spacing $\kappa$,
--
--   $$\mathrm{Grid}(\Lambda)=\Big\{U=\sum_{P\in\Lambda}u_PP:\ u_P\in\kappa\mathbb Z\cap[-1,1]\Big\}.$$
--
--   Finally $e^{-\theta\cdot\infty}=0$.
--
--   These encode the lattice geometry that the structure learning algorithm must preserve.
--
--   **Formalization Note** Distances are `SimpleGraph.edist` in $\mathbb N\cup\{\infty\}$. `SimpleGraph.dist` would give the junk value $0$ between disconnected clauses. Radii are natural numbers: a real radius $r$ gives the ball of $\lfloor r\rfloor$, so the growth bound at integers implies it at reals. The path length in $CC_{i,t}$ counts edges. The ranges $d,D\ge1$, $c_{gr}\ge1$ of Definition 2.2 are hypotheses of the statements.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Definitions 2.1–2.2, (22)–(23), p.14; Definition 5.2 and (102), p.28; (246), p.58

import Definitions.Def_StationarityTest_Pauli

namespace StationarityTest

/-!
# Interaction graphs, balls, `(d, D, c_gr)` Hamiltonians, connected clause sets and grids

T. Bergamaschi, *The stationarity test*, arXiv:2610.01074 (held file sha256 0b7e46fb…),
Definitions 2.1–2.2, (22)–(23), p.14; Definition 5.2 and (102), p.28; (246), p.58.

**Formalization Note.** The interaction graph of a clause set `Γ` (Definition 2.1) is a
`SimpleGraph` on all `k`-local strings whose edges join two distinct members of `Γ` with
overlapping site supports, so every path runs inside `Γ`. Distances are `SimpleGraph.edist`
(`ℕ∞`, equal to `⊤` between disconnected clauses; `SimpleGraph.dist` would return the junk value
`0`). `dist_Γ(i, γ) = min_{γ₀ ∋ i} dist_Γ(γ₀, γ)` is an infimum in `ℕ∞` (`⊤` if no clause of `Γ`
contains `i`). Balls have integer radii: the paper's `r ≥ 0` real gives the same ball as `⌊r⌋`,
and the growth bound for integers `r ≥ 1` implies it for real `r ≥ 1`. "Maximum degree at most
`d` (including self-edges)" counts, for every clause, the clauses of `Γ` overlapping it, itself
included. The ranges `d, D ≥ 1`, `c_gr ≥ 1` of Definition 2.2 are hypotheses of the statements.
-/

variable {n q k : ℕ}

/-- Two clauses overlap: their site supports intersect. -/
def Overlap (γ₁ γ₂ : KLocal n q k) : Prop :=
  ¬ Disjoint (siteSupport γ₁.1) (siteSupport γ₂.1)

instance : DecidableRel (Overlap (n := n) (q := q) (k := k)) := fun _ _ => by
  unfold Overlap; infer_instance

/-- Definition 2.1: the interaction graph `G_H = (Γ, E)` of the clause set `Γ`, edges between
distinct overlapping clauses of `Γ` (as a graph on all clauses, the non-members isolated). -/
def interactionGraph (Γ : Finset (KLocal n q k)) : SimpleGraph (KLocal n q k) :=
  SimpleGraph.fromRel fun γ₁ γ₂ => γ₁ ∈ Γ ∧ γ₂ ∈ Γ ∧ Overlap γ₁ γ₂

/-- Definition 2.1: `dist_Γ(γ₁, γ₂)`, the graph distance in the interaction graph (`⊤` if not
connected). -/
noncomputable def clauseDist (Γ : Finset (KLocal n q k)) (γ₁ γ₂ : KLocal n q k) : ℕ∞ :=
  (interactionGraph Γ).edist γ₁ γ₂

/-- Definition 2.1: `dist_Γ(i, γ) := min_{γ₀ ∋ i} dist_Γ(γ₀, γ)`, over the clauses `γ₀ ∈ Γ`
containing site `i`. -/
noncomputable def siteDist (Γ : Finset (KLocal n q k)) (i : Fin n) (γ : KLocal n q k) : ℕ∞ :=
  ⨅ γ₀ ∈ Γ, ⨅ (_ : i ∈ siteSupport γ₀.1), clauseDist Γ γ₀ γ

/-- The distance from a point `x ∈ [n] ∪ Γ` (a site `Sum.inl i` or a clause `Sum.inr γ₀`) to a
clause `γ`. -/
noncomputable def pointDist (Γ : Finset (KLocal n q k)) :
    Fin n ⊕ KLocal n q k → KLocal n q k → ℕ∞
  | Sum.inl i, γ => siteDist Γ i γ
  | Sum.inr γ₀, γ => clauseDist Γ γ₀ γ

/-- (22): the clause ball `B_H[x, r] := {γ ∈ Γ : dist_Γ(x, γ) ≤ r}`. -/
noncomputable def clauseBall (Γ : Finset (KLocal n q k)) (x : Fin n ⊕ KLocal n q k) (r : ℕ) :
    Finset (KLocal n q k) :=
  open Classical in Γ.filter fun γ => pointDist Γ x γ ≤ r

/-- Definition 2.2: the interaction graph of `Γ` has maximum degree at most `d`, self-edges
included: every clause of `Γ` overlaps at most `d` clauses of `Γ`, itself counted. -/
def DegreeLe (Γ : Finset (KLocal n q k)) (d : ℕ) : Prop :=
  ∀ γ ∈ Γ, (Γ.filter fun γ' => Overlap γ γ').card ≤ d

/-- Definition 2.2, (23): `Γ` is the clause set of a `(d, D, c_gr)` Hamiltonian: degree at most
`d` (self-edges included) and `|B[x, r]| ≤ c_gr · r^D` for every `x ∈ [n] ∪ Γ` and every `r ≥ 1`. -/
def IsDDcgr (d D : ℕ) (cgr : ℝ) (Γ : Finset (KLocal n q k)) : Prop :=
  DegreeLe Γ d ∧
    (∀ i : Fin n, ∀ r : ℕ, 1 ≤ r →
      ((clauseBall Γ (Sum.inl i) r).card : ℝ) ≤ cgr * (r : ℝ) ^ D) ∧
    (∀ γ ∈ Γ, ∀ r : ℕ, 1 ≤ r →
      ((clauseBall Γ (Sum.inr γ) r).card : ℝ) ≤ cgr * (r : ℝ) ^ D)

/-- Definition 5.2: `Λ ⊆ S^k_[n]` is `t`-connected to site `i`: every `e ∈ Λ` is reached from a
clause of `Λ` containing `i` by a path of overlapping clauses within `Λ` of length (number of
edges) at most `t`. `CC_{i,t}` is the set of such `Λ`; `Λ = ∅` belongs to it. -/
def IsTConnected (Λ : Finset (KLocal n q k)) (i : Fin n) (t : ℕ) : Prop :=
  ∀ e ∈ Λ, siteDist Λ i e ≤ t

/-- (102): `Grid(Λ)`, the coefficient vectors `U = Σ_{P∈Λ} u_P P` with `u_P ∈ κℤ ∩ [−1, 1]`
(coefficients outside `Λ` are `0`). -/
def gridSet (κ : ℝ) (Λ : Finset (KLocal n q k)) : Set (KLocal n q k → ℝ) :=
  {u | (∀ P, P ∉ Λ → u P = 0) ∧ ∀ P ∈ Λ, (∃ z : ℤ, u P = κ * z) ∧ |u P| ≤ 1}

/-- `e^{−θ·x}` for an extended distance `x ∈ ℕ∞`, with `e^{−θ·∞} = 0` (246). -/
noncomputable def expDecay (θ : ℝ) (x : ℕ∞) : ℝ :=
  if x = ⊤ then 0 else Real.exp (-θ * (x.toNat : ℝ))

end StationarityTest


