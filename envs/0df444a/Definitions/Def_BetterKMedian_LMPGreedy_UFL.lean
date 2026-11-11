-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_UFL
-- name    : BetterKMedian_LMPGreedy_UFL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:12.342698+00:00
-- url     : https://prove2.me/theorems/6a2b3aa3-c3c1-4b7b-b530-e2ae340a211a
-- title:
--   §2, Definition 2.1 — uncapacitated facility location with uniform opening cost, $\mathrm{OPT}_f$ and the $\rho$-LMP guarantee
-- statement:
--   An **instance** has $N$ points `Fin N`, a real **pseudometric** $d$ on them (nonnegative, symmetric, $d(x,x)=0$, triangle inequality; distinct points may be at distance $0$), a set $D$ of **clients** and a set $F$ of **facilities** (finite sets of points, possibly overlapping), and a **uniform opening cost** $f\ge0$; there is a facility whenever there is a client.
--
--   For $S\subseteq F$ nonempty, $d(j,S)=\min_{i\in S}d(i,j)$ (`distToSet`). The connection cost is $\mathrm{cost}(S)=\sum_{j\in D}d(j,S)$ and $\mathrm{cost}_f(S)=\mathrm{cost}(S)+f\,|S|$. A **solution** (`IsFeasible`) is $S\subseteq F$ that is nonempty when $D\ne\emptyset$; this encodes the paper's convention $d(j,\emptyset)=+\infty$ (the value `distToSet ∅ j = 0` is never used by a solution of an instance with clients). $\mathrm{OPT}_f$ (`OPT`) is the minimum of $\mathrm{cost}_f$ over the finite, nonempty family of solutions.
--
--   **Definition 2.1.** A set $S$ meets the **$\rho$-LMP** guarantee (`IsLMPOutput ρ S`) if $S$ is a solution and
--   $$\sum_{j\in D}d(j,S)\le\rho\,\bigl(\mathrm{OPT}_f-f\,|S|\bigr).$$
--   A $\rho$-LMP approximation algorithm outputs such an $S$ on every instance.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, §2, printed pp. 5–6 (PDF 7–8), Definition 2.1

import Mathlib

set_option autoImplicit false

/-!
# Uncapacitated facility location with uniform opening cost; ρ-LMP outputs (§2, Definition 2.1)

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, §2 "Preliminaries", printed pp. 5–6 (PDF 7–8), Definition 2.1.

Conventions.
* The points are `Fin N`; the clients `D` and the facilities `F` are finite sets of points (they
  may overlap). Distances form a **pseudometric** on the points (nonnegative, symmetric, zero on
  the diagonal, triangle inequality); distinct points at distance `0` are allowed (the paper's
  Figures 1–3 co-locate clients with facilities).
* `d(j, S) = min_{i ∈ S} d(i, j)`. The paper's convention `d(j, ∅) = +∞` is encoded by
  feasibility: a solution `S` must be nonempty unless there are no clients. The value
  `distToSet I ∅ j = 0` is never used by a feasible solution with a client.
* `OPT_f` is a genuine minimum over the finite, nonempty family of feasible solutions.
-/

namespace BetterKMedian.LMPGreedy

/-- A metric uncapacitated facility location instance with uniform opening cost `f ≥ 0` (§2,
p. 6): points `Fin N`, real pseudometric `d`, clients `D`, facilities `F`. A facility exists
whenever a client does (otherwise no solution has finite cost). -/
structure Instance where
  /-- number of points -/
  N : ℕ
  /-- the distance between two points -/
  d : Fin N → Fin N → ℝ
  /-- the clients `D` -/
  clients : Finset (Fin N)
  /-- the facilities `F` -/
  facilities : Finset (Fin N)
  /-- the uniform opening cost `f` -/
  f : ℝ
  d_nonneg : ∀ x y, 0 ≤ d x y
  d_self : ∀ x, d x x = 0
  d_symm : ∀ x y, d x y = d y x
  d_triangle : ∀ x y z, d x z ≤ d x y + d y z
  f_nonneg : 0 ≤ f
  facilities_nonempty : clients.Nonempty → facilities.Nonempty

namespace Instance

variable (I : Instance)

/-- `d(j, S) = min_{i ∈ S} d(i, j)` for a nonempty set `S` (§2, p. 5); `0` for `S = ∅`, a value
no feasible solution with a client ever uses (see `IsFeasible`). -/
noncomputable def distToSet (S : Finset (Fin I.N)) (j : Fin I.N) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun i => I.d i j) else 0

/-- Connection cost `cost(S) = Σ_{j ∈ D} d(j, S)` (§2, p. 6). -/
noncomputable def cost (S : Finset (Fin I.N)) : ℝ :=
  ∑ j ∈ I.clients, I.distToSet S j

/-- Facility-location cost `cost_f(S) = Σ_{j ∈ D} d(j, S) + f · |S|` (§2, p. 6). -/
noncomputable def costF (S : Finset (Fin I.N)) : ℝ :=
  I.cost S + I.f * S.card

/-- A solution: `S ⊆ F`, and `S` nonempty unless there are no clients (the convention
`d(j, ∅) = +∞` of §2 makes an empty solution infinitely expensive as soon as `D ≠ ∅`). -/
def IsFeasible (S : Finset (Fin I.N)) : Prop :=
  S ⊆ I.facilities ∧ (I.clients.Nonempty → S.Nonempty)

/-- The finite family of feasible solutions. -/
noncomputable def feasibleSets : Finset (Finset (Fin I.N)) := by
  classical
  exact I.facilities.powerset.filter (fun S => I.clients.Nonempty → S.Nonempty)

/-- `OPT_f`: the optimum value of the facility-location instance, the minimum of `cost_f` over
all feasible solutions (§2, p. 6). The minimum exists: the family is finite and nonempty. -/
noncomputable def OPT : ℝ :=
  I.feasibleSets.inf'
    ⟨I.facilities, by
      classical
      simp only [feasibleSets, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨subset_rfl, I.facilities_nonempty⟩⟩
    I.costF

/-- **Definition 2.1** (p. 6): the output `S` of a facility-location algorithm on this instance
meets the `ρ`-LMP guarantee: `S ⊆ F` is a solution and
`Σ_{j ∈ D} d(j, S) ≤ ρ · (OPT_f − f · |S|)`. -/
def IsLMPOutput (ρ : ℝ) (S : Finset (Fin I.N)) : Prop :=
  I.IsFeasible S ∧ I.cost S ≤ ρ * (I.OPT - I.f * S.card)

end Instance

end BetterKMedian.LMPGreedy


