-- Prove2me | Definitions.Def_StochLoadBal_Makespan_Rounding
-- name    : StochLoadBal_Makespan_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:11.040912+00:00
-- url     : https://prove2.me/theorems/8eacfc7e-a9f7-4b1e-8e6d-686ddaba514c
-- title:
--   The LP (5)–(9), the class loop of §3.2 and the outputs of the GAP rounding characterized by (13)–(14) (pp. 10–12)
-- statement:
--   This file defines the linear program and the rounding procedure of §3 of Gupta, Kumar, Nagarajan and Shen, on top of the model (sizes $X_{ij}$, truncated parts $X'_{ij}$, exceptional parts $X''_{ij}$, effective sizes $\beta_k$).
--
--   1. **The LP** (p. 10). For a parameter $b$, a fractional assignment $y=(y_{ij})$ is feasible when, with
--   $$z_i(k) := \sum_{j=1}^n \beta_k(X'_{ij})\,y_{ij}\qquad (6),$$
--   it satisfies
--   $$\sum_{i=1}^m y_{ij}=1\ \ \forall j\ \ (5),\qquad \sum_{i=1}^m\sum_{j=1}^n \mathbb E[X''_{ij}]\,y_{ij}\le 2\ \ (7),$$
--   $$\sum_{i\in K} z_i(k)\le b\cdot k\ \ \text{for all } K\subseteq[m] \text{ with } |K|=k\ge1\ \ (8),\qquad y_{ij}\ge0,\ z_i(k)\ge 0\ \ (k=1,\dots,m)\ \ (9).$$
--   2. **The class loop** (§3.2, steps 1–2). Start with $L=[m]$ and $\ell=m$. While $\ell>0$: the machines $L'=\{i\in L: z_i(\ell)\le b\}$ are said to be in **class** $\ell$; remove them, $L\leftarrow L\setminus L'$, and set $\ell=|L|$. Write $\ell_i$ for the class of machine $i$.
--   3. **The GAP instance $I$** (step 3). Processing times $p_{ij}=\beta_{\ell_i}(X'_{ij})$, costs $c_{ij}=\mathbb E[X''_{ij}]$, makespan bound $b$.
--   4. **Outputs of the rounding.** An assignment $\sigma$ with job sets $J_i=\{j:\sigma(j)=i\}$ is an output of the rounding when it has the two properties (13)–(14) of p. 12:
--   $$\sum_{i=1}^m\sum_{j\in J_i}\mathbb E[X''_{ij}]\le 2\quad(13),\qquad \sum_{j\in J_i}\beta_{\ell_i}(X'_{ij})\le b+1\ \ \forall i\in[m]\quad(14).$$
--
--   The paper obtains its assignment from the Shmoys–Tardos algorithm for the generalized assignment problem and uses only properties (13)–(14) of it; Observation 2 states that such an assignment exists. Defining outputs by these properties makes the upper bound of Lemma 6 apply to every assignment the algorithm could return.
--
--   **Formalization Note** The variables $z_i(k)$ are not LP variables here: (6) determines them from $y$, so `zLoad` is a function of $y$. Constraint (8) is stated for every nonempty $K$ with $k=|K|$ (the case $K=\emptyset$ is trivial). The loop is a recursion with fuel $m$ that recomputes $\ell=|L|$ in each round exactly as the paper does; if some round finds $L'=\emptyset$ (impossible for a feasible $y$, by Observation 1) it stops, and an unclassified machine keeps the junk class $0$. None of these objects mentions an optimal assignment or its value.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, pp. 10–12, LP (5)–(9), §3.2 The Rounding Procedure, and (13)–(14)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

namespace StochLoadBal.Makespan

open MeasureTheory

variable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The LP load `z_i(k) = Σ_j β_k(X'_{ij}) · y_{ij}` of machine `i` at parameter `k`;
constraint (6) of the LP (p. 10) determines `z` from `y` in exactly this way. -/
noncomputable def zLoad (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (y : Fin m → Fin n → ℝ)
    (i : Fin m) (k : ℕ) : ℝ :=
  ∑ j, effSize P k (fun ω => trunc (X i j ω)) * y i j

/-- Feasibility of `y` (with `z := zLoad`, which is constraint (6)) for the LP (5)–(9) of
p. 10 with parameter `b`:
* (9) `y_{ij} ≥ 0`, and `z_i(k) ≥ 0` for `k = 1, …, m`;
* (5) `Σ_i y_{ij} = 1` for every job `j`;
* (7) `Σ_i Σ_j E[X''_{ij}] · y_{ij} ≤ 2`;
* (8) `Σ_{i ∈ K} z_i(|K|) ≤ b · |K|` for every nonempty `K ⊆ [m]`. -/
def LPFeasible (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (b : ℝ)
    (y : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ y i j) ∧
  (∀ i (k : ℕ), 1 ≤ k → k ≤ m → 0 ≤ zLoad P X y i k) ∧
  (∀ j, ∑ i, y i j = 1) ∧
  (∑ i, ∑ j, (∫ ω, exc (X i j ω) ∂P) * y i j ≤ 2) ∧
  ∀ K : Finset (Fin m), K.Nonempty →
    ∑ i ∈ K, zLoad P X y i K.card ≤ b * (K.card : ℝ)

open Classical in
/-- The class loop of the rounding procedure (§3.2, p. 11, steps 1–2), run for at most `fuel`
iterations on the set `L` of unclassified machines with current class map `cls`.
In each iteration `ℓ = |L|`; the machines `L' = {i ∈ L : z_i(ℓ) ≤ b}` receive class `ℓ` and are
removed from `L`. The loop stops when `L = ∅` (the paper's `ℓ = 0`), when the fuel is spent,
or when `L' = ∅` (where the paper's loop would not terminate; Observation 1 excludes this for
feasible `y`). -/
noncomputable def classLoop (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (b : ℝ)
    (y : Fin m → Fin n → ℝ) : ℕ → Finset (Fin m) → (Fin m → ℕ) → (Fin m → ℕ)
  | 0, _, cls => cls
  | fuel + 1, L, cls =>
    if L = ∅ then cls
    else
      if L.filter (fun i => zLoad P X y i L.card ≤ b) = ∅ then cls
      else
        classLoop P X b y fuel (L \ L.filter (fun i => zLoad P X y i L.card ≤ b))
          (fun i => if i ∈ L.filter (fun i => zLoad P X y i L.card ≤ b) then L.card else cls i)

/-- The class `ℓ_i` of machine `i` assigned by the rounding procedure (§3.2, p. 11), started
with `ℓ = m`, `L = [m]` and run for at most `m` iterations. The value `0` means "never
classified" (a junk value; Observation 1 rules it out for feasible `y`). -/
noncomputable def machineClass (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (b : ℝ)
    (y : Fin m → Fin n → ℝ) : Fin m → ℕ :=
  classLoop P X b y m Finset.univ (fun _ => 0)

/-- The deterministic processing time of the GAP instance `I` (§3.2, p. 11, step 2(b)):
`p_{ij} = β_{ℓ_i}(X'_{ij})`, where `ℓ_i` is the class of machine `i`. -/
noncomputable def procTime (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (b : ℝ)
    (y : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  effSize P (machineClass P X b y i) (fun ω => trunc (X i j ω))

/-- The assignment cost of the GAP instance `I` (§3.2, p. 11, step 1): `c_{ij} = E[X''_{ij}]`. -/
noncomputable def gapCost (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (i : Fin m) (j : Fin n) :
    ℝ :=
  ∫ ω, exc (X i j ω) ∂P

/-- An assignment `σ` (job `j` goes to machine `σ j`, so `J_i = {j | σ j = i}`) is an **output
of the rounding** of the LP solution `y` when it has the two properties (13)–(14) of p. 12,
which the Shmoys–Tardos rounding of step 3 guarantees (Observation 2):
* (13) `Σ_i Σ_{j ∈ J_i} E[X''_{ij}] ≤ 2`;
* (14) `Σ_{j ∈ J_i} β_{ℓ_i}(X'_{ij}) ≤ b + 1` for every machine `i`. -/
def IsRoundingOutput (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (b : ℝ)
    (y : Fin m → Fin n → ℝ) (σ : Fin n → Fin m) : Prop :=
  (∑ j, gapCost P X (σ j) j ≤ 2) ∧
  ∀ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), procTime P X b y i j ≤ b + 1

end StochLoadBal.Makespan


