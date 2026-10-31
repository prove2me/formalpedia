-- Prove2me | Definitions.Def_MalleableSched_LP1
-- name    : MalleableSched_LP1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:54.005054+00:00
-- url     : https://prove2.me/theorems/039b26a0-e5e1-4478-b441-b32b590e8e20
-- title:
--   The LP (LP1), its support graph, Type 1/Type 2 jobs, $\bar S_j$, $J^1_i$, $\ell_i$ and the threshold sets $T_j(\theta)$
-- statement:
--   Fix an assignment $\mathbf S$, a real $C$ and a matrix $\Delta\in\mathbb R^{M\times J}$ (the core vectors of Lemma 4). Let $S_j^+=\{i\in S_j:\Delta_{ij}>0\}$. The feasibility LP (LP1) has a variable $x_{ij}$ for every $j\in J$ and $i\in S_j^+$:
--   $$
--   \sum_{i\in S_j^+}x_{ij}\ge1\ \ (j\in J),\qquad \sum_{j\in J:\,i\in S_j^+}\frac{1}{\Delta_{ij}}\,x_{ij}\le C\ \ (i\in M),\qquad x\ge0 .
--   $$
--   For a solution $x'$, the **support graph** $G(x')$ on $J\cup M$ has an edge $\{i,j\}$ whenever $x'_{ij}>0$. Given an orientation of $G(x')$:
--
--   1. job $j$ is of **Type 1** if it has an in-edge $(i_j,j)$ with $x'_{i_jj}>1/2$; otherwise it is of **Type 2**;
--   2. $\bar S_j$ is the set of machines $i$ with an edge directed $j\to i$;
--   3. $J^1_i=\{j: i_j=i,\ x'_{i_jj}>1/2\}$ and $\ell_i=\sum_{j'\in J^1_i}\frac{1}{\Delta_{ij'}}x'_{ij'}$, the LP load of machine $i$ from Type 1 jobs;
--   4. for $\theta>0$, $T_j(\theta)=\{i\in\bar S_j:\ell_i\le\theta\}$, and $\theta\mapsto\max_{i\in T_j(\theta)}2\ell_i+f_j(T_j(\theta))$ is the function whose minimizer $\theta^*_j$ defines the reduced assignment;
--   5. the **reduced assignment** $\mathbf T$ puts a Type 1 job on $\{i_j\}$ and a Type 2 job on $T_j(\theta^*_j)$.
--
--   These objects carry the proof of Theorem 1 (§2.1): (LP1) is feasible, an extreme point has a pseudoforest support graph, and rounding along an orientation gives a well-structured assignment.
--
--   **Formalization Note** $x$ and $\Delta$ are real $m\times n$ matrices (rows machines, columns jobs); the entries of $x$ outside $\{(i,j):i\in S^+_j\}$ are required to be $0$, an affine copy of the paper's variable space. The support graph is the published edge set `supportEdges x` $=\{(i,j):x_{ij}>0\}$. An orientation is a predicate `toJob i j` ("the edge is directed $i\to j$"); `InDegLeOne` says every job and every machine has at most one in-edge. In the reduced assignment, $i_j$ is a chosen witness of the Type 1 property (unique under in-degree at most one). The maximum over $T_j(\theta)$ is a supremum in $[0,\infty]$ ($0$ on the empty set, where $f_j(\emptyset)=\infty$).
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, §2.1, pp.8–9 ((LP1), S⁺ⱼ, G(x′), Type 1/Type 2, S̄ⱼ, J¹ᵢ, ℓᵢ, Tⱼ(θ), θ*ⱼ, Lemma 9's T)

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

open scoped ENNReal

namespace MalleableSched

open UnrelatedSched.TwoApprox

/-- **The machine set `S⁺ⱼ = {i ∈ Sⱼ : Δᵢⱼ > 0}`.** Fotakis, Matuschke & Papadigenopoulos,
arXiv:2111.06225v2, §2.1, p.8: "Using the coefficients Δij given by Lemma 4, let
S+_j := {i ∈ Sj : Δij > 0} for j ∈ J".

**Formalization Note.** `Δ : Matrix (Fin m) (Fin n) ℝ` has rows indexed by machines and columns
by jobs (the paper's `Δ ∈ ℝ^{M×J}`). -/
noncomputable def Splus {n m : ℕ} (Δ : Matrix (Fin m) (Fin n) ℝ) (S : Fin n → Finset (Fin m))
    (j : Fin n) : Finset (Fin m) :=
  (S j).filter (fun i => 0 < Δ i j)

/-- **Feasible solution of (LP1).** arXiv:2111.06225v2, §2.1, p.8: "consider the following
feasibility LP with decision variables xij for every j ∈ J and i ∈ S+_j.
Σ_{i∈S+_j} xij ≥ 1 ∀j ∈ J; Σ_{j∈J:i∈S+_j} (1/Δij) xij ≤ C ∀ i ∈ M; x ≥ 0 (LP1)".

**Formalization Note.** `x` is a full `m × n` real matrix (rows machines, columns jobs) whose
entries outside the paper's variable set `{(i, j) : i ∈ S⁺ⱼ}` are fixed to `0` (`zero_outside`).
This set is an affine copy of the paper's feasible region, so extreme points correspond. The
coefficient `(1/Δᵢⱼ) xᵢⱼ` is written `x i j / Δ i j`. -/
structure LP1Feasible {n m : ℕ} (Δ : Matrix (Fin m) (Fin n) ℝ) (S : Fin n → Finset (Fin m))
    (C : ℝ) (x : Matrix (Fin m) (Fin n) ℝ) : Prop where
  zero_outside : ∀ i j, i ∉ Splus Δ S j → x i j = 0
  nonneg : ∀ i j, 0 ≤ x i j
  job : ∀ j, 1 ≤ ∑ i ∈ Splus Δ S j, x i j
  machine : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ Splus Δ S j), x i j / Δ i j ≤ C

/-- **The feasible region of (LP1)** (arXiv:2111.06225v2, §2.1, p.8), a subset of
`ℝ^{M×J}`. An *extreme point solution* of (LP1) (p.8) is an element of
`Set.extremePoints ℝ (LP1Region Δ S C)`. -/
def LP1Region {n m : ℕ} (Δ : Matrix (Fin m) (Fin n) ℝ) (S : Fin n → Finset (Fin m)) (C : ℝ) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {x | LP1Feasible Δ S C x}

/-- **Orientation of a machine–job graph with in-degree at most one.** arXiv:2111.06225v2,
Lemma 6, p.8: "The graph G(x′) has an orientation such that any node has an in-degree of at most
1."

**Formalization Note.** The bipartite graph has machine nodes `Fin m`, job nodes `Fin n` and edge
set `E` (an edge `{i, j}` is the pair `(i, j)`). An orientation is a predicate
`toJob : Fin m → Fin n → Prop`: the edge `(i, j)` is directed `i → j` (an in-edge of job `j`)
if `toJob i j`, and `j → i` (an in-edge of machine `i`) otherwise; values off `E` are irrelevant.
In-degree at most one: every job has at most one in-edge and every machine has at most one
in-edge. -/
def InDegLeOne {n m : ℕ} (E : Finset (Fin m × Fin n)) (toJob : Fin m → Fin n → Prop) : Prop :=
  (∀ j : Fin n, {i : Fin m | (i, j) ∈ E ∧ toJob i j}.Subsingleton) ∧
    (∀ i : Fin m, {j : Fin n | (i, j) ∈ E ∧ ¬ toJob i j}.Subsingleton)

/-- **Type 1 job.** arXiv:2111.06225v2, §2.1, p.9: "For each job j ∈ J, let ij ∈ Sj denote the
unique machine such that (ij, j) is an in-edge of node j (if such a machine exists) … let
S′j = {ij} if ij exists and x′_{ij j} > 1/2 ("Type 1 assignment") and let S′j = S̄j otherwise
("Type 2 assignment")."

**Formalization Note.** The support graph `G(x′)` has edge set `supportEdges x` (the pairs with
`x i j > 0`). Job `j` is of Type 1 if some in-edge `(i, j)` of `j` has `x i j > 1/2`; when every
node has in-degree at most one, that `i` is the paper's `i_j`. -/
def IsType1 {n m : ℕ} (x : Matrix (Fin m) (Fin n) ℝ) (toJob : Fin m → Fin n → Prop)
    (j : Fin n) : Prop :=
  ∃ i : Fin m, (i, j) ∈ supportEdges x ∧ toJob i j ∧ 1 / 2 < x i j

open Classical in
/-- **The machine set `S̄ⱼ`.** arXiv:2111.06225v2, §2.1, p.9: "let S̄j the set of machines
i ∈ S+_j such that there is an edge (j, i) in the oriented graph."

**Formalization Note.** The machines `i` with `(i, j)` an edge of the support graph of `x`
directed `j → i` (`¬ toJob i j`). For `x` feasible for (LP1), every such `i` lies in `S⁺ⱼ`. -/
noncomputable def Sbar {n m : ℕ} (x : Matrix (Fin m) (Fin n) ℝ) (toJob : Fin m → Fin n → Prop)
    (j : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (i, j) ∈ supportEdges x ∧ ¬ toJob i j)

open Classical in
/-- **The job set `J¹ᵢ`.** arXiv:2111.06225v2, Lemma 7, p.9: "For i ∈ M let
J1_i := {j ∈ J : ij = i, x′_{ij j} > 1/2}."

**Formalization Note.** The jobs `j` whose in-edge `(i, j)` (directed `i → j`) in the support
graph of `x` has `x i j > 1/2`. -/
noncomputable def J1 {n m : ℕ} (x : Matrix (Fin m) (Fin n) ℝ) (toJob : Fin m → Fin n → Prop)
    (i : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (i, j) ∈ supportEdges x ∧ toJob i j ∧ 1 / 2 < x i j)

/-- **The Type 1 LP load `ℓᵢ`.** arXiv:2111.06225v2, §2.1, p.9: "ℓi := Σ_{j′∈J1_i}
(1/Δij′) x′_{ij′} be the load of machine i due to jobs in J1_i in the LP solution." -/
noncomputable def ell {n m : ℕ} (Δ : Matrix (Fin m) (Fin n) ℝ) (x : Matrix (Fin m) (Fin n) ℝ)
    (toJob : Fin m → Fin n → Prop) (i : Fin m) : ℝ :=
  ∑ j ∈ J1 x toJob i, x i j / Δ i j

open Classical in
/-- **The threshold set `Tⱼ(θ)`.** arXiv:2111.06225v2, §2.1, p.9: "For θ > 0, let
Tj(θ) := {i ∈ S̄j : ℓi ≤ θ}." -/
noncomputable def thresholdSet {n m : ℕ} (Δ : Matrix (Fin m) (Fin n) ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) (toJob : Fin m → Fin n → Prop) (j : Fin n) (θ : ℝ) :
    Finset (Fin m) :=
  (Sbar x toJob j).filter (fun i => ell Δ x toJob i ≤ θ)

/-- **The function minimized by `θ*ⱼ`.** arXiv:2111.06225v2, §2.1, p.9: "assign it to
Tj(θ∗_j), where θ∗_j is a minimizer of max_{i∈Tj(θ)} 2ℓi + fj(Tj(θ))."

**Formalization Note.** The value is `max_{i ∈ Tⱼ(θ)} 2ℓᵢ + fⱼ(Tⱼ(θ))` in `ℝ≥0∞`; the maximum
is `⨆` (equal to `0` over the empty set, where `fⱼ(∅) = ∞` makes the value `∞`). Each `ℓᵢ` is
nonnegative for feasible `x`, so `ENNReal.ofReal` loses nothing. -/
noncomputable def thresholdObjective {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ)
    (Δ : Matrix (Fin m) (Fin n) ℝ) (x : Matrix (Fin m) (Fin n) ℝ)
    (toJob : Fin m → Fin n → Prop) (j : Fin n) (θ : ℝ) : ℝ≥0∞ :=
  (⨆ i ∈ thresholdSet Δ x toJob j θ, ENNReal.ofReal (2 * ell Δ x toJob i)) +
    procTime g j (thresholdSet Δ x toJob j θ)

open Classical in
/-- **The reduced assignment `T` of Lemma 9.** arXiv:2111.06225v2, Lemma 9, p.9: "Let T be the
assignment defined by Tj = Tj(θ∗) if S′j = S̄j and Tj = {ij} otherwise."

**Formalization Note.** A Type 1 job `j` goes to `{i_j}`, where `i_j` is a chosen witness of
`IsType1 x toJob j` (unique when every node has in-degree at most one); every other job goes to
`Tⱼ(θ*ⱼ)` with `θ*ⱼ = θstar j`. -/
noncomputable def lemma9Assignment {n m : ℕ} (Δ : Matrix (Fin m) (Fin n) ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) (toJob : Fin m → Fin n → Prop) (θstar : Fin n → ℝ) :
    Fin n → Finset (Fin m) :=
  fun j => if h : IsType1 x toJob j then {Classical.choose h} else
    thresholdSet Δ x toJob j (θstar j)

end MalleableSched


