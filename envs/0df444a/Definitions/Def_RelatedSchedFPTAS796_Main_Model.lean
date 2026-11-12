-- Prove2me | Definitions.Def_RelatedSchedFPTAS796_Main_Model
-- name    : RelatedSchedFPTAS796_Main_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:19.946642+00:00
-- url     : https://prove2.me/theorems/03b46f63-c9e7-4f8b-bdb3-4cac69ceb53b
-- title:
--   Related-machine schedules, makespan, work profiles and additive set approximation
-- statement:
--   **Scheduling on related machines.** An instance of $Qm\|C_{\max}$ consists of $n\ge 0$ jobs with positive rational sizes $p_1,\dots,p_n$ (a multiset: equal sizes keep their multiplicity) and $m$ machines with positive rational speeds $s_1,\dots,s_m$. A schedule $\sigma$ assigns every job to one machine. The load of machine $i$ is
--   $$L_i(\sigma)=\frac{1}{s_i}\sum_{j:\,\sigma(j)=i}p_j,$$
--   the makespan is $C_{\max}(\sigma)=\max_i L_i(\sigma)$, and $\sigma$ is **$(1+\varepsilon)$-approximate** when $C_{\max}(\sigma)\le(1+\varepsilon)\,C_{\max}(\tau)$ for every schedule $\tau$, i.e. $C_{\max}(\sigma)\le(1+\varepsilon)\mathrm{OPT}$ with $\mathrm{OPT}$ the minimum over all $m^n$ schedules.
--
--   **Work profiles.** The work profile $P(\sigma)\in\mathbb R^m$ records the total size assigned to each machine; $\mathcal P(J)$ is the set of all work profiles. A **partial schedule** on $d$ explicit machines assigns each job to one of the machines $1,\dots,d$ or leaves it for an implicit machine $d+1$; its partial work profile records the totals on the explicit machines, and $\mathcal S(J)\subseteq\mathbb R^d$ is the set of partial work profiles. For a sub-multiset $J''\subseteq J$, $\mathcal S(J'')$ uses only jobs of $J''$, and $\Sigma(J'')$ is their total size.
--
--   **Set approximation (Definition 2.1).** For finite $S,\tilde S\subseteq\mathbb R^d_{\ge0}$, a box $B$ (closed $[v,w]$, half-open $[v,w)$, or the whole space) and $\delta\in\mathbb R^d_{\ge0}$, $\tilde S$ approximates $S\cap B$ with additive error $\delta$ if (i) every $x\in S\cap B$ has some $\tilde x\in\tilde S$ with $x-\delta\le\tilde x\le x+\delta$, and (ii) every $\tilde x\in\tilde S$ has some $x\in S$ (not necessarily in $B$) with $\tilde x-\delta\le x\le\tilde x+\delta$. Vector inequalities are coordinatewise.
--
--   **Definition 5.1.** $A\subseteq_\delta B$ if every $a\in A$ has some $b\in B$ with $a-\delta\le b\le a+\delta$.
--
--   **Definition 5.4.** A set $T$ of vectors is **axis-projection closed** if $x_je_j\in T$ whenever $x\in T$ and $1\le j\le d$.
--
--   **Definition 5.2.** A **$\kappa$-grid** is a set $G=s+\{\sum_{j=1}^d z_j\delta_je_j: 0\le z_j\le N_j,\ z_j\in\mathbb Z\}$ with $0<\delta_j<\kappa_j$, $s_j\ge0$, $s_j+N_j\delta_j\le\kappa_j/\varepsilon$ and $N_j\delta_j\ge 2/\varepsilon-1$ for every $j$. For $J'\subseteq J$, a **dense certificate** for $J'$ with error $\delta$ is a pair $(J'',S)$ with $J''\subseteq J'$, $\Sigma(J'')\le\Sigma(J')/(2d+2)$ and a $\kappa$-grid $G$ with $G\subseteq_\delta S\subseteq_\delta\mathcal S(J'')$.
--
--   These are the objects of the whole mission: the goal compares the output schedule with every schedule, and the profile problems are stated through $\mathcal P$, $\mathcal S$ and Definition 2.1.
--
--   **Formalization Note** Jobs are families indexed by their occurrences (`Fin n`); schedules are maps `Fin n → Fin m`, partial schedules maps `Fin n → Option (Fin d)` (`none` is the implicit machine). The makespan is `max` folded from `0`, which is the maximum load because all loads are nonnegative on instances with positive data. The half-open box is written coordinatewise because the strict order on `Fin d → ℝ` is not coordinatewise. In Definition 5.2 the paper's $\tilde O(\kappa)$ is a parameter $\delta$, made explicit where the certificate is used.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, §1 p.1 lines 20–25; §2.2 pp.7–8; §3 p.9 lines 345–349; Definition 2.1 p.8; Definition 5.1 p.13; Definition 5.2 p.13; Definition 5.4 p.14

import Mathlib

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-!
# Scheduling on related machines, work profiles and set approximation

Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, *Faster Approximation Schemes for
Scheduling on Related Machines*, STOC 2027 submission #796 (October 2026), §1 p.1 lines 20–25,
§2.2 pp.7–8 (problem `Qm∥Cmax`, work profiles `𝒫(J)`), §3 p.9 lines 345–349 (partial profiles
`𝒮(J)`), Definition 2.1 p.8, Definition 5.1 p.13, Definition 5.2 p.13, Definition 5.4 p.14.

**Formalization Note.**
* A multiset of `n` jobs is a family `p : Fin n → R` of sizes indexed by its occurrences
  (equal sizes keep their multiplicity). A schedule on `m` machines is `σ : Fin n → Fin m`
  (job occurrence `j` runs on machine `σ j`); a partial schedule on `d` explicit machines is
  `σ : Fin n → Option (Fin d)`, where `none` is the implicit machine `d + 1`.
* Vectors of `ℝ^d` are `Fin d → ℝ`. A closed box `[v, w]` is `Set.Icc v w` (the order on
  `Fin d → ℝ` is coordinatewise); the half-open box `[v, w)` is written out coordinatewise as
  `boxIco v w`, because the strict order `<` on `Fin d → ℝ` is *not* coordinatewise.
* The makespan is the maximum of the loads, computed as `Finset.fold max 0`; on the instances of the
  paper (positive sizes and speeds) all loads are `≥ 0`, so this is the maximum load.
-/

open Finset

section Scheduling

variable {n m : ℕ}

/-- The load `L_i(σ) = (∑_{j ∈ J_i(σ)} p_j) / s_i` of machine `i` under the schedule `σ`. -/
def load (p : Fin n → ℚ) (s : Fin m → ℚ) (σ : Fin n → Fin m) (i : Fin m) : ℚ :=
  (∑ j ∈ univ.filter (fun j => σ j = i), p j) / s i

/-- The makespan `C_max(σ) = max_i L_i(σ)` (as `max` folded from `0`; loads are nonnegative on
instances with positive data). -/
def makespan (p : Fin n → ℚ) (s : Fin m → ℚ) (σ : Fin n → Fin m) : ℚ :=
  (univ : Finset (Fin m)).fold max 0 (load p s σ)

/-- `σ` is a `(1 + ε)`-approximate schedule: `C_max(σ) ≤ (1 + ε)·C_max(τ)` for every schedule `τ`,
i.e. `C_max(σ) ≤ (1 + ε)·OPT` with `OPT` the minimum makespan over all `m^n` schedules. -/
def IsNearOptimal (p : Fin n → ℚ) (s : Fin m → ℚ) (ε : ℚ) (σ : Fin n → Fin m) : Prop :=
  ∀ τ : Fin n → Fin m, makespan p s σ ≤ (1 + ε) * makespan p s τ

end Scheduling

section Profiles

variable {n : ℕ}

/-- The work profile `P(σ)`: coordinate `i` is the total size of the jobs that `σ` assigns to
machine `i`. -/
def workProfile {m : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) : Fin m → ℝ :=
  fun i => ∑ j ∈ univ.filter (fun j => σ j = i), p j

/-- The set `𝒫(J) = {P(σ) : σ a feasible schedule}` of feasible work profiles on `m` machines. -/
def workProfiles (m : ℕ) (p : Fin n → ℝ) : Set (Fin m → ℝ) :=
  Set.range (workProfile (m := m) p)

/-- The partial work profile of a partial schedule on `d` explicit machines: coordinate `i` is the
total size of the jobs in `J_i(σ) = {j : σ j = some i}`; jobs with `σ j = none` are left for the
implicit machine `d + 1`. -/
def partialProfile {d : ℕ} (p : Fin n → ℝ) (σ : Fin n → Option (Fin d)) : Fin d → ℝ :=
  fun i => ∑ j ∈ univ.filter (fun j => σ j = some i), p j

/-- The set `𝒮(J)` of partial work profiles on `d` explicit machines. -/
def partialProfiles (d : ℕ) (p : Fin n → ℝ) : Set (Fin d → ℝ) :=
  Set.range (partialProfile (d := d) p)

/-- `𝒮(J'')` for the sub-multiset `J'' ⊆ J` given by a set of occurrences `T`: the partial profiles
of the partial schedules that use only jobs of `T` (all other jobs on the implicit machine). -/
def partialProfilesOn (d : ℕ) (p : Fin n → ℝ) (T : Finset (Fin n)) : Set (Fin d → ℝ) :=
  {x | ∃ σ : Fin n → Option (Fin d), (∀ j, j ∉ T → σ j = none) ∧ x = partialProfile p σ}

/-- The total size `Σ(J'')` of the jobs of `J` with occurrence in `T`. -/
def totalOn (p : Fin n → ℝ) (T : Finset (Fin n)) : ℝ := ∑ j ∈ T, p j

end Profiles

section Approximation

variable {d : ℕ}

/-- The half-open coordinate box `[v, w) = ∏_i [v_i, w_i)`. -/
def boxIco (v w : Fin d → ℝ) : Set (Fin d → ℝ) := {x | ∀ i, v i ≤ x i ∧ x i < w i}

/-- The nonnegative orthant `ℝ^d_{≥0}`. -/
def nonneg (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, 0 ≤ x i}

/-- **Definition 2.1** (p.8). `S'` approximates `S ∩ B` with additive error `δ`: both sets are
finite subsets of `ℝ^d_{≥0}`, and
(i) every `x ∈ S ∩ B` has some `x' ∈ S'` with `x − δ ≤ x' ≤ x + δ`;
(ii) every `x' ∈ S'` has some `x ∈ S` (not necessarily in `B`) with `x' − δ ≤ x ≤ x' + δ`.
The box `B` is a closed box `Set.Icc v w`, a half-open box `boxIco v w`, or `Set.univ` ("when no
box is specified, the approximation concerns the whole set"). -/
def ApproxAdd (S S' B : Set (Fin d → ℝ)) (δ : Fin d → ℝ) : Prop :=
  S.Finite ∧ S ⊆ nonneg d ∧ S'.Finite ∧ S' ⊆ nonneg d ∧
  (∀ x ∈ S ∩ B, ∃ x' ∈ S', x - δ ≤ x' ∧ x' ≤ x + δ) ∧
  (∀ x' ∈ S', ∃ x ∈ S, x' - δ ≤ x ∧ x ≤ x' + δ)

/-- **Definition 5.1** (p.13). `A ⊆_δ B`: every `a ∈ A` has some `b ∈ B` with `a − δ ≤ b ≤ a + δ`. -/
def SubsetApprox (A B : Set (Fin d → ℝ)) (δ : Fin d → ℝ) : Prop :=
  ∀ a ∈ A, ∃ b ∈ B, a - δ ≤ b ∧ b ≤ a + δ

/-- **Definition 5.4** (p.14). `T` is axis-projection closed: `x_j e_j ∈ T` whenever `x ∈ T` and
`j ∈ {1, …, d}` (`Pi.single j (x j)` is `x_j e_j`). Used for sets of real or integer vectors. -/
def AxisProjClosed {R : Type*} [Zero R] (T : Set (Fin d → R)) : Prop :=
  ∀ x ∈ T, ∀ j : Fin d, Pi.single j (x j) ∈ T

/-- **Definition 5.2** (p.13), first part. A `κ`-grid (for accuracy `ε`):
`G = s + {∑_j z_j δ_j e_j : 0 ≤ z_j ≤ N_j, z_j ∈ ℤ}` with `0 < δ_j < κ_j`, `s_j ≥ 0`,
`s_j + N_j δ_j ≤ κ_j / ε` and `N_j δ_j ≥ 2/ε − 1` for every `j`. -/
def IsKappaGrid (ε : ℝ) (κ : Fin d → ℝ) (G : Set (Fin d → ℝ)) : Prop :=
  ∃ (s δ : Fin d → ℝ) (N : Fin d → ℕ),
    (∀ j, 0 < δ j ∧ δ j < κ j ∧ 0 ≤ s j ∧ s j + N j * δ j ≤ κ j / ε ∧ 2 / ε - 1 ≤ N j * δ j) ∧
    G = {x | ∃ z : Fin d → ℕ, (∀ j, z j ≤ N j) ∧ x = fun j => s j + z j * δ j}

/-- **Definition 5.2** (p.13), second part, with the error `Õ(κ)` made explicit as `δ`.
For the jobs `p` and a sub-multiset `J' ⊆ J` (occurrences `J'`), a dense certificate for `J'` is a
pair `(J'', S)` with `J'' ⊆ J'`, `Σ(J'') ≤ Σ(J')/(2d + 2)`, and a `κ`-grid `G` with
`G ⊆_δ S ⊆_δ 𝒮(J'')`. -/
def IsDenseCertificate {n : ℕ} (ε : ℝ) (κ δ : Fin d → ℝ) (p : Fin n → ℝ) (J' J'' : Finset (Fin n))
    (S : Set (Fin d → ℝ)) : Prop :=
  J'' ⊆ J' ∧ totalOn p J'' ≤ totalOn p J' / (2 * d + 2) ∧
  ∃ G : Set (Fin d → ℝ), IsKappaGrid ε κ G ∧ SubsetApprox G S δ ∧
    SubsetApprox S (partialProfilesOn d p J'') δ

end Approximation

end RelatedSchedFPTAS796.Main


