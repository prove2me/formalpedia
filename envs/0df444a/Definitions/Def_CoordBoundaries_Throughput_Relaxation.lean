-- Prove2me | Definitions.Def_CoordBoundaries_Throughput_Relaxation
-- name    : CoordBoundaries_Throughput_Relaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:13.328224+00:00
-- url     : https://prove2.me/theorems/3a3a3dbe-2dfe-4d7b-a699-c1cb125e1bd3
-- title:
--   The configuration relaxation, its marginals and deficits, density constraints, and full and projected consistency on triples
-- statement:
--   A **configuration solution** for a candidate $(\mathcal B,\mathcal S,K)$ consists of a probability distribution $x_B=(x_{B,C})_{C\in\mathcal C(B)}$ for every block, a stored feasible schedule of every configuration inside its block, and the job constraints $y_j\le1$, where
--   $$y_{j,B}=\sum_{C\in\mathcal C(B),\,C\ni j}x_{B,C},\qquad y_j=\sum_B y_{j,B},\qquad F=\sum_j y_j.$$
--   For a global job, $a_j=y_{j,B_L(j)}$, $b_j=y_{j,B_R(j)}$ and $z_j$ is its mass in all other blocks. Further $L=\sum_{j\text{ local}}y_j$, $G=\sum_{j\text{ global}}y_j$, $Z=\sum_{j\text{ global}}z_j$, $W=\sum_{j\text{ global}}a_jb_j$, the boundary deficit $e_j=(a_j+b_j)/4-a_jb_j$ and the aggregate deficit $\mathcal D=G/4-W$ of display (1). The **density constraints** are
--   $$F\ge\frac{m\Delta|\mathcal B|}{\eta},\qquad F\ge\frac{K|\mathcal S|}{\eta^8}.$$
--
--   **Full consistency**: for every nonempty set $U$ of at most three blocks, a distribution $\pi_U$ on tuples $(C_B)_{B\in U}$ of pairwise disjoint configurations, such that $\pi_U$ restricted to every nonempty $V\subsetneq U$ equals $\pi_V$, and $\pi_{\{B\}}(C)=x_{B,C}$. **Projected consistency**: tracked sets $H_B\subseteq\{j\text{ global}: B\in\{B_L(j),B_R(j)\}\}$ and the same equations on tuples of pairwise disjoint recorded subsets $A_B\subseteq H_B$, with $\pi_{\{B\}}(A)=p_B(A)=\sum_{C\cap H_B=A}x_{B,C}$.
--
--   An **outcome** chooses one configuration per block. Independent block sampling gives outcome $\omega$ probability $\prod_Bx_{B,\omega_B}$. A **joint law** is any distribution on outcomes; it has marginals $x$ if $\Pr[C_B=C]=x_{B,C}$, and it **separates** a job set $J$ if on its support no $j\in J$ is chosen at both $B_L(j)$ and $B_R(j)$.
--
--   These are the objects that Lemma 2.2 and all of §3 are stated about.
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 10–14, §2.2 (relaxation, quantities, display (1), density constraints), §2.3 (full and projected consistency); p. 13, Lemma 2.2 (joint sampling)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Partition

open Classical

namespace CoordBoundaries.Throughput

/-! # The configuration relaxation and its consistency constraints (Tong–Xu, §2.2–§2.3, pp. 10–14)

A configuration solution fixes, for every block `B`, a probability distribution `x_B` on `𝒞(B)`
together with a stored witness schedule for every configuration, subject to `y_j ≤ 1` for every job.
The density constraints and the full or projected consistency constraints are separate predicates.
Outcomes of sampling one configuration per block are tuples `ω : Fin |ℬ| → Finset jobs`. -/

/-- A feasible solution of the configuration LP of §2.2 (p. 10): distributions `x_B` on `𝒞(B)`,
stored feasible schedules witnessing every configuration, and the job constraints `y_j ≤ 1`. -/
structure ConfigSol (I : Instance) (P : Partition I.T) (K : ℕ) where
  x : Fin P.len → Finset (Fin I.n) → ℝ
  x_nonneg : ∀ k C, 0 ≤ x k C
  x_supp : ∀ k C, C ∉ P.configs K k → x k C = 0
  x_sum : ∀ k, ∑ C ∈ P.configs K k, x k C = 1
  store : Fin P.len → Finset (Fin I.n) → Sched I
  store_ok : ∀ k C, C ∈ P.configs K k → P.WitnessIn k C (store k C)
  job_le : ∀ j, ∑ k, ∑ C ∈ (P.configs K k).filter (fun C => j ∈ C), x k C ≤ 1

/-- A tuple choosing one job set per block. -/
abbrev Tuple (I : Instance) (P : Partition I.T) := Fin P.len → Finset (Fin I.n)

namespace ConfigSol

variable {I : Instance} {P : Partition I.T} {K : ℕ} (s : ConfigSol I P K)

/-- Placement marginal `y_{j,B} = Σ_{C ∋ j} x_{B,C}`. -/
noncomputable def y (j : Fin I.n) (k : Fin P.len) : ℝ :=
  ∑ C ∈ (P.configs K k).filter (fun C => j ∈ C), s.x k C

/-- `y_{j,B}` at a block given by its index (`0` beyond the last block). -/
noncomputable def yN (j : Fin I.n) (t : ℕ) : ℝ := if h : t < P.len then s.y j ⟨t, h⟩ else 0

/-- Total fractional mass `y_j = Σ_B y_{j,B}`. -/
noncomputable def yj (j : Fin I.n) : ℝ := ∑ k, s.y j k

/-- Fractional throughput `F = Σ_j y_j`. -/
noncomputable def F : ℝ := ∑ j, s.yj j

/-- Left boundary mass `a_j = y_{j, B_L(j)}`. -/
noncomputable def a (j : Fin I.n) : ℝ := s.yN j (P.BL j)

/-- Right boundary mass `b_j = y_{j, B_R(j)}`. -/
noncomputable def b (j : Fin I.n) : ℝ := s.yN j (P.BR j)

/-- Interior mass `z_j = Σ_S z_{j,S}`, the mass outside the two boundary blocks. -/
noncomputable def z (j : Fin I.n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin P.len => (k : ℕ) ≠ P.BL j ∧ (k : ℕ) ≠ P.BR j), s.y j k

/-- `L = Σ_{j local} y_j`. -/
noncomputable def L : ℝ := ∑ j ∈ Finset.univ.filter P.IsLocal, s.yj j

/-- `G = Σ_{j global} y_j`. -/
noncomputable def G : ℝ := ∑ j ∈ Finset.univ.filter P.IsGlobal, s.yj j

/-- `Z = Σ_{j global} z_j`. -/
noncomputable def Z : ℝ := ∑ j ∈ Finset.univ.filter P.IsGlobal, s.z j

/-- `W = Σ_{j global} a_j b_j`. -/
noncomputable def W : ℝ := ∑ j ∈ Finset.univ.filter P.IsGlobal, s.a j * s.b j

/-- Boundary deficit `e_j = (a_j + b_j)/4 − a_j b_j` (p. 10). -/
noncomputable def e (j : Fin I.n) : ℝ := (s.a j + s.b j) / 4 - s.a j * s.b j

/-- The aggregate deficit `𝒟 = G/4 − W` of display (1), p. 10. -/
noncomputable def Dagg : ℝ := s.G / 4 - s.W

/-- First density constraint `F ≥ m∆|ℬ|/η` (p. 10). -/
def DenseBlocks (Δ q : ℕ) : Prop := (I.m : ℝ) * Δ * P.len / eta q ≤ s.F

/-- Second density constraint `F ≥ K|𝒮|/η⁸` (p. 10). -/
def DenseSuper (q : ℕ) : Prop := (K : ℝ) * P.numSuper / eta q ^ 8 ≤ s.F

end ConfigSol

/-- Keep only the entries of a tuple at blocks of `V` (`C|_V`; other entries become `∅`). -/
def restrictT {I : Instance} {P : Partition I.T} (V : Finset (Fin P.len)) (C : Tuple I P) :
    Tuple I P :=
  fun B => if B ∈ V then C B else ∅

/-- The tuple with `A` at block `B` and `∅` elsewhere. -/
def singleT {I : Instance} {P : Partition I.T} (B : Fin P.len) (A : Finset (Fin I.n)) :
    Tuple I P :=
  fun B' => if B' = B then A else ∅

/-- `Ω_U` (pp. 11–12): tuples over the blocks of `U` whose entry at each `B ∈ U` is an allowed
state of `B` and whose entries are pairwise disjoint (entries outside `U` are `∅`). -/
noncomputable def Omega {I : Instance} {P : Partition I.T}
    (St : Fin P.len → Finset (Finset (Fin I.n))) (U : Finset (Fin P.len)) : Finset (Tuple I P) :=
  Finset.univ.filter fun C =>
    (∀ B, B ∉ U → C B = ∅) ∧ (∀ B ∈ U, C B ∈ St B) ∧
      (∀ B ∈ U, ∀ B' ∈ U, B ≠ B' → Disjoint (C B) (C B'))

/-- Consistency on triples (p. 11 and p. 12) for per-block state families `St` and prescribed
single-block distributions `μ`: probabilities `π_U ≥ 0` supported on `Ω_U`, normalized for every
nonempty `U` with `|U| ≤ 3`, with marginal consistency for `∅ ≠ V ⊊ U`, and `π_{{B}} = μ_B`. -/
structure Consistent {I : Instance} {P : Partition I.T}
    (St : Fin P.len → Finset (Finset (Fin I.n))) (μ : Fin P.len → Finset (Fin I.n) → ℝ)
    (π : Finset (Fin P.len) → Tuple I P → ℝ) : Prop where
  nonneg : ∀ U C, 0 ≤ π U C
  supp : ∀ U C, C ∉ Omega St U → π U C = 0
  norm : ∀ U : Finset (Fin P.len), U.Nonempty → U.card ≤ 3 → ∑ C ∈ Omega St U, π U C = 1
  marg : ∀ U V : Finset (Fin P.len), V.Nonempty → V ⊂ U → U.card ≤ 3 →
    ∀ D ∈ Omega St V, ∑ C ∈ (Omega St U).filter (fun C => restrictT V C = D), π U C = π V D
  single : ∀ (B : Fin P.len), ∀ A ∈ St B, π {B} (singleT B A) = μ B A

/-- Tracked sets (p. 12): `H_B ⊆ {j global : B ∈ {B_L(j), B_R(j)}}`. -/
def Partition.ValidTracked {I : Instance} (P : Partition I.T) (H : Fin P.len → Finset (Fin I.n)) :
    Prop :=
  ∀ (B : Fin P.len), ∀ j ∈ H B, P.IsGlobal j ∧ ((B : ℕ) = P.BL j ∨ (B : ℕ) = P.BR j)

namespace ConfigSol

variable {I : Instance} {P : Partition I.T} {K : ℕ} (s : ConfigSol I P K)

/-- Full consistency (p. 11): consistent distributions on tuples of configurations with
`π_{{B}}(C) = x_{B,C}`. -/
def FullConsistent (π : Finset (Fin P.len) → Tuple I P → ℝ) : Prop :=
  Consistent (fun B => P.configs K B) s.x π

/-- `p_B(A) = Σ_{C : Ψ_B(C) = A} x_{B,C}` with `Ψ_B(C) = C ∩ H_B` (p. 12). -/
noncomputable def stateMass (H : Fin P.len → Finset (Fin I.n)) (B : Fin P.len)
    (A : Finset (Fin I.n)) : ℝ :=
  ∑ C ∈ (P.configs K B).filter (fun C => C ∩ H B = A), s.x B C

/-- Projected consistency (p. 12): tracked sets `H`, and consistent distributions on tuples of
recorded subsets `A_B ⊆ H_B` whose single-block laws are `p_B`. -/
def ProjConsistent (H : Fin P.len → Finset (Fin I.n))
    (π : Finset (Fin P.len) → Tuple I P → ℝ) : Prop :=
  P.ValidTracked H ∧ Consistent (fun B => (H B).powerset) (s.stateMass H) π

end ConfigSol

/-- Entry of a tuple at a block given by its index (`∅` beyond the last block). -/
def atN {I : Instance} {P : Partition I.T} (ω : Tuple I P) (t : ℕ) : Finset (Fin I.n) :=
  if h : t < P.len then ω ⟨t, h⟩ else ∅

/-- The outcomes of sampling one configuration per block: `∏_B 𝒞(B)`. -/
noncomputable def outcomes {I : Instance} (P : Partition I.T) (K : ℕ) : Finset (Tuple I P) :=
  Fintype.piFinset fun B => P.configs K B

namespace ConfigSol

variable {I : Instance} {P : Partition I.T} {K : ℕ} (s : ConfigSol I P K)

/-- Probability of `ω` under independent block sampling: `∏_B x_{B, ω_B}`. -/
noncomputable def prodProb (ω : Tuple I P) : ℝ := ∏ B, s.x B (ω B)

/-- Expectation under independent block sampling. -/
noncomputable def Eprod (f : Tuple I P → ℝ) : ℝ := ∑ ω ∈ outcomes P K, s.prodProb ω * f ω

/-- `μ` has the block marginals `Pr[C_B = C] = x_{B,C}` (Lemma 2.2). -/
def HasMarginals (μ : Tuple I P → ℝ) : Prop :=
  ∀ (B : Fin P.len) (C : Finset (Fin I.n)),
    ∑ ω ∈ (outcomes P K).filter (fun ω => ω B = C), μ ω = s.x B C

end ConfigSol

/-- `μ` is a probability distribution on the outcomes `∏_B 𝒞(B)`. -/
def IsLaw {I : Instance} (P : Partition I.T) (K : ℕ) (μ : Tuple I P → ℝ) : Prop :=
  (∀ ω, 0 ≤ μ ω) ∧ (∀ ω, ω ∉ outcomes P K → μ ω = 0) ∧ ∑ ω ∈ outcomes P K, μ ω = 1

/-- On the support of `μ`, no job of `J` is chosen at both of its boundary blocks. -/
def Separates {I : Instance} (P : Partition I.T) (μ : Tuple I P → ℝ) (J : Finset (Fin I.n)) :
    Prop :=
  ∀ ω, μ ω ≠ 0 → ∀ j ∈ J, ¬ (j ∈ atN ω (P.BL j) ∧ j ∈ atN ω (P.BR j))

/-- Tracked set at a block given by its index (`∅` beyond the last block). -/
def trackedAt {I : Instance} {P : Partition I.T} (H : Fin P.len → Finset (Fin I.n)) (t : ℕ) :
    Finset (Fin I.n) :=
  if h : t < P.len then H ⟨t, h⟩ else ∅

end CoordBoundaries.Throughput


