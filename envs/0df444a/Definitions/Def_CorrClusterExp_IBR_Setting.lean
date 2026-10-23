-- Prove2me | Definitions.Def_CorrClusterExp_IBR_Setting
-- name    : CorrClusterExp_IBR_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:27.771919+00:00
-- url     : https://prove2.me/theorems/86a6a328-145f-45b1-8258-ed06f5f952bd
-- title:
--   §2–§4, (1), (4), (5), Proposition 3.1 — experiments with marginal q, correlation matrices, worst-case variance, V^OPT, V^LB, IBR experiments, V^DP, V^k, f_q
-- statement:
--   This file sets up the robust correlation-design problem of Candogan, Chen and Niazadeh and the independent block randomization (IBR) experiments analysed in the paper.
--
--   **Experiments.** There are $n$ clusters. An *experiment* with marginal assignment probability $q$ is a joint law $P$ of binary assignments $Z=(Z_i)_{i\in[n]}\in\{0,1\}^n$ under which every $Z_i$ is Bernoulli$(q)$, i.e. $\mathbb P[Z_i=1]=q$ for every cluster $i$. Its *correlation matrix* is
--   $$
--   \Sigma(P)_{ik}=\frac{\mathbb E_P[Z_iZ_k]-q^2}{q(1-q)},
--   $$
--   which has unit diagonal.
--
--   **Worst-case variance and $V^{\mathrm{OPT}}$.** Given cluster sizes $w_i\ge 0$, nature chooses $y$ in the box $\times_{i\in[n]}[0,w_i]$. The worst-case variance of a matrix $S$ is $\max_{y\in\times_{i}[0,w_i]}y^\top S y$, and the robust correlation-design problem (1) is
--   $$
--   V^{\mathrm{OPT}}=\min_{P\in\mathcal P_q}\ \max_{y\in\times_{i\in[n]}[0,w_i]} y^\top\Sigma(P)y .
--   $$
--
--   **The relaxation $V^{\mathrm{LB}}$.** Let $\Re$ be the set of correlation matrices: positive semidefinite symmetric matrices with all diagonal entries equal to one. The relaxation (5) is
--   $$
--   V^{\mathrm{LB}}=\min_{\Sigma\in\Re}\ \max_{y\in\times_{i\in[n]}[0,w_i]} y^\top\Sigma y .
--   $$
--
--   **The block law of Proposition 3.1.** On $m$ clusters, with $p=\lceil qm\rceil-qm$, the law that with probability $p$ treats a uniformly random set of $\lfloor qm\rfloor$ clusters and with probability $1-p$ a uniformly random set of $\lceil qm\rceil$ clusters. When $qm$ is an integer, $p=0$ and it treats a uniformly random set of exactly $qm$ clusters.
--
--   **IBR experiments, $V^{\mathrm{DP}}$, $V^k$.** The clusters, sorted by decreasing size, are partitioned into consecutive blocks; an *IBR experiment* applies the block law independently on each block. $V^{\mathrm{DP}}$ is the worst-case variance of the optimal IBR experiment, i.e. the minimum over all partitions into consecutive blocks (the value of the dynamic program (4)). For an integer $k\ge 1$, the $k$-partition IBR experiment groups the clusters $(h-1)k+1,\dots,hk$ for $h=1,\dots,\lceil n/k\rceil$ (the last group may be smaller) and partitions each group optimally; $V^k$ is its worst-case variance. Finally $f_q(k)$ is $V^{\mathrm{OPT}}$ for $k$ clusters of size one.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Clusters are `Fin n`, 0-based (the paper's cluster $i$ is index $i-1$), and $Z_i=1$ is `z i = true`. A law is a real weight function on `Fin n → Bool` (nonnegative, total mass one, marginals $q$). The worst case is a real `sSup` of the image of the box, which for $w\ge 0$ is a nonempty compact set mapped by a continuous function, so the supremum is attained; for $w\ge0$ the value is $\ge 0$ ($y=0$). $V^{\mathrm{OPT}}$ and $V^{\mathrm{LB}}$ are real `sInf`s of sets that are nonempty (the independent law; the identity matrix) and bounded below by $0$. The partitions into consecutive blocks are Mathlib's `Composition n`, with block $j$ embedded into `Fin n` by `c.embedding j`; $V^{\mathrm{DP}}$ is an infimum over this finite nonempty type, hence a minimum. $V^k$ is the minimum of the IBR worst case over the compositions in which every multiple $hk<n$ is a block boundary (that is, the partitions refining the $k$-grouping); since the IBR worst case is the sum of the block worst cases, this minimum equals the worst case of the experiment that partitions each group optimally, as described on p. 18. The family contains the all-singletons composition, so it is nonempty. `corr` divides by $q(1-q)$; every theorem assumes $0<q\le 1/2$ (the paper's standing assumption, §2, p. 7).
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), pp. 6–19, (1), (4), (5), Proposition 3.1, §3.2 (IBR experiments), §4.1.2 (k-partition IBR experiment, f_q(k))

import Mathlib

namespace CorrClusterExp.IBR

open Matrix Finset

/-- A cluster-based experiment with marginal assignment probability `q` (§2, p. 7; §2.1, p. 8):
a law of `Z ∈ {0,1}ⁿ`, encoded as a real weight function on assignments `z : Fin n → Bool`
(`Zᵢ = 1` iff `z i = true`). It is nonnegative, has total mass one, and every cluster is
treated with probability `q`. Clusters are 0-based: the paper's cluster `i` is index `i − 1`. -/
def IsExperiment {n : ℕ} (q : ℝ) (P : (Fin n → Bool) → ℝ) : Prop :=
  (∀ z, 0 ≤ P z) ∧ ∑ z, P z = 1 ∧ ∀ i, ∑ z, (if z i = true then P z else 0) = q

/-- The correlation matrix `Σ(P)` of the assignments (p. 7): each `Zᵢ` is Bernoulli(`q`), so
`Σ(P)ᵢₖ = (E[ZᵢZₖ] − q²)/(q(1 − q))`. -/
noncomputable def corr {n : ℕ} (q : ℝ) (P : (Fin n → Bool) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => ((∑ z, if z i = true ∧ z k = true then P z else 0) - q ^ 2) / (q * (1 - q))

/-- The uncertainty set `×_{i∈[n]} [0, wᵢ]` (p. 7). -/
def box {n : ℕ} (w : Fin n → ℝ) : Set (Fin n → ℝ) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ w i}

/-- The worst-case variance `max_{y ∈ ×[0,wᵢ]} yᵀ S y` over the whole box (p. 7, (1)). -/
noncomputable def worstCase {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : ℝ :=
  sSup ((fun y => y ⬝ᵥ (S *ᵥ y)) '' box w)

/-- `V^OPT`, the optimal value of the robust correlation-design problem (1), p. 7. -/
noncomputable def VOPT {n : ℕ} (q : ℝ) (w : Fin n → ℝ) : ℝ :=
  sInf ((fun P => worstCase (corr q P) w) '' {P | IsExperiment q P})

/-- The set `ℜ` of correlation matrices (§1.3, p. 6): positive semidefinite (in particular
symmetric) with unit diagonal. -/
def IsCorrMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  S.PosSemidef ∧ ∀ i, S i i = 1

/-- `V^LB`, the optimal value of the relaxation (5), p. 17. -/
noncomputable def VLB {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  sInf ((fun S => worstCase S w) '' {S | IsCorrMatrix S})

/-- The law of Proposition 3.1 on `m` clusters (p. 13): with probability `p = ⌈qm⌉ − qm` a
uniformly random `⌊qm⌋`-subset is treated, with probability `1 − p` a uniformly random
`⌈qm⌉`-subset. When `qm ∈ ℕ`, `p = 0` and this is the uniform `qm`-subset of case 1. -/
noncomputable def fracLaw (q : ℝ) (m : ℕ) (z : Fin m → Bool) : ℝ :=
  let s := (univ.filter fun i => z i = true).card
  let p : ℝ := (⌈q * m⌉₊ : ℝ) - q * m
  (if s = ⌊q * m⌋₊ then p / (m.choose ⌊q * m⌋₊ : ℝ) else 0) +
  (if s = ⌈q * m⌉₊ then (1 - p) / (m.choose ⌈q * m⌉₊ : ℝ) else 0)

/-- The IBR experiment (§3.2, p. 14) of the partition of the sorted clusters into the
consecutive blocks of the composition `c`: the law of Proposition 3.1 independently on each
block. -/
noncomputable def ibrLaw {n : ℕ} (q : ℝ) (c : Composition n) (z : Fin n → Bool) : ℝ :=
  ∏ j : Fin c.length, fracLaw q (c.blocksFun j) (fun i => z (c.embedding j i))

/-- The worst-case variance of the IBR experiment with blocks `c`. -/
noncomputable def VIBR {n : ℕ} (q : ℝ) (w : Fin n → ℝ) (c : Composition n) : ℝ :=
  worstCase (corr q (ibrLaw q c)) w

/-- `V^DP`, the worst-case variance of the optimal IBR experiment (§3.2, p. 16): the minimum
over all partitions of the sorted clusters into consecutive blocks (a finite nonempty family). -/
noncomputable def VDP {n : ℕ} (q : ℝ) (w : Fin n → ℝ) : ℝ :=
  ⨅ c : Composition n, VIBR q w c

/-- The blocks `c` refine the `k`-grouping of §4.1.2 (p. 18): every multiple `hk < n` (the start
of a group, 0-based) is a block boundary. -/
def KGrouped {n : ℕ} (k : ℕ) (c : Composition n) : Prop :=
  ∀ h : ℕ, h * k < n → ∃ j : ℕ, c.sizeUpTo j = h * k

/-- `V^k`, the worst-case variance of the `k`-partition IBR experiment (§4.1.2, p. 18): the
minimum of the IBR worst case over the partitions refining the `k`-grouping (a finite nonempty
family: it contains `Composition.ones n`). -/
noncomputable def Vk {n : ℕ} (q : ℝ) (k : ℕ) (w : Fin n → ℝ) : ℝ :=
  ⨅ c : {c : Composition n // KGrouped k c}, VIBR q w c.1

/-- `f_q(k)`, the optimal value of (1) for `k` clusters of size one (p. 19). -/
noncomputable def fq (q : ℝ) (k : ℕ) : ℝ :=
  VOPT q (fun _ : Fin k => (1 : ℝ))

end CorrClusterExp.IBR


