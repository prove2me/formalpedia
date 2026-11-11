-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_Clusters
-- name    : CaiFourierSparse_Learning_Clusters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:14:41.658866+00:00
-- url     : https://prove2.me/theorems/a33c7c5f-3dbc-4334-aa4a-4d90a6053bc0
-- title:
--   Clusters of a Fourier-sparse signal (Algorithm 2), their bands (73), and multiband signals
-- statement:
--   A **cluster** is a set $C$ of labelled terms of $x$. $\operatorname{dist}(C,C')=\min_{i\in C,j\in C'}|f_i-f_j|$ (`clusterDist`), $\operatorname{range}(C)=[\min_{C}f,\max_Cf]$ (`cLo`, `cHi`) with length $|\operatorname{range}(C)|$ (`rangeLen`), and $|C|$ is the number of terms. $d_{\min}=C_Hk\log^{1.5}(k/\varepsilon)/\varepsilon$ (`dMin`). **Algorithm 2** starts from the $k$ singletons (`singletons`) and, while two distinct clusters satisfy $\operatorname{dist}(C_i,C_j)\le\min\{d_{\min}\min\{|C_i|,|C_j|\},2\Delta_{k,\varepsilon}\}$ (`Violates`), merges into one cluster all clusters having a frequency between them, i.e. in $[\min(\min_{C_i}f,\min_{C_j}f),\max(\max_{C_i}f,\max_{C_j}f)]$ (`Between`, `Alg2Step`). `IsAlg2Output` says that a family of clusters is reached by such merges and no pair violates the condition; every order of merges is allowed. `IsClusterPartition` says a family partitions the terms into nonempty disjoint clusters.
--
--   $\theta_s$ is the smallest positive integer $n$ with $\Delta_{n,\varepsilon n/k}\ge\Delta_{k,\varepsilon}$ (`thetaS`), and the **band** of a cluster is, by eq. (73), $I_C=[\min_Cf-\rho_C,\max_Cf+\rho_C]$ with $\rho_C=\Delta_{|C|,\varepsilon|C|/k}$ if $|C|<\theta_s$ and $\rho_C=\Delta_{k,\varepsilon}$ otherwise (`bandRadius`, `band`).
--
--   A **multiband signal** with bands $I_1,\dots,I_n$ is a $z\in L^2(\mathbb R)$ whose Fourier transform (Plancherel extension, kernel $e^{-2\pi i\xi t}$; `l2ft`) vanishes almost everywhere outside $I_1\cup\dots\cup I_n$ (`IsMultiband`). Clusters and bands are analysis objects of the hidden signal; no algorithm receives them.
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), §7, Algorithm 2, eq. (73), Lemma 7.2, Claim 7.3, Theorem 7.1, printed pp. 34–35 (PDF pp. 36–37)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Filter

namespace CaiFourierSparse.Learning

open MeasureTheory
open scoped ENNReal

/-! # Clusters of a Fourier-sparse signal (Algorithm 2), their bands (73), and multiband signals
(Cai–Chen–Shao–Wang, §7, Algorithm 2, Lemma 7.2, Claim 7.3, Theorem 7.1, eq. (73))

A cluster is a set of labelled terms `C ⊆ Fin k` of `x = ∑_j α_j e^{2π i f_j t}` (so repeated
frequencies and cancelling amplitudes stay separate terms). `dist(C, C') = min |f - f'|` over
pairs of terms, `range(C) = [min_{j∈C} f_j, max_{j∈C} f_j]` and `|C|` is the number of terms.
Algorithm 2 starts from the `k` singletons and, while two clusters satisfy
`dist(C_i, C_j) ≤ min{d_min · min{|C_i|, |C_j|}, 2Δ_{k,ε}}`, merges them together with every
cluster whose frequencies lie between them. The pair merged at each step is not fixed by the
page; `IsAlg2Output` admits every order of merges. Clusters and bands are analysis objects of
the hidden signal; no algorithm receives them. -/

/-- `dist(A, B) = min_{i ∈ A, j ∈ B} |f_i - f_j|` (`0` if a cluster is empty). -/
noncomputable def clusterDist {k : ℕ} (f : Fin k → ℝ) (A B : Finset (Fin k)) : ℝ :=
  if h : (A ×ˢ B).Nonempty then (A ×ˢ B).inf' h (fun p => |f p.1 - f p.2|) else 0

/-- `min_{j ∈ A} f_j` (`0` for an empty cluster). -/
noncomputable def cLo {k : ℕ} (f : Fin k → ℝ) (A : Finset (Fin k)) : ℝ :=
  if h : A.Nonempty then A.inf' h f else 0

/-- `max_{j ∈ A} f_j` (`0` for an empty cluster). -/
noncomputable def cHi {k : ℕ} (f : Fin k → ℝ) (A : Finset (Fin k)) : ℝ :=
  if h : A.Nonempty then A.sup' h f else 0

/-- `|range(A)| = max_{j ∈ A} f_j - min_{j ∈ A} f_j`. -/
noncomputable def rangeLen {k : ℕ} (f : Fin k → ℝ) (A : Finset (Fin k)) : ℝ :=
  cHi f A - cLo f A

/-- `d_min = C_H · k · log^{1.5}(k/ε) / ε` (Algorithm 2, Lemma 7.2; base-2 logarithm). -/
noncomputable def dMin (C k : ℕ) (ε : ℝ) : ℝ :=
  constCH C * k * Real.logb 2 ((k : ℝ) / ε) ^ (3 / 2 : ℝ) / ε

/-- The merging condition of Algorithm 2:
`dist(A, B) ≤ min{d_min · min{|A|, |B|}, 2Δ_{k,ε}}` for two distinct clusters. -/
def Violates {k : ℕ} (C : ℕ) (ε : ℝ) (f : Fin k → ℝ) (A B : Finset (Fin k)) : Prop :=
  A ≠ B ∧ clusterDist f A B ≤ min (dMin C k ε * (min A.card B.card : ℕ)) (2 * filterDelta C k ε)

/-- A cluster `D` lies between `A` and `B`: one of its frequencies lies in
`[min(range A ∪ range B), max(range A ∪ range B)]`. -/
def Between {k : ℕ} (f : Fin k → ℝ) (A B D : Finset (Fin k)) : Prop :=
  ∃ j ∈ D, min (cLo f A) (cLo f B) ≤ f j ∧ f j ≤ max (cHi f A) (cHi f B)

open Classical in
/-- One iteration of the while loop of Algorithm 2: for a violating pair `A, B`, merge every
cluster lying between them (including `A` and `B`) into one cluster. -/
def Alg2Step {k : ℕ} (C : ℕ) (ε : ℝ) (f : Fin k → ℝ) (P Q : Finset (Finset (Fin k))) : Prop :=
  ∃ A ∈ P, ∃ B ∈ P, Violates C ε f A B ∧
    Q = insert ((P.filter (Between f A B)).biUnion id) (P.filter (fun D => ¬ Between f A B D))

/-- The `k` initial singleton clusters `{(f_i, α_i)}`. -/
def singletons (k : ℕ) : Finset (Finset (Fin k)) := Finset.univ.image fun j => {j}

/-- `P` is a set of clusters returned by Algorithm 2 (`PartitionClusters`) on the frequencies
`f` with parameters `k, ε` and filter constant `C`: it is reached from the singletons by merge
steps, and no pair violates the separation condition. Every order of merges is allowed. -/
def IsAlg2Output {k : ℕ} (C : ℕ) (ε : ℝ) (f : Fin k → ℝ) (P : Finset (Finset (Fin k))) : Prop :=
  Relation.ReflTransGen (Alg2Step C ε f) (singletons k) P ∧
    ∀ A ∈ P, ∀ B ∈ P, ¬ Violates C ε f A B

/-- `P` partitions the `k` terms into nonempty, pairwise disjoint clusters. -/
def IsClusterPartition {k : ℕ} (P : Finset (Finset (Fin k))) : Prop :=
  (∀ A ∈ P, A.Nonempty) ∧ (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧ ∀ j, ∃ A ∈ P, j ∈ A

open Classical in
/-- `θ_s`: the smallest positive integer `n` with `Δ_{n, εn/k} ≥ Δ_{k,ε}` (proof of Theorem 7.1;
`n = k` qualifies, so it exists for `k ≥ 1`). -/
noncomputable def thetaS (C k : ℕ) (ε : ℝ) : ℕ :=
  if h : ∃ n : ℕ, 0 < n ∧ filterDelta C k ε ≤ filterDelta C n (ε * n / k) then Nat.find h
  else 0

/-- The radius of the band of a cluster of size `|A|`, eq. (73): `Δ_{|A|, ε|A|/k}` if
`|A| < θ_s`, and `Δ_{k,ε}` otherwise. -/
noncomputable def bandRadius (C k : ℕ) (ε : ℝ) (A : Finset (Fin k)) : ℝ :=
  if A.card < thetaS C k ε then filterDelta C A.card (ε * A.card / k) else filterDelta C k ε

/-- The band `I_A = [min_{A} f - r_A, max_{A} f + r_A]` of a cluster, eq. (73). -/
noncomputable def band {k : ℕ} (C : ℕ) (ε : ℝ) (f : Fin k → ℝ) (A : Finset (Fin k)) : Set ℝ :=
  Set.Icc (cLo f A - bandRadius C k ε A) (cHi f A + bandRadius C k ε A)

/-- The Fourier transform of a square-integrable `z : ℝ → ℂ` (Plancherel extension, kernel
`e^{-2π i ξ t}`), as an almost-everywhere defined function. -/
noncomputable def l2ft {z : ℝ → ℂ} (h : MemLp z 2 volume) : ℝ → ℂ :=
  ⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.toLp z))

/-- `z` is a multiband signal with bands `I_1, …, I_n` (pairs of endpoints): `z ∈ L²(ℝ)` and its
Fourier transform vanishes almost everywhere outside `I_1 ∪ ⋯ ∪ I_n`. -/
def IsMultiband (z : ℝ → ℂ) (bands : List (ℝ × ℝ)) : Prop :=
  ∃ h : MemLp z 2 volume, ∀ᵐ ξ ∂volume, (∀ I ∈ bands, ξ ∉ Set.Icc I.1 I.2) → l2ft h ξ = 0

end CaiFourierSparse.Learning


