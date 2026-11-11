-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_Prelim
-- name    : PostedPriceLimits_FullRevelation_Prelim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:22.301881+00:00
-- url     : https://prove2.me/theorems/994ccad6-3e4e-49fa-9833-f6dc4af10df6
-- title:
--   Averages, Bernoulli subsets and the geometric rank partitions $\mathcal K_s$ (§§3.2–3.3, §5.2)
-- statement:
--   1. **Averages** (§3.2). For a finite set $S$, $\mathrm{Avg}[f\mid S]=\frac1{|S|}\sum_{x\in S}f(x)$, with $\mathrm{Avg}[f\mid\varnothing]=0$.
--   2. **Bernoulli subsets.** A random subset $S\subseteq\Omega$ that contains each $x$ independently with probability $q\in[0,1]$ is realised as $S=\{x: U_x<q\}$ for independent uniform labels $U_x\in[0,1]$; the label law is the product of uniform laws on $[0,1]$.
--   3. **Geometric partition** (Definition 3.12). For an interval $K\subseteq[\kappa]=\{1,\dots,\kappa\}$, $\mathcal L(K)$ partitions $K$ into intervals of sizes $1,2,4,8,\dots$ starting from the right, the leftmost interval possibly truncated; for example $\mathcal L([30,80])=\{[30,49],(49,65],(65,73],(73,77],(77,79],(79,80]\}$. For a partition $\mathcal K$ of $[\kappa]$ into intervals, $\mathcal L(\mathcal K)=\bigcup_{K\in\mathcal K}\mathcal L(K)$.
--   4. **Rank partitions** (Definition 3.13). $\mathcal K_s=\mathcal L^s(\{[\kappa]\})$ for $s\in\mathbb Z_+$; $\mathcal K(k)$ is the part of $\mathcal K$ containing $k$ (Definition 3.11).
--   5. **Consecutive intervals.** Two nonempty intervals $C,D$ are consecutive when $D$ begins immediately after $C$ ends.
--   6. **Thresholds** (§5.2). $\varphi_s(k)=\min\mathcal K_s(k)-1$.
--
--   The partitions $\mathcal K_0,\mathcal K_1,\dots,\mathcal K_n$ are the rank-information schedule of the lower bound.
--
--   **Formalization Note** The piece of $\mathcal L(K)$ containing $k$ is the set of $j\in K$ with $\lfloor\log_2(\max K-j+1)\rfloor=\lfloor\log_2(\max K-k+1)\rfloor$. The trivial partition of $[\kappa]$ keeps only nonempty parts, so for $\kappa=0$ it is the empty partition.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), §3.2, p.6 (PDF 7); Definitions 3.11–3.13, p.7 (PDF 8); §5.2, p.16 (PDF 17); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib

open MeasureTheory

namespace PostedPriceLimits.FullRevelation

/-! ## Averages, Bernoulli subsets and geometric partitions (§§3.2–3.3) -/

/-- `Avg[f | S] = (1/|S|) ∑_{x ∈ S} f(x)`, with `Avg[f | ∅] = 0` (§3.2). -/
noncomputable def avg {α : Type*} (S : Finset α) (f : α → ℝ) : ℝ :=
  if S.card = 0 then 0 else (∑ x ∈ S, f x) / S.card

/-- The uniform law on `[0, 1]`, the primitive source of randomness used below. -/
noncomputable def unitUniform : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The law of the independent uniform labels `U : Ω → [0,1]` used to sample a random subset
`S = {x | U x < q}`, which contains each `x ∈ Ω` independently with probability `q ∈ [0,1]`. -/
noncomputable def subsetLabelLaw (Ω : Type*) [Fintype Ω] : Measure (Ω → ℝ) :=
  Measure.pi (fun _ : Ω => unitUniform)

/-- The random subset `{x | U x < q}` determined by the labels `U` and the inclusion
probability `q`. -/
noncomputable def sampledSubset {Ω : Type*} [Fintype Ω] (q : ℝ) (U : Ω → ℝ) : Finset Ω :=
  Finset.univ.filter (fun x => U x < q)

/-- `[κ] = {1, …, κ}`. -/
def rankRange (κ : ℕ) : Finset ℕ := Finset.Icc 1 κ

/-- For a finite interval `K ⊆ ℕ` and `k ∈ K`, the piece of the geometric partition `L(K)`
containing `k`: counting from the right end `max K`, the pieces have sizes `1, 2, 4, …`, the
leftmost one possibly truncated. Concretely `k, k'` share a piece iff
`⌊log₂(max K − k + 1)⌋ = ⌊log₂(max K − k' + 1)⌋`. -/
def geomPiece (K : Finset ℕ) (k : ℕ) : Finset ℕ :=
  K.filter (fun j => Nat.log 2 (K.sup id - j + 1) = Nat.log 2 (K.sup id - k + 1))

/-- Definition 3.12: the geometric partition `L(K)` of an interval `K`.
E.g. `L([30,80]) = {[30,49], (49,65], (65,73], (73,77], (77,79], (79,80]}`. -/
def geomPartition (K : Finset ℕ) : Finset (Finset ℕ) :=
  K.image (geomPiece K)

/-- Definition 3.12: for a partition `𝒦` of `[κ]` into intervals, `L(𝒦) = ⋃_{K ∈ 𝒦} L(K)`. -/
def refinePartition (𝒦 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  𝒦.biUnion geomPartition

/-- Definition 3.13: `𝒦_s = L^s({[κ]})`. At `κ = 0` use the empty partition of `∅`:
this corrects the source's literal `{∅}`, whose cardinality contradicts Lemma 3.14
at `κ = s = 0`. No positive-rank instance changes. -/
def rankPartition (κ s : ℕ) : Finset (Finset ℕ) :=
  refinePartition^[s] (({rankRange κ} : Finset (Finset ℕ)).filter (fun K => K.Nonempty))

/-- Definition 3.11: `𝒦(k)`, the part of the partition `𝒦` containing `k` (the union of the
parts containing `k`, which is that part since the parts are disjoint). -/
def partOf (𝒦 : Finset (Finset ℕ)) (k : ℕ) : Finset ℕ :=
  (𝒦.filter (fun K => k ∈ K)).sup id

/-- `C, D` are consecutive intervals: both nonempty and `D` starts right after `C` ends. -/
def ConsecutiveIntervals (C D : Finset ℕ) : Prop :=
  ∃ c ∈ C, c + 1 ∈ D ∧ (∀ x ∈ C, x ≤ c) ∧ (∀ y ∈ D, c + 1 ≤ y)

/-- §5.2: `φ_s(k) = min 𝒦_s(k) − 1`. -/
noncomputable def phi (κ s k : ℕ) : ℕ :=
  sInf (↑(partOf (rankPartition κ s) k) : Set ℕ) - 1

end PostedPriceLimits.FullRevelation


