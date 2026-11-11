-- Prove2me | Definitions.Def_DoubleCorrRME_Model
-- name    : DoubleCorrRME_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:25.888907+00:00
-- url     : https://prove2.me/theorems/83523c7f-ff60-4f18-8560-648cc564f51f
-- title:
--   Points, laws with $\Sigma\preceq\Lambda I_d$, the double-corruption and sample adversaries, multiset statistics
-- statement:
--   Points live in $\mathbb R^d$ with the Euclidean norm. A dataset of Problem 1 is a family $z=(z_{i,j})_{i\in[N],j\in[n]}$ of $Nn$ points ($N$ users with $n$ samples each).
--
--   A probability law $P$ on $\mathbb R^d$ has **covariance at most $\Lambda I_d$** if it has a finite second moment and, with $\mu=\mathbb E_P[x]$,
--
--   $$\mathbb E_P\langle u,x-\mu\rangle^2\le\Lambda\|u\|_2^2\qquad\text{for all }u\in\mathbb R^d .$$
--
--   The law of Problem 1 is the case $\Lambda=1$, and the clean dataset is $Nn$ i.i.d. draws from $P$.
--
--   **Strong $(\varepsilon,\alpha)$-double corruption** (Definition 1.1): a dataset $x$ is an $(\varepsilon,\alpha)$-double corruption of $z$ if there is a set $B\subseteq[N]$ of at most $\varepsilon N$ users such that at most $\alpha Nn$ points $x_{i,j}$ with $i\notin B$ differ from $z_{i,j}$; the points of users in $B$ are arbitrary. An adversary is any map $A$ of the whole clean dataset such that $A(z)$ is such a corruption of $z$ for every $z$. The adversary of Problem 2 replaces at most $\alpha n$ of $n$ samples.
--
--   For a multiset $S=\{z_k:k\in I\}$ given by a family and an index set: $\mu_S=\frac1{|S|}\sum_{k\in I}z_k$, $M_S(\nu)=\frac1{|S|}\sum_{k\in I}(z_k-\nu)(z_k-\nu)^\top$ and $\Sigma_S=M_S(\mu_S)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The finite second moment (`MemLp id 2`) is required: without it Lean's integral is $0$ and the covariance bound would hold vacuously. Adversaries need not be measurable. Multisets are index sets, so repeated values stay separate elements.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Definition 1.1 and Problem 1, p.1 (PDF p.2); notation, p.4 (PDF p.5); Problem 2, p.62 (PDF p.63)

import Mathlib

open MeasureTheory

namespace DoubleCorrRME

/-!
# Points, laws, multiset statistics, Problem 1 and the two adversaries

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…): Definition 1.1 and
Problem 1, p.1 (PDF p.2); notation, p.4 (PDF p.5); Problem 2, p.62 (PDF p.63).

**Formalization Note.**
* Points live in `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the Euclidean norm `‖·‖₂`.
* Indices are 0-based: the paper's `[N]`, `[n]` are `Fin N`, `Fin n`.
* A finite multiset `S = {z_k : k ∈ ℐ}` is a family `z : ι → ℝ^d` together with a `Finset` `ℐ` of
  indices. Equal values at different indices stay separate elements, which is the multiset meaning;
  `µ_S`, `M_S(ν)`, `Σ_S` are averages over `ℐ`.
* A law `P` with "mean `µ` and covariance `Σ ⪯ I_d`" is a probability measure with finite second
  moment (`MemLp id 2`) and `E⟨u, x − µ⟩² ≤ ‖u‖²` for all `u`, where `µ := ∫ x dP`. Without
  `MemLp id 2` Lean's integral of a non-integrable function is `0` and the covariance bound would
  hold vacuously.
* The adversaries are arbitrary maps of the whole clean dataset, measurable or not ("may examine the
  entire dataset"). A randomized adversary is a mixture of such maps.
-/

/-- A point of `ℝ^d` with the Euclidean norm. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The rank-one matrix `v v⊤`. -/
def outer {d : ℕ} (v : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.vecMulVec (fun a => v a) (fun a => v a)

/-- The quadratic form `vᵀ A v`. -/
def quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : Vec d) : ℝ :=
  ∑ a, ∑ b, v a * A a b * v b

/-- The Frobenius inner product `⟨A, B⟩ = tr(Aᵀ B) = ∑_{a,b} A_{ab} B_{ab}`. -/
def frobInner {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ a, ∑ b, A a b * B a b

/-- The population mean `µ := E_{x∼P}[x]` (Bochner integral). -/
noncomputable def popMean {d : ℕ} (P : Measure (Vec d)) : Vec d := ∫ x, x ∂P

/-- Covariance bound `Σ ⪯ Λ I_d` for a law `P` (a probability measure, supplied as an instance where
it is used): `P` has a finite second moment and `E⟨u, x − µ⟩² ≤ Λ‖u‖²` for all `u`. -/
def IsCovLe {d : ℕ} (Λ : ℝ) (P : Measure (Vec d)) : Prop :=
  MemLp id 2 P ∧ ∀ u : Vec d, ∫ x, (inner ℝ u (x - popMean P)) ^ 2 ∂P ≤ Λ * ‖u‖ ^ 2

/-- The law of Problem 1: finite second moment, mean `µ` and covariance `Σ ⪯ I_d`. -/
def IsBoundedCovLaw {d : ℕ} (P : Measure (Vec d)) : Prop := IsCovLe 1 P

/-- The law of the clean dataset `{z_{i,j}}` of Problem 1: all `Nn` samples i.i.d. from `P`. -/
noncomputable def cleanLaw (N n : ℕ) {d : ℕ} (P : Measure (Vec d)) :
    Measure (Fin N → Fin n → Vec d) :=
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin n => P

/-- The corruption pattern of Definition 1.1 between a clean dataset `z` and an observed dataset `x`:
some set `B` of at most `εN` users, and at most `αNn` changed points among the users outside `B`
(the points of users in `B` are arbitrary). -/
def IsDoubleCorruption {N n d : ℕ} (ε α : ℝ) (z x : Fin N → Fin n → Vec d) : Prop :=
  ∃ B : Finset (Fin N), (B.card : ℝ) ≤ ε * N ∧
    ((Finset.univ.filter fun k : Fin N × Fin n => k.1 ∉ B ∧ x k.1 k.2 ≠ z k.1 k.2).card : ℝ) ≤
      α * N * n

/-- A strong `(ε, α)`-double-corruption adversary (Definition 1.1): any map of the whole clean
dataset whose output is, for every clean dataset, an `(ε, α)`-double corruption of it. -/
def IsDoubleAdversary {N n d : ℕ} (ε α : ℝ)
    (A : (Fin N → Fin n → Vec d) → (Fin N → Fin n → Vec d)) : Prop :=
  ∀ z, IsDoubleCorruption ε α z (A z)

/-- The adversary of Problem 2: after inspecting the samples it replaces at most `αn` of them. -/
def IsSampleAdversary {n d : ℕ} (α : ℝ) (A : (Fin n → Vec d) → (Fin n → Vec d)) : Prop :=
  ∀ X, ((Finset.univ.filter fun k => A X k ≠ X k).card : ℝ) ≤ α * n

/-- `µ_S := (1/|S|) ∑_{x∈S} x` for the multiset `S = {z_k : k ∈ I}` (p.4). -/
noncomputable def meanOn {ι : Type*} {d : ℕ} (z : ι → Vec d) (I : Finset ι) : Vec d :=
  ((I.card : ℝ))⁻¹ • ∑ k ∈ I, z k

/-- `M_S(ν) := (1/|S|) ∑_{x∈S} (x − ν)(x − ν)⊤` for `S = {z_k : k ∈ I}` (p.4). -/
noncomputable def momentOn {ι : Type*} {d : ℕ} (z : ι → Vec d) (I : Finset ι) (ν : Vec d) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((I.card : ℝ))⁻¹ • ∑ k ∈ I, outer (z k - ν)

/-- `Σ_S := (1/|S|) ∑_{x∈S} (x − µ_S)(x − µ_S)⊤ = M_S(µ_S)` (p.4). -/
noncomputable def covOn {ι : Type*} {d : ℕ} (z : ι → Vec d) (I : Finset ι) :
    Matrix (Fin d) (Fin d) ℝ :=
  momentOn z I (meanOn z I)

end DoubleCorrRME


