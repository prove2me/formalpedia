-- Prove2me | Definitions.Def_HawkesParking_Spine_Model
-- name    : HawkesParking_Spine_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:20.933806+00:00
-- url     : https://prove2.me/theorems/e3884415-cde6-4554-a4c4-5567a794d9b9
-- title:
--   Definition 1, eqs. (3), (6), §2.2, Definition 2, Lemma 2, eq. (10) — Hawkes cluster law, compensator, polytopes, Dyck paths, parking functions
-- statement:
--   This file sets up the objects of A. Daw, *Conditional Uniformity and Hawkes Processes*: the cluster of a Hawkes process, its compensator points, the polytopes on which they live, Dyck paths and parking functions.
--
--   **Kernel.** An excitation kernel is a function $g:\mathbb R_+\to\mathbb R_+$ with
--   $$\rho=\int_0^\infty g(t)\,dt,\qquad G(x)=\int_0^x g(u)\,du .$$
--   The standing assumptions (`IsKernel g`) are: $g$ is measurable, $g(t)\ge 0$ for $t\ge 0$, $g$ is integrable on $(0,\infty)$, and $0<\rho<1$.
--
--   **Cluster.** A Hawkes cluster starts with an event at $A_0=0$; each event at $A_i$ excites the intensity by $g(t-A_i)$, so before the $j$-th offspring event the intensity is $\lambda(A_j-)=\sum_{i=0}^{j-1} g(A_j-A_i)$ (eq. (3)). For $k\in\mathbb N$, the measure `clusterLaw g k` on $\mathbb R^k$ is the joint law of the event $\{N=k+1\}$ and the offspring epochs $(A_1,\dots,A_k)$:
--   $$P\big(N=k+1,\ (A_1,\dots,A_k)\in da\big)=e^{-(k+1)\rho}\prod_{j=1}^k\Big(\sum_{i=0}^{j-1} g(a_j-a_i)\Big)\,\mathbf 1\{0=a_0<a_1<\dots<a_k\}\,da .$$
--   Its total mass is $P(N=k+1)$.
--
--   **Compensator.** The compensator points are $\Lambda_j=\sum_{i=0}^{j-1}G(A_j-A_i)$ (eq. (6)). The measure `condCompensatorLaw g k` is the law of $(\Lambda_1,\dots,\Lambda_k)$ given $N=k+1$: the image of the cluster law under the compensator map, divided by $P(N=k+1)$.
--
--   **Polytopes.** With $\mathbb R_+=[0,\infty)$,
--   $$\mathcal P_k=\{x\in\mathbb R^k_+ : x_i<i\rho\ \forall i,\ x_1<x_2<\dots<x_k\},$$
--   and $\bar{\mathcal P}_k$ is $\mathcal P_k$ with $\rho=1$. $\mathrm{Uni}(S)$ is Lebesgue measure on $S$ normalized by the volume of $S$.
--
--   **Dyck paths and regions.** $\mathsf D_k$ is the set of non-decreasing integer vectors $d$ with $1\le d_i\le i$ (the paper's encoding of a $k$-step Dyck path, p. 8). For $d\in\mathsf D_k$, the region of eq. (10) is
--   $$\bar{\mathcal P}_{k,d}=\{x\in\mathbb R^k_+ : d_i-1\le x_i<d_i\ \forall i,\ x_1<\dots<x_k\},$$
--   and $\kappa_i(d)=|\{j: d_j=i\}|$.
--
--   **Parking functions** (Definition 2). $\pi\in\mathbb Z_+^k$ is a parking function of length $k$ if its increasing rearrangement $\vec\pi$ satisfies $\vec\pi_{(i)}\le i$ for each $i$. $\mathsf{PF}_k$ is the finite set of them.
--
--   **The parking-spine law.** `spineLaw ρ k` is the law of $\rho\cdot\big((\pi-U)_{(1)},\dots,(\pi-U)_{(k)}\big)$, where $\pi$ is uniform on $\mathsf{PF}_k$, $U$ is uniform on $(0,1)^k$ and independent of $\pi$, and $(\cdot)_{(i)}$ are order statistics.
--
--   These are the objects of the mission's goal (Theorem 1) and of every milestone.
--
--   **Formalization Note.** (1) The cluster is defined by its likelihood (Janossy density) on the ordered epochs, the classical form of the law of a point process with conditional intensity (3) on $[0,\infty)$ with exactly $k$ points after $A_0=0$: $\prod_j\lambda(A_j-)\cdot\exp(-\int_0^\infty\lambda_t\,dt)$, where $\int_0^\infty\lambda_t\,dt=(k+1)\rho$. Mathlib has no point processes with compensators, and the step from the intensity to this likelihood is classical (the paper cites Brown et al. 2002, eq. (2.14)), not part of this paper; the proof of Lemma 2 (p. 11) works with the same object. The cluster is *not* defined in compensator coordinates, so that Lemma 2 is a theorem. (2) Measurability of $g$ and $\rho>0$ are added to the page's assumptions: $g$ is integrated, and for $\rho=0$ the event $N=k+1\ge 2$ is null and Lemma 2's $1/\rho$ is undefined. (3) $G$ is computed with $g$ extended by zero to $(-\infty,0]$; this changes nothing for $x\ge 0$, the only arguments the paper uses. (4) Vectors are 0-indexed: the paper's coordinate $i\in\{1,\dots,k\}$ is Lean's `i : Fin k` with value `i + 1`; $A_0=0$ is prepended with `Fin.cons`. (5) Parking-function values are drawn from $\{1,\dots,k\}$; this loses nothing, since $\vec\pi_{(k)}\le k$ bounds every value. (6) The parking-spine law is written as the mixture over $\pi$ of the image of the uniform measure on $(0,1)^k$, which avoids a measurable structure on $\mathbb N^k$. (7) Order statistics are `v ∘ Tuple.sort v`. (8) "$x_i<x_{i+1}$ for $1\le i\le k-1$" is `StrictMono x`.
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, pp. 6–10 and 13, §2.1 and Definition 1 (eq. (3)), §2.2 and Definition 2 (pp. 8), eq. (6) (p. 10), Lemma 2 (polytope P_k, p. 10), unit polytope and eq. (10) (p. 13)

import Mathlib

namespace HawkesParking.Spine

open MeasureTheory

/-- `ρ = ∫_0^∞ g(t) dt`, the mean number of direct offspring of an event (Definition 1, p. 7). -/
noncomputable def rho (g : ℝ → ℝ) : ℝ := ∫ t in Set.Ioi 0, g t

/-- `G(x) = ∫_0^x g(u) du` (p. 9). The kernel is only data on `(0, ∞)`, so it is extended by
zero to the negative half-line; for `x ≥ 0` this is exactly `∫_0^x g`, and `G(x) = 0` for `x < 0`. -/
noncomputable def bigG (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, (Set.Ioi (0 : ℝ)).indicator g u

/-- Standing assumptions on the excitation kernel `g : ℝ₊ → ℝ₊` (§2.1, p. 6, and Definition 1,
p. 7): nonnegative on `[0, ∞)`, integrable there with `ρ < 1`. Measurability and `0 < ρ` are
added (disclosed in the natural-language statement). -/
structure IsKernel (g : ℝ → ℝ) : Prop where
  measurable : Measurable g
  nonneg : ∀ t, 0 ≤ t → 0 ≤ g t
  integrable : IntegrableOn g (Set.Ioi 0)
  rho_pos : 0 < rho g
  rho_lt_one : rho g < 1

/-- The epoch vector `(A₀, A₁, …, A_k)` with `A₀ = 0`, from `a = (A₁, …, A_k)`. -/
def withZero {k : ℕ} (a : Fin k → ℝ) : Fin (k + 1) → ℝ := Fin.cons 0 a

/-- Ordered epochs: `0 = A₀ < A₁ < ⋯ < A_k`. -/
def orderedEpochs (k : ℕ) : Set (Fin k → ℝ) := {a | StrictMono (withZero a)}

/-- The intensity just before the `(j+1)`-st offspring epoch, eq. (3):
`λ(A_{j+1}−) = ∑_{i=0}^{j} g(A_{j+1} − A_i)` (Lean index `j : Fin k`, paper index `j + 1`). -/
noncomputable def preIntensity (g : ℝ → ℝ) {k : ℕ} (a : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ i ∈ Finset.Iio j.succ, g (withZero a j.succ - withZero a i)

/-- The size-`(k+1)` cluster law `P(N = k + 1, (A₁, …, A_k) ∈ ·)`, given by the likelihood
(Janossy density) of the point process with conditional intensity (3) on `[0, ∞)`:
`e^{-(k+1)ρ} ∏_{j=1}^{k} λ(A_j−)` on ordered epochs. -/
noncomputable def clusterLaw (g : ℝ → ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  (volume.restrict (orderedEpochs k)).withDensity fun a =>
    ENNReal.ofReal (Real.exp (-((k + 1 : ℝ) * rho g)) * ∏ j, preIntensity g a j)

/-- The compensator points, eq. (6): `Λ_j = ∑_{i=0}^{j-1} G(A_j − A_i)` (Lean index `j : Fin k`,
paper index `j + 1`). -/
noncomputable def compensator (g : ℝ → ℝ) {k : ℕ} (a : Fin k → ℝ) : Fin k → ℝ :=
  fun j => ∑ i ∈ Finset.Iio j.succ, bigG g (withZero a j.succ - withZero a i)

/-- The conditional law of `(Λ₁, …, Λ_k)` given `N = k + 1`. -/
noncomputable def condCompensatorLaw (g : ℝ → ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  (clusterLaw g k Set.univ)⁻¹ • (clusterLaw g k).map (compensator g)

/-- The uniform distribution `Uni(S)` on a set `S ⊆ ℝ^k`. -/
noncomputable def unif {k : ℕ} (S : Set (Fin k → ℝ)) : Measure (Fin k → ℝ) :=
  (volume S)⁻¹ • volume.restrict S

/-- The polytope `P_k = {x ∈ ℝ^k_+ | x_i < iρ ∀ 1 ≤ i ≤ k, x_i < x_{i+1} ∀ 1 ≤ i ≤ k − 1}`
(Lemma 2, p. 10), with `ℝ_+ = [0, ∞)`. -/
def polytope (k : ℕ) (ρ : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∀ i : Fin k, x i < ((i : ℕ) + 1 : ℝ) * ρ) ∧ StrictMono x}

/-- The unit polytope `P̄_k = P_k` at `ρ = 1` (p. 13). -/
def unitPolytope (k : ℕ) : Set (Fin k → ℝ) := polytope k 1

/-- The `k`-step Dyck paths `D_k`, recorded as vectors (§2.2, p. 8): non-decreasing
`d ∈ ℕ^k` with `1 ≤ d_i ≤ i`. -/
def dyckPaths (k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun i : Fin k => Finset.Icc 1 ((i : ℕ) + 1)).filter fun d =>
    ∀ i j : Fin k, i ≤ j → d i ≤ d j

/-- The Dyck region `P̄_{k,d}`, eq. (10), p. 13. -/
def dyckRegion (k : ℕ) (d : Fin k → ℕ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∀ i, (d i : ℝ) - 1 ≤ x i ∧ x i < d i) ∧ StrictMono x}

/-- `κ_i(d) = |{j | d_j = i}|` (Propositions 2 and 3). -/
def kappa {k : ℕ} (d : Fin k → ℕ) (i : ℕ) : ℕ := (Finset.univ.filter fun j => d j = i).card

/-- Order statistics of a real vector: `v` sorted increasingly. -/
noncomputable def sortVec {k : ℕ} (v : Fin k → ℝ) : Fin k → ℝ := v ∘ Tuple.sort v

/-- A natural-number vector sorted increasingly (`⃗π`). -/
def sortNat {k : ℕ} (π : Fin k → ℕ) : Fin k → ℕ := π ∘ Tuple.sort π

/-- The parking functions of length `k`, Definition 2 (p. 8): `π ∈ ℤ^k_+` whose increasing
rearrangement satisfies `π_(i) ≤ i`. Values are taken from `{1, …, k}`, which loses nothing. -/
def parkingFunctions (k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 k).filter fun π =>
    ∀ i : Fin k, sortNat π i ≤ (i : ℕ) + 1

/-- The open unit cube `(0, 1)^k`. -/
def unitCube (k : ℕ) : Set (Fin k → ℝ) := Set.univ.pi fun _ => Set.Ioo 0 1

/-- The law of `ρ · ((π − U)_(1), …, (π − U)_(k))`, with `π` uniform on `PF_k` and
`U ∼ Uni(0,1)^k` independent of `π`, written as the mixture over `π`. -/
noncomputable def spineLaw (ρ : ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  ((parkingFunctions k).card : ENNReal)⁻¹ •
    ∑ π ∈ parkingFunctions k,
      (volume.restrict (unitCube k)).map fun u => ρ • sortVec fun i => (π i : ℝ) - u i

end HawkesParking.Spine


