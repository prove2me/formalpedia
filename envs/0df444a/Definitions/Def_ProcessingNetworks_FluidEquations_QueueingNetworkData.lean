-- Prove2me | Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
-- name    : ProcessingNetworks_FluidEquations_QueueingNetworkData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:40:40.903324+00:00
-- url     : https://prove2.me/theorems/04a4443e-1d34-40d1-8a42-a4d0d6b5e876
-- title:
--   Queueing network model data (Section 2.6) and fluid equations (6.1)-(6.6), specialized
-- statement:
--   A **queueing network** (Section 2.6) is an SPN with one activity per buffer: each buffer/class
--   $i$ is served by a unique server pool $p(i)$, and completed jobs move between classes
--   according to an $I \times I$ routing matrix $P$ ($P_{ij}$ = probability a completed class-$i$
--   job next becomes class $j$). `poolBuffers dat k` is $I(k)$, the set of classes served by pool
--   $k$ (Eq. 2.43), and `QueueingNetworkData.toSPNData` is the network's Section 2.1 model data
--   (mission I's `SPNData`): the material requirements matrix is the identity and the server
--   requirements matrix is $A_{ki} = \mathbb 1[p(i) = k]$, with the strictly positive capacities $b$.
--
--   `IsFluidModelSolutionQN` specializes the general fluid equations (6.1)-(6.6) — restated by
--   mission III as `IsFluidModelSolution` — to this structure: consumption is the identity
--   ($B = 1$, so $\hat D = \hat F$), the output matrix is $\Gamma_{ij} = P_{ji}$, and the capacity
--   bound (6.6) is stated pool-by-pool via `poolBuffers`.
--
--   **Formalization note.** This is a genuine specialization, not an independent redefinition:
--   every conjunct traces to (6.1)-(6.6) with the substitutions $B=1$, $\Gamma_{ij}=P_{ji}$,
--   $A_{ki} = \mathbb 1[p(i)=k]$ made explicit, matching how Section 2.6 itself introduces
--   queueing networks as a special case of the general SPN model; `toSPNData` records the same
--   substitutions as model data, so that the standard setup of Chapter 6 can be instantiated for a
--   queueing network.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 125, Section 2.6 (queueing networks) and Eqs. (6.1)-(6.6), specialized

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_SPNModel

namespace ProcessingNetworks.FluidEquations

open ProcessingNetworks.Stability

/-- A queueing network (Dai & Harrison, Section 2.6): a special class of SPN with one activity
per buffer (`I = J`, indexed together by `Fin I`), organized into `K` server pools. `p i` is the
pool serving class `i` (`p(i)` in the book's notation); `P` is the `I × I` routing matrix
(`P i j` = probability a completed class-`i` job next becomes a class-`j` job); `m` is the vector
of mean service times; `lam` is the vector of external arrival rates; `b` is the `K`-vector of
server-pool capacities, strictly positive. -/
structure QueueingNetworkData (I K : ℕ) where
  p : Fin I → Fin K
  P : Matrix (Fin I) (Fin I) ℝ
  m : Fin I → ℝ
  lam : Fin I → ℝ
  b : Fin K → ℝ
  b_pos : ∀ k, 0 < b k

/-- The Section 2.1 model data of a queueing network (mission I's `SPNData`): `J = I`, the
material requirements matrix is the identity (each activity consumes one job of its own class),
and the server requirements matrix is `A k i = 1 ↔ p i = k` (Eq. (2.43)). -/
def QueueingNetworkData.toSPNData {I K : ℕ} (dat : QueueingNetworkData I K) : SPNData I I K where
  A := fun k i => if dat.p i = k then 1 else 0
  B := 1
  b := dat.b
  A_binary := by
    intro k i
    by_cases h : dat.p i = k <;> simp [h]
  B_binary := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  A_col_nonzero := fun i => ⟨dat.p i, by simp⟩
  B_col_nonzero := fun j => ⟨j, by simp⟩
  b_pos := dat.b_pos

/-- `I(k)` (Eq. (2.43)): the set of buffers/classes processed by server pool `k`. -/
def poolBuffers {I K : ℕ} (dat : QueueingNetworkData I K) (k : Fin K) : Finset (Fin I) :=
  Finset.univ.filter (fun i => dat.p i = k)

/-- The fluid equations (6.1)-(6.6), specialized to a queueing network: since a queueing network
has one activity per buffer with full consumption of its own buffer (`B = 1`, the identity
matrix), (6.3) becomes `D̂ = F̂`; since a completed class-`j` job becomes class `i` with
probability `P j i`, the expected-output matrix of (6.1) is `Γ i j = P j i`; and the capacity
bound (6.6) is stated per server pool via `poolBuffers`, matching (6.6) with the queueing
network's `0`-`1` capacity-consumption matrix `A k i = 1 ↔ p i = k`. -/
def IsFluidModelSolutionQN {I K : ℕ} (dat : QueueingNetworkData I K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin I → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Fh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, dat.m i * Fh t i = Th t i) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ i ∈ poolBuffers dat k, (Th t i - Th s i) ≤ dat.b k * (t - s))

end ProcessingNetworks.FluidEquations


