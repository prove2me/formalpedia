-- Prove2me | Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
-- name    : ProcessingNetworks_BackPressure_AllocationPolytope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:19:32.13298+00:00
-- url     : https://prove2.me/theorems/e3606e71-4b93-4d97-a7ca-0760a63c993d
-- title:
--   The allocation polytope, objective, extreme allocations, and Definition 9.9
-- statement:
--   The **allocation polytope** $\mathcal A := \{\beta \in \mathbb{R}^J_+ : A\beta \le b\}$;
--   $p(\beta,z) := z\cdot R\beta$ is the bilinear back-pressure objective; $E$ ("extreme
--   allocations") is $\mathcal A$'s set of extreme points.
--
--   **Definition 9.9.** $\beta \in \mathcal A$ is **$z$-maximal** if $p(\beta,z) =
--   \max_{\alpha\in\mathcal A} p(\alpha,z)$.
--
--   The back-pressure optimization problem (9.15)–(9.17) at a system state $(\hat n, \hat z)$
--   maximizes $p(\beta, \hat z)$ over $\beta \in \mathcal A$ subject to material availability
--   $B(\hat n + u) \le \hat z$, where $u$ is the service-initiation vector (9.17): $u_j = 1$ iff
--   $\beta_j > 0$ and no type-$j$ service is open. `serviceInitiation` is $u$ and `BPFeasible dat
--   n̂ ẑ β` is feasibility for (9.15)–(9.17).
--
--   **Formalization note.** `ExtremeAllocations` is `Set.extremePoints ℝ (AllocationPolytope
--   dat)`, reusing Mathlib's own convex-geometry substrate rather than restating extreme-point
--   theory, per this mission's own `BRIEF.md` recommendation. `IsZMaximal` is phrased as "$\beta$
--   is feasible and dominates every feasible $\alpha$" rather than via an explicit `sSup`/`⨆`
--   expression over $\mathcal A$ — this sidesteps any junk-value risk entirely and is
--   definitionally equivalent to "achieves the maximum" whenever a maximizer exists.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 173, Section 9.3 and Definition 9.9

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData

namespace ProcessingNetworks.BackPressure

/-- The allocation polytope `A := {β ∈ ℝ^J_+ : Aβ ≤ b}`, Section 9.3. -/
def AllocationPolytope {I J K : ℕ} (dat : SPNPlanningData I J K) : Set (Fin J → ℝ) :=
  {β | (∀ j, 0 ≤ β j) ∧ ∀ k, (dat.A.mulVec β) k ≤ dat.b k}

/-- The bilinear back-pressure objective `p(β,z) := z·Rβ`. -/
noncomputable def p {I J K : ℕ} (dat : SPNPlanningData I J K) (β : Fin J → ℝ) (z : Fin I → ℝ) :
    ℝ :=
  z ⬝ᵥ dat.R.mulVec β

/-- `E`, the (finite) set of extreme points of the allocation polytope `A` — "extreme
allocations," Section 9.3. -/
def ExtremeAllocations {I J K : ℕ} (dat : SPNPlanningData I J K) : Set (Fin J → ℝ) :=
  Set.extremePoints ℝ (AllocationPolytope dat)

/-- Definition 9.9 (`z`-maximal allocation), Dai & Harrison p. 173 (PDF p. 189): `β ∈ A` is
`z`-maximal if `p(β,z) = max_{α∈A} p(α,z)`, formalized as `β` being feasible and dominating every
other feasible allocation — a junk-value-free way to state "achieves the maximum." -/
def IsZMaximal {I J K : ℕ} (dat : SPNPlanningData I J K) (β : Fin J → ℝ) (z : Fin I → ℝ) : Prop :=
  β ∈ AllocationPolytope dat ∧ ∀ α ∈ AllocationPolytope dat, p dat α z ≤ p dat β z

/-- The service-initiation indicator `u_j` of Eq. (9.17): `1` if `β_j > 0` and no type-`j`
service is currently open (`n̂_j = 0`), else `0`. -/
noncomputable def serviceInitiation {J : ℕ} (nhat : Fin J → ℕ) (β : Fin J → ℝ) (j : Fin J) : ℝ :=
  if 0 < β j ∧ nhat j = 0 then 1 else 0

/-- Feasibility of the back-pressure optimization problem (9.15)-(9.17) at system state
`(n̂, ẑ)`: `β` is a nonnegative, capacity-respecting allocation (`β ∈ A`) whose implied service
initiations respect material availability (`B(n̂+u) ≤ ẑ`). -/
def BPFeasible {I J K : ℕ} (dat : SPNPlanningData I J K) (nhat : Fin J → ℕ) (zhat : Fin I → ℕ)
    (β : Fin J → ℝ) : Prop :=
  β ∈ AllocationPolytope dat ∧
  ∀ i, (dat.B.mulVec (fun j => (nhat j : ℝ) + serviceInitiation nhat β j)) i ≤ (zhat i : ℝ)

end ProcessingNetworks.BackPressure


