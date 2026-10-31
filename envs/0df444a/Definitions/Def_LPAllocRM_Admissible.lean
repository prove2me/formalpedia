-- Prove2me | Definitions.Def_LPAllocRM_Admissible
-- name    : LPAllocRM_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:07:44.782982+00:00
-- url     : https://prove2.me/theorems/f8493482-3308-4912-9072-34d4946dc9a9
-- title:
--   Admissible policies: $AN^\pi\le b$ almost surely
-- statement:
--   In a problem with resource matrix $A$, capacity vector $b$, horizon $\tau$ and arrival process $D$ on a probability space $(\Omega,P)$, a policy $\pi\in\Pi$ is **admissible** if each count $N^\pi_j$ is a random variable and, almost surely,
--
--   $$AN^\pi\le b.$$
--
--   The constraint $0\le N^\pi\le D(\tau)$ holds for every policy by construction. These are the constraints of (1): "a policy needs to satisfy (almost surely) $AN^\pi\le c$ and $0\le N^\pi\le D(\tau)$" and "the constraints must be satisfied for almost every sample path of the demand process". In the $k$th problem $b=kc$.
--
--   **Formalization Note** "Random variable" is rendered as almost-everywhere measurability with respect to $P$, which makes $E(f\cdot N^\pi)$ in (1) meaningful.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, eq. (1) and eq. (2), p.722; §4, p.723

import Mathlib
import Definitions.Def_LPAllocRM_accepted
open MeasureTheory

namespace LPAllocRM

/-- A policy `π` is admissible in a problem with capacity vector `b`, resource matrix `A`, horizon
`τ` and arrival process `D` on the probability space `(Ω, P)` if each count `N^π_j` is a random
variable and, almost surely, `A N^π ≤ b`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
(1), p.722 (PDF p.3): "a policy needs to satisfy (almost surely) AN^π ⩽ c and 0 ⩽ N^π ⩽ D(τ)";
"Note that the constraints must be satisfied for almost every sample path of the demand process";
(2): "the number of accepted class j customers is then given by the random variable N^π_j".
In the kth problem the capacity is `k c` (§4, p.723).

**Formalization Note** The constraint `0 ≤ N^π ≤ D(τ)` holds by construction of `accepted`.
"`N^π_j` is a random variable" is rendered as `AEMeasurable` with respect to `P`; this is what
makes `E(f · N^π)` in (1) meaningful. -/
def Admissible {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (τ : ℝ) (P : Measure Ω) (D : Ω → ℝ → Fin n → ℕ) (π : Policy n) : Prop :=
  (∀ j, AEMeasurable (fun ω => (accepted τ π (D ω) j : ℝ)) P) ∧
  ∀ᵐ ω ∂P, ∀ i, ∑ j, A i j * (accepted τ π (D ω) j : ℝ) ≤ b i

end LPAllocRM


