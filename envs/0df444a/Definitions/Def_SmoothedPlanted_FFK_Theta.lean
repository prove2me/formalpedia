-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Theta
-- name    : SmoothedPlanted_FFK_Theta
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:32:49.379254+00:00
-- url     : https://prove2.me/theorems/2d78f64a-2f0e-414a-9da4-0696e604e336
-- title:
--   Robust Lifted Theta SDP and optimality
-- statement:
--   For a graph on literals $(i,a)$, add the per-variable constraints $g(i):=\sum_a M_{ia,ia}\le1$ to the Robust Theta SDP. Its value $\Theta$ is the supremum of the same total mass objective over this feasible set. A matrix is optimal iff it is feasible and its mass is at least that of every feasible matrix. This definition contains no theorem about its value or recovery. The Gram formulation permits all vector solutions in arbitrary finite dimension. For nonnegative budgets the feasible set is nonempty and compact.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Robust Lifted Theta SDP and optimality, printed p. 24 (PDF p. 26), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_ThetaPrime

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

def variableMass {V : Type} {q : ℕ} (M : Gram (V × Fin q)) (i : V) : ℝ :=
  ∑ a, M (some (i,a)) (some (i,a))
def liftedFeasible {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (H : SimpleGraph (V × Fin q)) (k : ℕ) (Δ : ℝ) (M : Gram (V × Fin q)) : Prop :=
  thetaFeasible H k Δ M ∧ ∀ i, variableMass M i ≤ 1
def theta {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (H : SimpleGraph (V × Fin q)) (k : ℕ) (Δ : ℝ) : ℝ :=
  sSup {z | ∃ M : Gram (V × Fin q), liftedFeasible H k Δ M ∧ z = mass M}
def liftedOptimal {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (H : SimpleGraph (V × Fin q)) (k : ℕ) (Δ : ℝ) (M : Gram (V × Fin q)) : Prop :=
  liftedFeasible H k Δ M ∧
    ∀ N : Gram (V × Fin q), liftedFeasible H k Δ N → mass N ≤ mass M

end SmoothedPlanted.FFK


