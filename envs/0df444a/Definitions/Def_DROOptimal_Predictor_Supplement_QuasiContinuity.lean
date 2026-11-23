-- Prove2me | Definitions.Def_DROOptimal_Predictor_Supplement_QuasiContinuity
-- name    : DROOptimal_Predictor_Supplement_QuasiContinuity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:31:15.186324+00:00
-- url     : https://prove2.me/theorems/83fa4db2-24c9-48f8-9638-15b2b886ebcf
-- title:
--   Notation, p. 5; §5, pp. 23–24 — quasi-continuity for a topological model domain
-- statement:
--   A map $f:A\to B$ from a topological space to a metric space is quasi-continuous at $p\in A$ when every neighborhood $U$ of $p$ and every $\epsilon>0$ admit a nonempty open subset $V\subseteq U$ such that
--   $$
--   \operatorname{dist}(f(p),f(q))\le\epsilon\quad(q\in V).
--   $$
--   The map is quasi-continuous when this holds at every point. The set $V$ need not contain $p$. This is the source's neighborhood definition, isolated from the particular model carrier so that it also applies to the weak topology on Borel probability distributions in §5. On decisions the distance is Euclidean. The definition neither implies nor requires a Borel-measurable selector.
--
--   Differences from the source:
--   - generalization: The notation on p. 5 uses Euclidean subsets, and §5 uses the weak model topology → The reusable predicate accepts any topological domain and pseudometric codomain; reason: The same neighborhood criterion specializes to every source instance, and Theorem 11 uses exactly the source's weak model topology and Euclidean decision distance
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 5, Notation; §5, pp. 23–24 (weak model topology and quasi-continuous selectors)

import Mathlib

set_option autoImplicit false

namespace DROOptimal.Predictor.Supplement

open Topology

/-- Notation, p. 5, used with the weak model topology in §5, pp. 23–24.
The open set need not contain the base point. This topological formulation also
applies when the model space is infinite dimensional. -/
def QuasiContinuousAt {A B : Type*} [TopologicalSpace A] [PseudoMetricSpace B]
    (f : A → B) (p : A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ U ∈ 𝓝 p,
    ∃ V : Set A, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, dist (f p) (f q) ≤ ε

/-- Quasi-continuity at every point, with exactly the neighborhood criterion
of Notation, p. 5; distance on decisions specializes to Euclidean distance. -/
def QuasiContinuous {A B : Type*} [TopologicalSpace A] [PseudoMetricSpace B]
    (f : A → B) : Prop :=
  ∀ p, QuasiContinuousAt f p

end DROOptimal.Predictor.Supplement


