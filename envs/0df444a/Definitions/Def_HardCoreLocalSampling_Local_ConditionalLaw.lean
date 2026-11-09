-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_ConditionalLaw
-- name    : HardCoreLocalSampling_Local_ConditionalLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:57.10926+00:00
-- url     : https://prove2.me/theorems/5f0e1ce3-f6b4-447b-b6d7-5bc4b1b99ff0
-- title:
--   Compatible hard-core weights and conditional marginal
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $\lambda$ be its fugacity, and let $\xi$ be a tri-state pinning. The pinning is feasible if some independent set agrees with all its pins. Define
--
--   $$
--   w_\xi(I)=\mathbf1\{I\text{ independent},\ I\sim\xi\}\lambda^{|I|},\qquad
--   Z_\xi=\sum_{I\subseteq V}w_\xi(I),\qquad
--   \mu_\xi(I)=\frac{w_\xi(I)}{Z_\xi}.
--   $$
--
--   The conditional unoccupied marginal at $v$ is $\sum_{I:v\notin I}\mu_\xi(I)$. Thus the requested bit has value one for absence. At positive fugacity and feasible pinning, $Z_\xi>0$. These finite sums specify the target distribution; they do not provide a marginal-query primitive to an algorithm.
--
--   The strict tree-uniqueness threshold is $\lambda_c(\Delta)=(\Delta-1)^{\Delta-1}/(\Delta-2)^\Delta$ for $\Delta\ge3$.
--
--   **Formalization Note** The weight and mass formulas are total real-valued functions. A zero normalizing denominator yields zero mass; the source domain is positive fugacity with feasible pins, where this case is excluded. The rational threshold formula is intended only for degrees at least three, where its natural-number subtractions are exact.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §2, printed p.2 (PDF p.3); threshold in §1, printed p.1 (PDF p.2)

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting
import Definitions.Def_HardCoreLocalSampling_Local_Pinning

namespace HardCoreLocalSampling.Local

/-! The finite hard-core law of §2, printed p.2 / PDF p.3. Finite sums
below define mathematical targets. They are not permitted sampler primitives. -/

/-- At least one independent set agrees with every specified pin. -/
def Feasible {V : Type*} [Fintype V] (G : SimpleGraph V) (pin : Pinning V) : Prop :=
  ∃ I : Finset V, ExpanderBIS.HardCore.IsIndep G I ∧ Compatible pin I

/-- The compatible hard-core weight, zero on incompatible or nonindependent sets. -/
noncomputable def conditionalWeight {V : Type*} [Fintype V]
    (G : SimpleGraph V) (lam : ℝ) (pin : Pinning V) (I : Finset V) : ℝ := by
  classical
  exact if ExpanderBIS.HardCore.IsIndep G I ∧ Compatible pin I then lam ^ I.card else 0

/-- Sum of the compatible independent-set weights. -/
noncomputable def conditionalPartition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (lam : ℝ) (pin : Pinning V) : ℝ :=
  ∑ I : Finset V, conditionalWeight G lam pin I

/-- The conditional probability mass of a finite vertex set. This total formula
returns zero if its denominator is zero. The source domain is positive fugacity
and feasible pinning, where the denominator is strictly positive. -/
noncomputable def conditionalMass {V : Type*} [Fintype V]
    (G : SimpleGraph V) (lam : ℝ) (pin : Pinning V) (I : Finset V) : ℝ :=
  conditionalWeight G lam pin I / conditionalPartition G lam pin

/-- Probability that a queried vertex is absent; the requested output bit is 1
for this outcome. The denominator convention is that of `conditionalMass`. -/
noncomputable def conditionalUnoccupied {V : Type*} [Fintype V]
    (G : SimpleGraph V) (lam : ℝ) (pin : Pinning V) (v : V) : ℝ := by
  classical
  exact ∑ I : Finset V, if v ∉ I then conditionalMass G lam pin I else 0

/-- The full strict tree-uniqueness threshold. Only degrees at least three
are used by this source; no meaning for smaller degrees is imposed here. -/
def criticalFugacity (Delta : ℕ) : ℚ :=
  ((Delta - 1 : ℕ) : ℚ) ^ (Delta - 1) / ((Delta - 2 : ℕ) : ℚ) ^ Delta

end HardCoreLocalSampling.Local


