-- Prove2me | Definitions.Def_ProcessingNetworks_Subcriticality_MaximalStability
-- name    : ProcessingNetworks_Subcriticality_MaximalStability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:25:39.181677+00:00
-- url     : https://prove2.me/theorems/a9271542-3721-41db-9e22-8fc8e0f41d8d
-- title:
--   Section 5.7 — stability region and maximal stability
-- statement:
--   Section 5.7 views a given SPN not as a single model but as a family indexed by its
--   arrival-rate vector $\lambda \in \mathbb{R}_+^I$. For a fixed $\lambda$, a **stable control
--   policy** is one under which (a) Assumption 3.1 (the Markov representation) holds, and (b) the
--   resulting network is stable in the sense of Definition 3.6. The **stability region** $\Lambda^*$
--   is the set of $\lambda$ for which *some* stable control policy exists.
--
--   A control policy `p` is **maximally stable** if (a) its implementation does not depend on
--   $\lambda$, and (b) it is a stable policy for every $\lambda \in \Lambda^*$.
--
--   Here a policy is represented abstractly by a value `p : Policy`, and `PolicyStable p lam`
--   records whether `p`, applied unchanged, is a stable policy at arrival-rate vector `lam`.
--   `StabilityRegion PolicyStable` is $\Lambda^*$: the set of `lam` for which some `p` works.
--   `IsMaximallyStable PolicyStable p` is exactly clause (b) applied to a fixed `p` ranging over
--   every `lam` in $\Lambda^*$.
--
--   **Formalization note.** Condition (a), "$p$'s implementation does not depend on $\lambda$," is
--   not a separate hypothesis to state: it is built into the very shape of `PolicyStable : Policy →
--   (Fin I → ℝ) → Prop` and `IsMaximallyStable`'s universal quantifier, which test one fixed value
--   of `p` against every `lam`, rather than allowing a different policy to be chosen for each
--   arrival-rate vector.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 102, Section 5.7

import Mathlib

namespace ProcessingNetworks.Subcriticality

/-- The stability region `Λ*` for a given SPN (Section 5.7, p. 102, PDF p. 118): the set of
arrival-rate vectors `λ` for which *some* control policy is a stable policy, i.e. Assumption 3.1
holds under that policy and the resulting SPN is stable (Definition 3.6) at that `λ`. A policy
is represented abstractly by a value of `Policy`, and `PolicyStable p lam` records that `p` is a
stable policy for arrival-rate vector `lam`. -/
def StabilityRegion {I : ℕ} {Policy : Type*} (PolicyStable : Policy → (Fin I → ℝ) → Prop) :
    Set (Fin I → ℝ) :=
  {lam | ∃ p, PolicyStable p lam}

/-- A control policy `p` is maximally stable (Section 5.7, p. 102, PDF p. 118) if it is a stable
policy for every `λ` in the stability region `Λ*`. "Its implementation does not depend on `λ`" is
encoded by `p`'s type: the same value `p` is tested against every `lam` in the definition, rather
than being chosen anew for each one. -/
def IsMaximallyStable {I : ℕ} {Policy : Type*} (PolicyStable : Policy → (Fin I → ℝ) → Prop)
    (p : Policy) : Prop :=
  ∀ lam ∈ StabilityRegion PolicyStable, PolicyStable p lam

end ProcessingNetworks.Subcriticality


