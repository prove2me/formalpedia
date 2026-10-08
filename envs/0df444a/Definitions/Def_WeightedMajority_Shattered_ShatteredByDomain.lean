-- Prove2me | Definitions.Def_WeightedMajority_Shattered_ShatteredByDomain
-- name    : WeightedMajority_Shattered_ShatteredByDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:04.624539+00:00
-- url     : https://prove2.me/theorems/c1e98136-736d-4b0b-8963-633cf2c7560b
-- title:
--   Shattering a finite function family by its domain
-- statement:
--   A finite family of Boolean functions $\varphi_i:X\to\{0,1\}$, indexed by $i=1,\ldots,n$, is **shattered by its domain** if every Boolean pattern of values across the functions occurs at some point of $X$:
--
--   $$
--   \forall b\in\{0,1\}^n\;\exists x\in X\;\forall i\in\{1,\ldots,n\},\quad \varphi_i(x)=b_i.
--   $$
--
--   This is the dual of the usual VC shattering of domain points by a function class. It supplies the exact richness assumption in Theorem 7.2.
--
--   **Formalization Note** The family is indexed by `Fin n`; its indices are zero-based in Lean. For $n=0$, this definition holds exactly when $X$ is nonempty, since the unique empty pattern must occur at an instance.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), p. 244, paragraph defining 'shattered by X'; https://doi.org/10.1006/inco.1994.1009

import Mathlib

namespace WeightedMajority.Shattered

/-- A family of Boolean functions is shattered by its domain when every joint
pattern of their values occurs at an instance (Littlestone--Warmuth, p. 244). -/
def ShatteredByDomain {X : Type*} {n : ℕ} (φ : Fin n → X → Bool) : Prop :=
  ∀ b : Fin n → Bool, ∃ x : X, ∀ i : Fin n, φ i x = b i

end WeightedMajority.Shattered


