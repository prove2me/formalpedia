-- Prove2me | Definitions.Def_TargetedSamplers_IsOracleFor
-- name    : TargetedSamplers_IsOracleFor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:02.380825+00:00
-- url     : https://prove2.me/theorems/8c9972be-b150-43cd-b5dc-22d4939b9358
-- title:
--   Oracles answering a promise problem
-- statement:
--   A **promise problem** $\Pi=(\Pi_Y,\Pi_N)$ is a pair of disjoint sets of bit strings (the published definition `KarpLiptonOM.PromiseProblem`). Strings in neither set are outside the promise.
--
--   An oracle $O$ **answers** $\Pi$ if $O(z)=1$ for $z\in\Pi_Y$, $O(z)=0$ for $z\in\Pi_N$, and $O(z)\in\{0,1\}$ arbitrary elsewhere. A class relative to a promise-problem oracle (as in $\mathrm{prRTC}^{\mathrm{prcoRTC}}$, Lemma 4.16) requires the oracle algorithm to work for every oracle that answers $\Pi$.
--
--   **Formalization Note** The paper does not fix the semantics of promise-problem oracles; this is the standard one.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Lemma 4.16, p.25 (pdf p.27)

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem

namespace TargetedSamplers

/-- `O` is an oracle for the promise problem `L = (Π_Y, Π_N)` (a published `KarpLiptonOM.PromiseProblem`:
disjoint sets of bit strings): it answers `1` on yes-instances, `0` on no-instances, and `0` or `1`,
arbitrarily, outside the promise (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission,
manuscript sha256 599d0a59…, Lemma 4.16, p.25: `prRTC^{prcoRTC}`).

**Formalization Note** The page writes classes relative to promise-problem oracles without fixing the
semantics; this is the standard one: the oracle machine must work for every such `O`. -/
def IsOracleFor (L : KarpLiptonOM.PromiseProblem) (O : List Bool → ℕ) : Prop :=
  (∀ z ∈ L.yes, O z = 1) ∧ (∀ z ∈ L.no, O z = 0) ∧ ∀ z, O z ≤ 1

end TargetedSamplers


