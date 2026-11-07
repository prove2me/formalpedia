-- Prove2me | Definitions.Def_ReplicableDecisions_IsMaxLikelihood
-- name    : ReplicableDecisions_IsMaxLikelihood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:12.550774+00:00
-- url     : https://prove2.me/theorems/53c2d32e-e19c-4d2e-b61a-e73d8b6c8073
-- title:
--   A likelihood maximizer $\widehat P(S)$
-- statement:
--   A selection $\widehat P$ of a maximum-likelihood model maps each sample $S\in\mathcal Z^n$ to a model with
--
--   $$
--   Q^n(S)\le\widehat P(S)^n(S)\qquad\text{for every }Q\in\mathcal P.
--   $$
--
--   It is the estimator through which samples enter the rule of Theorem 3.1.
--
--   **Formalization Note** The selection is any such function of the sample, which covers every fixed tie-breaking.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Lemma 3.5, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment

namespace ReplicableDecisions

/-- **A likelihood maximizer selection.** Chen, *Replicable Decisions in Finite Experiments*, STOC
2027 submission (sha256 52d181db…), Lemma 3.5, p.13 (PDF p.15): `P̂(S)` is "a maximum-likelihood model
in P, with fixed tie-breaking".

**Formalization Note.** `mle` is any function of the sample with `Qⁿ(S) ≤ (mle S)ⁿ(S)` for every `Q`
and `S`, which covers every fixed tie-breaking. -/
def IsMaxLikelihood {ι : Type*} {Z : Type} [Fintype Z] {n : ℕ} (E : Experiment ι Z)
    (mle : (Fin n → Z) → ι) : Prop :=
  ∀ x j, productLaw (E.P j) x ≤ productLaw (E.P (mle x)) x

end ReplicableDecisions


