-- Prove2me | Definitions.Def_MonoidProdQ_IncrementalSummary_HasEssWidthLE
-- name    : MonoidProdQ_IncrementalSummary_HasEssWidthLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:53:27.944477+00:00
-- url     : https://prove2.me/theorems/4bafcc2d-1df9-4106-a77a-7ebf9b6601e7
-- title:
--   Essential width at most $B$
-- statement:
--   The **essential width** of an incremental summary is $\kappa=\max_{x\in D}\max_{T\subseteq I}|\mathrm{Ess}_x(T)|$. For a real number $B$, the summary has essential width at most $B$ if
--
--   $$|\mathrm{Ess}_x(T)|\le B\qquad\text{for every } x\in D \text{ and every } T\subseteq I.$$
--
--   This is the hypothesis of the essential-width adversary theorem.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 2 and Theorem 14, p.27

import Definitions.Def_MonoidProdQ_IncrementalSummary_ess

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 2 and Theorem 14, p.27: the essential width
`κ = max_{x ∈ D} max_{T ⊆ I} |Essₓ(T)|` of the summary is at most `B`, i.e.
`|Essₓ(T)| ≤ B` for every `x ∈ D` and every `T ⊆ I`. `B` is real, as in Theorem 14's
"B ≥ 0". -/
def IncrementalSummary.HasEssWidthLE {I Sig Out Q : Type*} [DecidableEq I] [Fintype I]
    [DecidableEq Q] {f : (I → Sig) → Out} {D : Finset (I → Sig)}
    (S : IncrementalSummary f D Q) (B : ℝ) : Prop :=
  ∀ x ∈ D, ∀ T : Finset I, ((S.ess x T).card : ℝ) ≤ B

end MonoidProdQ


