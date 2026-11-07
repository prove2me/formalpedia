-- Prove2me | Definitions.Def_MonoTestDAG_transcript
-- name    : MonoTestDAG_transcript
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:31.593747+00:00
-- url     : https://prove2.me/theorems/693ba594-b2ae-4a22-83c9-995fc334d007
-- title:
--   Transcripts $\mathrm{Tr}(D,Q)$ and their total variation distance
-- statement:
--   For a distribution $D$ over functions $V\to\mathbb R$ and a query set $Q\subseteq V$, $\mathrm{Tr}(D,Q)$ denotes the distribution of the restriction $F|_Q$ for $F\sim D$. The total variation distance is $\mathrm{TV}(P,P')=\sup_A|P(A)-P'(A)|$, the supremum over measurable $A\subseteq\mathbb R^Q$.
--
--   **Formalization Note.** Distributions over functions are probability mass functions (`PMF`). Every distribution the paper constructs is finitely supported, and for a countably supported distribution the acceptance probability of a tester is always defined. TV is the published `MarkovChainCLT.tvDist`, which adds no condition. The module also defines `trTV`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §2.4, p.11

import Mathlib
import Definitions.Def_TotalVariationDist

namespace MonoTestDAG

/-- `Tr(D, Q)`: the law of the restriction `F|_Q` for `F ∼ D`, where `D` is a (finitely or
countably supported) distribution over functions `V → ℝ` and `Q ⊆ V` a query set.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §2.4, p.11.

**Formalization Note.** Distributions over functions are probability mass functions `PMF`;
every distribution the paper constructs is finitely supported. -/
noncomputable def transcript {V : Type} (D : PMF (V → ℝ)) (Q : Finset V) : PMF (↥Q → ℝ) :=
  D.map (fun f v => f v)

/-- `TV(Tr(D₁, Q), Tr(D₂, Q))`, the total variation distance `sup_A |Pr₁(A) − Pr₂(A)|` of the two
transcript laws on `ℝ^Q` (with its Borel σ-algebra), using the published
`MarkovChainCLT.tvDist`. -/
noncomputable def trTV {V : Type} (D₁ D₂ : PMF (V → ℝ)) (Q : Finset V) : ℝ :=
  MarkovChainCLT.tvDist (transcript D₁ Q).toMeasure (transcript D₂ Q).toMeasure

end MonoTestDAG


