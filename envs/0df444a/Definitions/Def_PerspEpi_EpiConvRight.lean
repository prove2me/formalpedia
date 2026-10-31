-- Prove2me | Definitions.Def_PerspEpi_EpiConvRight
-- name    : PerspEpi_EpiConvRight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:29.522988+00:00
-- url     : https://prove2.me/theorems/f14c65ff-dfb4-4001-bae0-872a3a68065a
-- title:
--   Epi-convergence of a family as $\lambda\downarrow 0$
-- statement:
--   A family $\{f_\lambda\}_{\lambda > 0}$ epi-converges to $f$ as $\lambda \downarrow 0$ if
--
--   $$
--   f_{\lambda_k} \xrightarrow{e} f \quad\text{for every sequence } \lambda_k \downarrow 0 .
--   $$
--
--   This is the sense of Lemma 1 and Proposition 4(a),(b).
--
--   **Formalization Note** "$\lambda_k\downarrow 0$" is encoded as a sequence of positive reals tending to $0$ (`Tendsto t atTop (𝓝[>] 0)`). Every such sequence has a monotone subsequence and epi-limits pass to subsequences, so the notion is the same as with monotone sequences.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §1.2 Notation, p.4

import Mathlib
import Definitions.Def_PerspEpi_SeqEpiConv

namespace PerspEpi

/-- **Epi-convergence of a family as λ ↓ 0.** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §1.2 Notation, p.4: "We extend
these notions to families of functions {f_λ}_{λ↓0} via f_λ →ξ f :⟺ ∀{λ_k} ↓ 0 : f_{λ_k} →ξ f".

**Formalization Note.** "{λ_k} ↓ 0" is encoded as a sequence of positive reals tending to `0`
(`Tendsto t atTop (𝓝[>] 0)`). Monotonicity is not required; since every such sequence has a
monotone subsequence and epi-limits of subsequences agree, the notion is the same. -/
def EpiConvRight {X : Type*} [TopologicalSpace X] (F : ℝ → X → EReal) (g : X → EReal) : Prop :=
  ∀ t : ℕ → ℝ, Filter.Tendsto t Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) →
    SeqEpiConv (fun k => F (t k)) g

end PerspEpi


