-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerToUpper
-- name    : DiscreteConvex_NetworkFlows_NegLowerToUpper
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:13:49.296349+00:00
-- url     : https://prove2.me/theorems/bece2f12-204c-48cb-bd88-f79e58d052a2
-- title:
--   Negation-and-recast map $\mathbb R\cup\{-\infty\}\to\mathbb R\cup\{+\infty\}$
-- statement:
--   Sends $v \in \mathbb R \cup \{-\infty\}$ to $-v \in \mathbb R \cup \{+\infty\}$: $-\infty \mapsto +\infty$, $r \mapsto -r$ for $r \in \mathbb R$. Used to add a lower-capacity term to an upper-capacity term (both drawn from the book's own extended real lines for capacities) without a `WithTop ℝ`/`WithBot ℝ` type mismatch in Lean; see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247

import Mathlib

/-!
The negation-and-recast map `ℝ ∪ {-∞} → ℝ ∪ {+∞}`, used to add a lower-capacity term to an
upper-capacity term without a `WithTop ℝ`/`WithBot ℝ` type mismatch, in
`DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- Sends `v : ℝ ∪ {-∞}` to `-v : ℝ ∪ {+∞}`: `⊥ ↦ ⊤`, `(r:ℝ) ↦ (-r:ℝ)`. -/
def NegLowerToUpper (v : WithBot ℝ) : WithTop ℝ :=
  WithBot.recBotCoe (⊤ : WithTop ℝ) (fun r : ℝ => ((-r : ℝ) : WithTop ℝ)) v

end DiscreteConvex.NetworkFlows


