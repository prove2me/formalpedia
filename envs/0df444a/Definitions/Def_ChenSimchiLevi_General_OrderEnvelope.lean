-- Prove2me | Definitions.Def_ChenSimchiLevi_General_OrderEnvelope
-- name    : ChenSimchiLevi_General_OrderEnvelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:11:02.671377+00:00
-- url     : https://prove2.me/theorems/b381a744-3fe2-44bc-9090-b4a465d80b19
-- title:
--   Fixed-cost ordering envelope
-- statement:
--   Given a fixed order cost $k$ and a post-order profit function $G$, define the ordering envelope at starting inventory $x$ by
--   $$W(x)=\sup_{y\ge x}\{G(y)-k\mathbf 1_{\{y>x\}}\}.$$
--   It separates the structural effect of fixed-cost ordering from the paper's demand and price model. The proof of Theorem 4.1 identifies this envelope with $v_t(x)-c_tx$.
--
--   **Formalization Note** The supremum is real-valued; the theorems using it give attainment and coercivity hypotheses, so its empty or unbounded-set default value is never relied on.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 892, proof of Theorem 4.1, display of v*_t

import Definitions.Def_ChenSimchiLevi_General_Model

set_option autoImplicit false

namespace ChenSimchiLevi.General

noncomputable section

/-- The order-or-do-not-order envelope in the proof of Theorem 4.1. -/
def orderEnvelope (k : ℝ) (G : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun y => -k * δ (y - x) + G y) '' Set.Ici x)

end
end ChenSimchiLevi.General


