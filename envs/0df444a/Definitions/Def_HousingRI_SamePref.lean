-- Prove2me | Definitions.Def_HousingRI_SamePref
-- name    : HousingRI_SamePref
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:41.642074+00:00
-- url     : https://prove2.me/theorems/ce1b1a7c-8dc6-4d04-8403-82bfaed5f972
-- title:
--   Agent $k$ has the same preferences at two profiles, $\tilde R_k = R_k$
-- statement:
--   Let $A$ and $\tilde A$ be two preference profiles given by real matrices over a set $N$ of agents and objects ($j\,R_k\,l$ iff $A_{kl}\le A_{kj}$). Agent $k$ has the **same preferences** at both profiles, $\tilde R_k=R_k$, when the two rows induce the same weak order:
--
--   $$\forall a,b\in N:\quad A_{kb}\le A_{ka}\iff \tilde A_{kb}\le \tilde A_{ka}.$$
--
--   It is used in condition (1) of an improvement and in the one-agent reduction of the proof of Theorem 1.
--
--   **Formalization Note** The comparison is ordinal: the utility rows need not be equal.
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, §3, p.13, condition (1) of improvement and proof of Theorem 1.

import Mathlib

namespace HousingRI

/-- **Equal preferences of one agent at two profiles**, `R̃ₖ = Rₖ` (Biró, Klijn, Klimentova,
Viana, arXiv:2102.00167v1, §3, condition (1) of improvement, p.13, and proof of Theorem 1, p.13).

**Formalization Note.** Preferences are utility matrices (`j Rₖ l` is `A k l ≤ A k j`), so two
profiles give agent `k` the same preference relation exactly when the two rows induce the same
weak order. This is an ordinal equivalence, not equality of the utility rows. -/
def SamePref {N : Type*} (A Ã : N → N → ℝ) (k : N) : Prop :=
  ∀ a b : N, A k b ≤ A k a ↔ Ã k b ≤ Ã k a

end HousingRI


