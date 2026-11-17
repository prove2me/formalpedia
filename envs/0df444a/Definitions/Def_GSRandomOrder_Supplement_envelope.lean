-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_envelope
-- name    : GSRandomOrder_Supplement_envelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:06:58.730756+00:00
-- url     : https://prove2.me/theorems/69858ac2-bfd3-497c-8c57-3a6bbd33a388
-- title:
--   Disposal envelope $\bar v(S)=\max_{T\subseteq S}v(T)$ and its marginals
-- statement:
--   For a valuation $v:2^N\to\mathbb R\cup\{-\infty\}$ with $v(\emptyset)=0$ the **disposal envelope** is
--   $$
--   \bar v(S)=\max_{T\subseteq S} v(T),
--   $$
--   a real number $\ge0$ (take $T=\emptyset$). The marginal of an item $g$ to a bundle $B$ is $\bar v(g\mid B)=\bar v(B+g)-\bar v(B)$.
--
--   Frozen routing trains its routes on the envelopes of the bidders: by Lemma 4.2 of the paper the envelope of a GS valuation is a nonnegative nondecreasing GS valuation with the same welfare optimum.
--
--   **Formalization Note** The maximum is `Finset.sup` over `S.powerset` in `WithBot ℝ`, read as a real with `unbotD 0` (never reached for valuations).
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4.1, p.12, Lemma 4.2 (definition of the envelope); §4.2, p.13, eq. (10) (marginals)

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Disposal envelope** `v̄(S) = max_{T ⊆ S} v(T)` (R. Paes Leme, M. Pál, N. Patel, *Gross
Substitutes Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §4.1,
p.12, Lemma 4.2).

**Formalization Note.** The maximum is `Finset.sup` over `S.powerset` in `WithBot ℝ`, read as a
real number with `unbotD 0`; for a valuation (`v(∅) = 0`) the term `T = ∅` makes it `≥ 0`, so the
fallback is never used. -/
noncomputable def envelope {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (S : Finset (Fin n)) : ℝ :=
  (S.powerset.sup v).unbotD 0

/-- The marginal `v̄(g | B) = v̄(B + g) − v̄(B)` of item `g` to the bundle `B` under the
envelope (§4.2, p.13, eq. (10)). -/
noncomputable def envelopeMarginal {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (g : Fin n)
    (B : Finset (Fin n)) : ℝ :=
  envelope v (insert g B) - envelope v B

end GSRandomOrder.Supplement


