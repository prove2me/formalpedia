-- Prove2me | Definitions.Def_HSOSetCover_FullCover_Oracle
-- name    : HSOSetCover_FullCover_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:15.213205+00:00
-- url     : https://prove2.me/theorems/443f58fb-8f9e-49ab-be57-29e6bde43fd9
-- title:
--   Oracle outcomes and the failure-invariant call assumption (FICA)
-- statement:
--   An oracle model on a measurable space $\Omega$ consists, for each opportunity $i\in[k]$, of a measurable event $S_i$ (the call returns an accepted cover by its cutoff) and a measurable token cost $\mathrm{TOK}_i:\Omega\to[0,\infty]$ (the cost through response or cancellation at the cutoff). No relation between $\mathrm{TOK}_i$ and $S_i$ is imposed, since the realized token cost may correlate with success.
--
--   For $F\subseteq[k]$ write $A_F=\bigcap_{i\in F}S_i^{c}$, the event that every opportunity in $F$ fails. A probability measure $\mu$ satisfies the **failure-invariant call assumption** if for every $F\subseteq[k]$:
--
--   1. for each $i\notin F$, $\mu(S_i\cap A_F)=p_i\,\mu(A_F)$;
--   2. for each $i\notin F$, $\int_{A_F}\mathrm{TOK}_i\,d\mu=c_i\,\mu(A_F)$;
--   3. for each $G\subseteq[k]$ disjoint from $F$,
--   $$\mu\Bigl(\bigcap_{i\in G}S_i\cap A_F\Bigr)=\Bigl(\prod_{i\in G}p_i\Bigr)\mu(A_F).$$
--
--   Thus earlier failures do not change the success probability or the expected token cost of a call not yet made, and the success events of the unused calls are conditionally independent. This is the hypothesis of every result in §4 of the source.
--
--   **Formalization Note** The conditions are written multiplicatively so that they are unambiguous without a positivity assumption. FICA itself implies $\mu(A_F)=\prod_{i\in F}(1-p_i)>0$, so these are the conditional statements of the source. Pairs $(S_i,\mathrm{TOK}_i)$ are not assumed independent.
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, §3, PDF p. 5 / printed p. 4; §4 opening paragraph, PDF p. 6 / printed p. 5

import Mathlib
import Definitions.Def_HSOSetCover_FullCover_Instance

open MeasureTheory

namespace HSOSetCover.FullCover

/-- The oracle outcomes (§3–§4, PDF pp. 5–6) on a measurable space `Ω`: for each call opportunity
`i`, the measurable event `S i` that it returns an accepted cover by its cutoff, and its nonnegative
measurable token cost `TOK i` through response or cancellation at the cutoff. No relation between
`TOK i` and `S i` is imposed: the realized token cost may correlate with success. -/
structure OracleModel (k : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The event that opportunity `i` returns an accepted cover by `ℓᵢ`. -/
  S : Fin k → Set Ω
  /-- The token cost of opportunity `i`. -/
  TOK : Fin k → Ω → ENNReal
  measurableSet_S : ∀ i, MeasurableSet (S i)
  measurable_TOK : ∀ i, Measurable (TOK i)

variable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- `A_F = ⋂_{i ∈ F} (S i)ᶜ`: every opportunity in `F` fails. -/
def OracleModel.allFail (O : OracleModel k Ω) (F : Finset (Fin k)) : Set Ω :=
  ⋂ i ∈ F, (O.S i)ᶜ

/-- The **failure-invariant call assumption** (FICA, PDF p. 6): for every set `F` of opportunities
already used and failed, conditionally on `A_F`,
1. each unused opportunity `i` still has success probability `pᵢ`,
2. each unused opportunity `i` still has expected token cost `cᵢ`,
3. the success events of the unused opportunities are independent.
The three clauses are written in multiplicative form, `P(E ∩ A_F) = q · P(A_F)` for
`P(E | A_F) = q`. -/
def FICA (P : Instance k) (μ : Measure Ω) (O : OracleModel k Ω) : Prop :=
  ∀ F : Finset (Fin k),
    (∀ i, i ∉ F →
      μ (O.S i ∩ O.allFail F) = ENNReal.ofReal (P.prob i) * μ (O.allFail F)) ∧
    (∀ i, i ∉ F →
      ∫⁻ x in O.allFail F, O.TOK i x ∂μ = ENNReal.ofReal (P.cost i) * μ (O.allFail F)) ∧
    (∀ G : Finset (Fin k), Disjoint G F →
      μ ((⋂ i ∈ G, O.S i) ∩ O.allFail F) =
        (∏ i ∈ G, ENNReal.ofReal (P.prob i)) * μ (O.allFail F))

end HSOSetCover.FullCover


