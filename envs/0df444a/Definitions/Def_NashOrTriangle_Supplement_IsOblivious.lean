-- Prove2me | Definitions.Def_NashOrTriangle_Supplement_IsOblivious
-- name    : NashOrTriangle_Supplement_IsOblivious
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:46:17.590734+00:00
-- url     : https://prove2.me/theorems/4710e417-89c7-41ed-94ed-9b535ffbe918
-- title:
--   Oblivious best-response oracles
-- statement:
--   A best-response oracle of the oracle model is **oblivious** if its answer to a query does not depend on when the query is made: it is a fixed response map assigning to every maximizing query (a finite rational column mixture, or $\bot$) a row, and to every minimizing query (a finite rational row mixture, or $\bot$) a column. An oblivious adversary fixes this map knowing the algorithm, but before any random bits of the algorithm are drawn.
--
--   The paper's lower bounds (Theorem 3.1) hold against oblivious adversaries, and its bounded-rank algorithm (Theorem 5.1) is analysed against fixed response maps.
--
--   **Formalization Note** The published `BRAdversary` indexes its answers by the number of the BR call; obliviousness says that all indices give the same answer.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), §1.1, p.4 (PDF p.5): "oblivious adversaries who fix the value and BR oracles"; §5, p.12 (PDF p.13): "Because the response maps are fixed"

import Mathlib
import Definitions.Def_NashOrTriangle_BRAdversary

namespace NashOrTriangle.Supplement

/-- The best-response oracle `adv` is **oblivious**: its answer to a query does not depend on the
index of the call, so it is a fixed response map from queries (finite rational mixtures, or `⊥`)
to strategies, chosen before the run.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 4 (PDF p. 5): "Our lower
bounds on the other hand hold against oblivious adversaries who fix the value and BR oracles with
knowledge of the algorithm, but before the algorithm's random bits (if any) are drawn."; §5,
printed p. 12 (PDF p. 13): "Because the response maps are fixed".

**Formalization Note** The published `BRAdversary` is call-indexed (adaptive); obliviousness is
the restriction that every call index gives the same answer, for maximizing and minimizing queries
alike, `⊥` queries included. -/
def IsOblivious {A B : Type*} {M : A → B → ℚ} {δ : ℝ} (adv : BRAdversary M δ) : Prop :=
  (∀ n n' q, adv.row n q = adv.row n' q) ∧ (∀ n n' p, adv.col n p = adv.col n' p)

end NashOrTriangle.Supplement


