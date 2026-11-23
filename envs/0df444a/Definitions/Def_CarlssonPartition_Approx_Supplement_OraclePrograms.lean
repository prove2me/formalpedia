-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_OraclePrograms
-- name    : CarlssonPartition_Approx_Supplement_OraclePrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:27:11.478176+00:00
-- url     : https://prove2.me/theorems/2fea3fae-b9c4-4e7a-a157-2b454d98ea65
-- title:
--   §4 — adaptive exact-oracle programs with an interaction-derived query count
-- statement:
--   A deterministic adaptive query program sees only the finite transcript of its previous questions and their answers. At each step it either issues a new question or returns an output. Public parameters may select the program before the unknown oracle is supplied. A terminating interaction satisfies
--   $$
--   N(\mathrm{return})=0,\qquad N(\mathrm{query\ followed\ by\ a\ run})=1+N(\mathrm{run}).
--   $$
--   The inductive run relation derives both the returned output and the actual number of oracle calls from the same interaction. It cannot attach a fabricated count to an independently chosen output. Internal exact calculations are uncharged, as appropriate for the source's integration-oracle call bound. This reusable definition is separate from planar density and partition data.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §4.1–§4.3, pp. 18–21 (PDF 19–22); proof of Theorem 10, p. ec12 (PDF 49)

import Mathlib

namespace CarlssonPartition.Approx.Supplement

/-- A deterministic adaptive oracle program. Its only changing input is the finite
transcript of questions and answers; it either asks another question or returns an
output. Public problem parameters can select the program before the oracle is known.
Only oracle calls are charged in this model, not intervening exact computations. -/
structure QueryProgram (Q A O : Type*) where
  next : List (Q × A) → Q ⊕ O

/-- Actual terminating interaction with an oracle, starting at the displayed history.
The query count is derived from the interaction: stopping costs zero and a question
costs exactly one. It is not a scalar supplied independently of the program's output. -/
inductive QueryProgram.Runs {Q A O : Type*} (P : QueryProgram Q A O) (oracle : Q → A) :
    List (Q × A) → O → ℕ → Prop where
  | stop (h : List (Q × A)) (o : O) (hp : P.next h = Sum.inr o) :
      P.Runs oracle h o 0
  | ask (h : List (Q × A)) (q : Q) (o : O) (n : ℕ)
      (hp : P.next h = Sum.inl q)
      (rest : P.Runs oracle (h ++ [(q, oracle q)]) o n) :
      P.Runs oracle h o (n + 1)

end CarlssonPartition.Approx.Supplement


