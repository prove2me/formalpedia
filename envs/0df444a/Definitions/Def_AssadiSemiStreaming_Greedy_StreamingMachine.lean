-- Prove2me | Definitions.Def_AssadiSemiStreaming_Greedy_StreamingMachine
-- name    : AssadiSemiStreaming_Greedy_StreamingMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:38:31.603344+00:00
-- url     : https://prove2.me/theorems/9ebb8f84-8756-4965-bcb5-a499ae76c307
-- title:
--   One-pass randomized finite-output streaming machines
-- statement:
--   A generic machine reads an ordered list once. With s bits it has 2^s available retained states, an input-independent initial probability law, a transition law depending only on the retained state and current input symbol, and an output law depending only on the final state. The input and output alphabets are parameters. Successive transitions compose by probability-law binding. Fresh random coins and unrestricted transition computation are allowed. Every retained private random bit and every remembered input datum belongs to the counted state; unused states are allowed. Deterministic machines are obtained with point masses. There is no input-dependent advice, graph access, or uncharged transcript at output.
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), §1, printed p. 1 / PDF 3; §3.2 footnote 6, printed p. 6 / PDF 8

import Mathlib

namespace AssadiSemiStreaming.Greedy

/-- A generic one-pass randomized machine. Its finite retained state accounts
for every stored bit, including retained randomness. No computation-time bound. -/
structure StreamingMachine (Input Output : Type) (s : ℕ) where
  initial : PMF (Fin (2 ^ s))
  step : Fin (2 ^ s) → Input → PMF (Fin (2 ^ s))
  output : Fin (2 ^ s) → PMF Output

noncomputable def StreamingMachine.law {Input Output : Type} {s : ℕ}
    (A : StreamingMachine Input Output s) (stream : List Input) : PMF Output :=
  (stream.foldl (fun q e => q.bind (fun st => A.step st e)) A.initial).bind A.output

end AssadiSemiStreaming.Greedy


