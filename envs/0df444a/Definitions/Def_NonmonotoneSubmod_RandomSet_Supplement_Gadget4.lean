-- Prove2me | Definitions.Def_NonmonotoneSubmod_RandomSet_Supplement_Gadget4
-- name    : NonmonotoneSubmod_RandomSet_Supplement_Gadget4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:13:40.928198+00:00
-- url     : https://prove2.me/theorems/11150574-a9e2-4c50-b9de-6385166bc4a7
-- title:
--   Theorem 4.1 proof — the eight-element parity gadget
-- statement:
--   For each of four Boolean positions, introduce a true and a false element. A valid selection contains exactly one element from each pair, and its parity is the xor of the selected true bits. For a set $S$ of these eight elements and right-hand parity bit $b$, the entire rational table is
--   $$g_b(S)=\begin{cases}|S|&|S|<4,\\8-|S|&|S|>4,\\4&|S|=4\text{ and the assignment satisfies parity }b,\\8/3&|S|=4\text{ and the valid assignment fails parity }b,\\10/3&|S|=4\text{ and the selection is invalid}.\end{cases}$$
--
--   The table is a proof object for Theorem 4.1. Its submodularity and the hardness conclusion are proof obligations, rather than assumptions bundled into this definition. The valid-selection predicate and parity function are shared with the six-element gadget.
--
--   **Formalization Note** Positions are numbered from zero and the code uses exact rational values; true and false are explicit Boolean labels.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4):1133–1153, 2011, DOI 10.1137/090779346; p. 1145, proof of Theorem 4.1, four bullet points

import Mathlib
open Classical

namespace NonmonotoneSubmod.RandomSet.Supplement

/-- A valid local selection chooses exactly one truth label for every variable. -/
def ValidSelection {d : ℕ} (S : Finset (Fin d × Bool)) : Prop :=
  ∀ i, ((i, false) ∈ S ↔ (i, true) ∉ S)

def selectionParity {d : ℕ} (S : Finset (Fin d × Bool)) : Bool :=
  (List.finRange d).foldl (fun b i => Bool.xor b (decide ((i, true) ∈ S))) false

/-- Complete eight-element table in the proof of Theorem 4.1, p.1145. -/
noncomputable def gadget4 (rhs : Bool) (S : Finset (Fin 4 × Bool)) : ℚ :=
  if S.card < 4 then S.card
  else if 4 < S.card then 8 - (S.card : ℚ)
  else if ValidSelection S then
    if selectionParity S = rhs then 4 else 8 / 3
  else 10 / 3

end NonmonotoneSubmod.RandomSet.Supplement


