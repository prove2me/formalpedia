-- Prove2me | Definitions.Def_PrivLittlestone_challengeIndicator
-- name    : PrivLittlestone_challengeIndicator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:09.927836+00:00
-- url     : https://prove2.me/theorems/4e4edfa3-e014-4ffd-9a5e-b5fd5e70ef68
-- title:
--   Challenge indicator $\chi(H, e)$
-- statement:
--   $\chi(H, e) \in \{0,1\}$ indicates that the replay of the phase starting at $H$ through the endpoint $e$ contains the unequal record pair: some round of the phase up to the endpoint has $z^0_i \neq z^1_i$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma B.2, p.22

import Mathlib
import Definitions.Def_PrivLittlestone_Adversary
import Definitions.Def_PrivLittlestone_contPrefix

namespace PrivLittlestone

open Classical in
/-- The **challenge indicator** `χ(H, e)` (He–He, *Private Online Learning of Littlestone Classes
and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Lemma B.2, p.22):
`1` if the replay through the endpoint `e` of the phase starting at `t₀` (past classifiers, then
the aggregate `g`) contains the unequal record pair, i.e. some round `t₀ ≤ i ≤ k` (`i < T` for
`e = (T, no-cross)`) has `z⁰_i ≠ z¹_i`; `0` otherwise. -/
noncomputable def challengeIndicator {X : Type*} {T : ℕ} (adv : Adversary X T)
    (past : Fin T → X → Bool) (t₀ : ℕ) (g : X → Bool) (e : ℕ × Bool) : ℕ :=
  if ∃ i : Fin T, t₀ ≤ (i : ℕ) ∧ (i : ℕ) ≤ e.1 ∧
      (adv i (contPrefix past t₀ g i)).1 ≠ (adv i (contPrefix past t₀ g i)).2 then 1 else 0

end PrivLittlestone


