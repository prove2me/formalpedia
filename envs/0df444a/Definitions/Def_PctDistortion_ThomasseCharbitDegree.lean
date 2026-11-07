-- Prove2me | Definitions.Def_PctDistortion_ThomasseCharbitDegree
-- name    : PctDistortion_ThomasseCharbitDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:53.946029+00:00
-- url     : https://prove2.me/theorems/b7193ccf-3c3e-4a11-9908-2961eaccec77
-- title:
--   The degree condition of Theorem B
-- statement:
--   For $\alpha\in[1/2,1)$ let $s=\lfloor 1/(1-\alpha)\rfloor$. The **degree condition** at $\alpha$ says that every α-majority digraph $G=(V,E)\in M_\alpha$ has a vertex $w$ with
--   $$\deg^-(w)\le\frac{|V|}{s}.$$
--   This is the condition of Theorem B. With strict inequality it is the Thomassé–Charbit conjecture (Conjecture 1, p.18), a special case of the Caccetta–Häggkvist conjecture.
--
--   **Formalization Note** $s$ is the natural-number floor and the division is real. The condition ranges over the α-majority digraphs of all finite elections with nonempty voter and candidate sets.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem B, p.4; Conjecture 1, p.18

import Mathlib
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_inDeg

set_option autoImplicit false

namespace PctDistortion

/-- The **degree condition of Theorem B** (the Thomassé–Charbit condition, non-strict form) at
percentile `α`: every α-majority digraph `G = (V, E)` of a finite election has a vertex of
in-degree at most `|V| / ⌊1/(1−α)⌋`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem B, p.4: "every α-majority digraph G = (V, E) has a vertex of in-degree at most
|V|/⌊1/(1−α)⌋."

**Formalization Note.** `⌊1/(1−α)⌋` is `Nat.floor`; the division is real. The condition ranges
over all of `M_α` (`IsAlphaMajority`), i.e. over the α-majority digraphs of all finite elections
with nonempty voter and candidate sets. Conjecture 1 (p.18) states the same with strict `<`;
Theorem B uses "at most". -/
def ThomasseCharbitDegree (α : ℝ) : Prop :=
  ∀ (W : Type) [Fintype W] (G : Digraph W), IsAlphaMajority α G →
    ∃ w, (inDeg G w : ℝ) ≤ (Fintype.card W : ℝ) / (⌊1 / (1 - α)⌋₊ : ℝ)

end PctDistortion


