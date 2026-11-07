-- Prove2me | Definitions.Def_SublinearSteiner_ScoreEstimator
-- name    : SublinearSteiner_ScoreEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:46:24.83622+00:00
-- url     : https://prove2.me/theorems/9015a536-c242-422a-88ad-33937fc824e9
-- title:
--   The score of a uniform retained point and the estimate $Z$
-- statement:
--   The score from the proof of Lemma 4.8. Sample a uniform retained point and let $C$ be its component in $G_a(N)$. If $|C|>B$ the score is $0$; if $C\in\mathcal C_0$ it is $1/|C|$; if $C\in U$, then with probability $1/|C|$ run the matching oracle $\mathrm{VO}$ at $C$ with fresh ranks and score half of the matched indicator, and otherwise score $0$.
--
--   With $\hat\vartheta$ the empirical mean of independent samples,
--   $$Z=\max\{0,\ g_-\max\{0,\hat\vartheta-\xi\}-2s\}.$$
--
--   **Formalization Note.** One sample is a retained point, a coin of bias $1/|C|$ and an order of the copies, with the explicit probability `scoreWeight`.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), proof of Lemma 4.8, p.25

import Mathlib
import Definitions.Def_SublinearSteiner_Statistics
import Definitions.Def_SublinearSteiner_Multigraph

open scoped Classical

namespace SublinearSteiner

/-!
# The score of a uniform retained point and the estimate `Z`

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), proof of Lemma 4.8, p.25.

"For the score, explore the component `C` of a uniform retained point. If it is large the score is `0`; if `C ∈ C0` it
is `1/|C|`; if `C ∈ U`, then with probability `1/|C|` we run the matching oracle at `C` with fresh ranks and score half
of the matched indicator, and otherwise score `0`. Let `ϑ̂` be the empirical mean and
`Z = max{0, g₋ max{0, ϑ̂ − ξ} − 2s}`."

**Formalization Note.** One sample is a retained point, a coin of bias `1/|C|` and an order of the copies; its law is
the finite weight `scoreWeight`. Samples are independent, with weight the product over the samples. The oracle is
`VO` of the multigraph module, run with a fresh memo table.
-/

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- One sample: a retained point, a coin, and an order of the copies. -/
abbrev ScoreSample (N : Finset (Fin n)) (E : Type) [Fintype E] := ↥N × Bool × Multigraph.Order E

/-- The score of one sample (p.25). -/
noncomputable def scoreValue (w : FinMetric n) (T N S : Finset (Fin n)) (a : ℝ) (B : ℕ)
    (H : Multigraph ↥(restComps w T N S a B) E) (s : ScoreSample N E) : ℝ :=
  let C := component w N a s.1
  if B < C.card then 0
  else if hU : C ∈ restComps w T N S a B then
    (if s.2.1 = true ∧ (Multigraph.vo H s.2.2 ⟨C, hU⟩).1.isSome = true then 1 / 2 else 0)
  else 1 / (C.card : ℝ)

/-- The probability of one sample: a uniform retained point `x`, a coin of bias `1/|C|` for the component `C` of `x`, and
a uniform order. -/
noncomputable def scoreWeight (w : FinMetric n) (N : Finset (Fin n)) (a : ℝ) (s : ScoreSample N E) : ℝ :=
  (N.card : ℝ)⁻¹ *
    (if s.2.1 = true then 1 / ((component w N a s.1).card : ℝ) else 1 - 1 / ((component w N a s.1).card : ℝ)) *
    (Fintype.card (Multigraph.Order E) : ℝ)⁻¹

/-- `Z = max{0, g₋ max{0, ϑ̂ − ξ} − 2s}` (p.25). -/
noncomputable def scoreEstimate (gm ξ : ℝ) (s : ℕ) (θ : ℝ) : ℝ :=
  max 0 (gm * max 0 (θ - ξ) - 2 * s)

end SublinearSteiner


