-- Prove2me | Definitions.Def_FirstChoiceDesign_ExtractsRandomAssignment
-- name    : FirstChoiceDesign_ExtractsRandomAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:56.189242+00:00
-- url     : https://prove2.me/theorems/75327678-2236-437e-90b2-5a081897c7a4
-- title:
--   Definition 2 — the first-choice research design extracts a random assignment
-- statement:
--   **Definition 2.** The first-choice research design extracts a random assignment for a gDA mechanism $\varphi$ if for any assignment problem $X$, any school $s$, any potential lottery realization $r$, and any students $j,k\in\mathit{First}_s(r)$,
--
--   $$
--   P(D_{js}(R)=1)=P(D_{ks}(R)=1).
--   $$
--
--   This is the requirement that makes offers within $\mathit{First}_s$ comparable to a randomized trial: the propensity score is constant over the group.
--
--   **Formalization Note** Probabilities are the values in $[0,\infty]$ of `lotteryLaw` at the sets of profiles. The first display of the source is formalized, not its "equivalent requirement" with types.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Definition 2, p.10

import Definitions.Def_FirstChoiceDesign_First
import Definitions.Def_FirstChoiceDesign_lotteryLaw

namespace FirstChoiceDesign

/-- Definition 2, p.10: the first-choice research design extracts a random assignment for `φ`. For
any assignment problem `X`, any school `s`, any potential lottery realization `r` and any students
`j, k ∈ First_s(r)`, `P(D_js(R) = 1) = P(D_ks(R) = 1)`.

**Formalization Note** The probabilities are values in `ℝ≥0∞` of `lotteryLaw`, which is the law of
`R`. Problems range over all student and school counts, with priorities in `{1, …, φ.K n}`. -/
def ExtractsRandomAssignment (φ : GDA) : Prop :=
  ∀ (n m : ℕ) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m), Potential φ.regime r →
    ∀ j ∈ First φ X s r, ∀ k ∈ First φ X s r,
      lotteryLaw (n := n) (m := m) φ.regime {R | D φ X j s R} =
        lotteryLaw (n := n) (m := m) φ.regime {R | D φ X k s R}

end FirstChoiceDesign


