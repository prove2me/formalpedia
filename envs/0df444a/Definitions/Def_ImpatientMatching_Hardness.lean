-- Prove2me | Definitions.Def_ImpatientMatching_Hardness
-- name    : ImpatientMatching_Hardness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:16.971634+00:00
-- url     : https://prove2.me/theorems/5aaeff16-5841-470d-bbf2-dbef8f8b4fbc
-- title:
--   The promise problem, estimation hardness, and PTAS
-- statement:
--   For a regime and a rational $\eta$, the **YES** side of the promise on a pair $(I,b)$ is $g^*/\Lambda\ge b+\eta$, and the **NO** side is $g^*/\Lambda\le b-\eta$, both with $b>0$ and $\Lambda>0$.
--
--   **Estimation is NP-hard at accuracy $\delta$** when every NP language over every finite nonempty alphabet maps in deterministic polynomial time to a pair $(I,b)$ such that, for every real $\hat g$ with
--   $$|\hat g-g^*(I)|\le\delta\,g^*(I),$$
--   membership of the word is equivalent to $b\Lambda<\hat g$.
--
--   An algorithm family is a **polynomial-time approximation scheme** when, for each fixed rational $\delta'>0$, one polynomial-time algorithm maps the encoding of every input to a rational within $\delta'g^*$. The proposition $\mathrm P=\mathrm{NP}$ is stated on the classes of the published `CookPvsNP`.
--
--   **Formalization Note** The promise sides are written $(b+\eta)\Lambda\le g^*$ and $g^*\le(b-\eta)\Lambda$. The clause $\Lambda>0$ matters: an empty input would otherwise satisfy both sides. The estimate reading follows the source's proof on p.11–12, where comparison of $\hat g/\Lambda$ with $b$ solves the promise problem.
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §1.3, p.6; §3.2, pp.8–9; (12), p.11

import Definitions.Def_ImpatientMatching_Value
import Definitions.Def_SetCoverThreshold_SetCover_Complexity

namespace ImpatientMatching

/-- The YES side of the promise (12), p.11: `g∗/Λ ≥ b + η` with `b > 0` and `Λ > 0`.

**Formalization Note.** Written `(b + η)Λ ≤ g∗`. Without `0 < Λ`, an empty input would satisfy
both sides for every `b > η` and the hardness claim would be empty; the source's instances have
`Λ > 0`. -/
def gapYes (r : Regime) (η : ℚ) (p : MatchInput × ℚ) : Prop :=
  0 < p.2 ∧ 0 < totalRate p.1 ∧
    ((((p.2 : ℝ) + (η : ℝ)) * totalRate p.1 : ℝ) : EReal) ≤ gStar (toInstance r p.1)

/-- The NO side of the promise (12), p.11: `g∗/Λ ≤ b − η` with `b > 0` and `Λ > 0`. -/
def gapNo (r : Regime) (η : ℚ) (p : MatchInput × ℚ) : Prop :=
  0 < p.2 ∧ 0 < totalRate p.1 ∧
    gStar (toInstance r p.1) ≤ ((((p.2 : ℝ) - (η : ℝ)) * totalRate p.1 : ℝ) : EReal)

/-- "Computing a numerical estimate `ĝ` with `|ĝ − g∗| ≤ δ g∗` is NP-hard" (Theorem 3.2, p.8; §1.3,
p.6): every NP language over every finite nonempty alphabet maps in deterministic polynomial time
to an input `I` and a rational `b`, so that comparing any such estimate with `bΛ` decides the
language. -/
def EstimationNPHard (r : Regime) (δ : ℝ) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.NP Sym' →
      ∃ f : List Sym' → MatchInput × ℚ,
        CookPvsNP.PolyTimeComputable (fun x => encPromise (f x)) ∧
        ∀ (x : List Sym') (ghat : ℝ),
          |ghat - gStarReal r (f x).1| ≤ δ * gStarReal r (f x).1 →
            (x ∈ L' ↔ ((f x).2 : ℝ) * totalRate (f x).1 < ghat)

/-- `P = NP`, on the classes of the published `CookPvsNP`. -/
def PEqNP : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym

/-- A polynomial-time approximation scheme for `g∗` (Theorem 3.2, p.9): for each fixed rational
accuracy `δ' > 0`, one polynomial-time algorithm that maps the encoding of every input to the encoding
of a rational within `δ' g∗`. -/
def AdmitsPTAS (r : Regime) : Prop :=
  ∀ δ' : ℚ, 0 < δ' → ∃ A : List Bool → List Bool, CookPvsNP.PolyTimeComputable A ∧
    ∀ I : MatchInput, ∃ ghat : ℚ, A (encInput I) = encRat ghat ∧
      |(ghat : ℝ) - gStarReal r I| ≤ (δ' : ℝ) * gStarReal r I

end ImpatientMatching


