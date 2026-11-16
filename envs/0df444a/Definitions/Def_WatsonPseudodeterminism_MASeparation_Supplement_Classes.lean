-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_Classes
-- name    : WatsonPseudodeterminism_MASeparation_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:29:02.624523+00:00
-- url     : https://prove2.me/theorems/7bda641b-e918-4f9b-86fe-d2ad4a8e147b
-- title:
--   The communication classes RP, ZPP = RP ∩ coRP and psP for families
-- statement:
--   Let $F=(F_t)_t$ be a family of two-party partial Boolean functions on pairs of $N_t$-bit strings, and write $\ell(N)=\lfloor\log_2 N\rfloor+1$. The complemented family $\overline F$ has the same lengths and functions $\overline{F_t}$.
--
--   1. $F\in\mathrm{RP}$ if $N_t\to\infty$ and there is one natural constant $C$ such that every $F_t$ has an RP-type protocol of cost at most $C\,\ell(N_t)^C$.
--   2. $F\in\mathrm{ZPP}$ if $F\in\mathrm{RP}$ and $\overline F\in\mathrm{RP}$, i.e.
--   $$\mathrm{ZPP}=\mathrm{RP}\cap\mathrm{coRP}.$$
--   3. $F\in\mathrm{psP}$ if $N_t\to\infty$ and there is one natural constant $C$ such that every $F_t$ has a psP-type protocol (error $1/3$) of cost at most $C\,\ell(N_t)^C$.
--
--   These are the communication analogues of the classical classes, with "efficient" meaning polylogarithmic cost in the input length, as in the base mission's MA and N·BPP classes.
--
--   **Formalization Note** The family structure and the growth condition are the base mission's published `Families` definition; the cost shape $C(\lfloor\log_2N\rfloor+1)^C$ is the same as in its classes MA and N·BPP. ZPP is defined through the identity $\mathrm{ZPP}=\mathrm{RP}\cap\mathrm{coRP}$ that the paper recalls on p. 2 and uses literally in §3.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §1, pp. 1–2 (classes; "Recall ZPP = RP ∩ coRP", p. 2); §1.1, p. 3 (families, polylog N); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Families
import Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_Models

namespace WatsonPseudodeterminism.MASeparation.Supplement

/-- The complemented family F̄: same input lengths, each function complemented. -/
def complementFamily (F : Family) : Family where
  length := F.length
  fn t := complementFn (F.fn t)

/-- RP: a growing family with RP-type cost at most C(⌊log₂ N⌋ + 1)^C, one C for the family. -/
def InRP (F : Family) : Prop :=
  Growing F ∧ ∃ C : ℕ, ∀ t, ∃ d : ℕ,
    d ≤ C * (Nat.log 2 (F.length t) + 1) ^ C ∧ RPProtocol (F.fn t) d

/-- §1, p. 2: "Recall ZPP = RP ∩ coRP". -/
def InZPP (F : Family) : Prop :=
  InRP F ∧ InRP (complementFamily F)

/-- psP: a growing family with psP-type (error 1/3) cost at most C(⌊log₂ N⌋ + 1)^C. -/
def InPsP (F : Family) : Prop :=
  Growing F ∧ ∃ C : ℕ, ∀ t, ∃ d : ℕ,
    d ≤ C * (Nat.log 2 (F.length t) + 1) ^ C ∧ PsPProtocol (F.fn t) d

end WatsonPseudodeterminism.MASeparation.Supplement


