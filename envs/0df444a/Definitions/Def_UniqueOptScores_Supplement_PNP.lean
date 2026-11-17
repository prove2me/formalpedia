-- Prove2me | Definitions.Def_UniqueOptScores_Supplement_PNP
-- name    : UniqueOptScores_Supplement_PNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:52:46.3207+00:00
-- url     : https://prove2.me/theorems/7440d6a0-c4ed-46a2-abcf-64bc6e9859cd
-- title:
--   The class $\Delta^{\mathrm P}_2=\mathrm P^{\mathrm{NP}}$
-- statement:
--   A language $L$ belongs to $\Delta^{\mathrm P}_2=\mathrm P^{\mathrm{NP}}$ if it is decided by a deterministic polynomial-time oracle machine $M$ with an oracle for a language $B\in\mathrm{NP}$:
--   $$x\in L\iff M^{B}\text{ accepts }x .$$
--   The queries may be adaptive: each query may depend on the answers to earlier queries.
--
--   This class supplies the predicates of symmetric alternation $\mathrm S_2^{\mathrm{NP}}$.
--
--   **Formalization Note** The paper fixes one NP-complete oracle language; here the oracle is any language of the base mission's $\mathrm{NP}$ (at the empty oracle). This is the same class: an NP-complete language is in NP, and every query to some $B\in\mathrm{NP}$ is answered by one query to an NP-complete language after a polynomial-time reduction. The polynomial clock must hold for every oracle, as in the base mission.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15), "Bounded access to NP"

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_output
import Definitions.Def_UniqueOptScores_NP

namespace UniqueOptScores

namespace Supplement

/-- **The class Δ^P_2 = P^NP.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15): "The class Δ^P_2 = P^NP consists of languages decidable by a
deterministic polynomial-time machine with an oracle for a fixed NP-complete language. The queries
may be adaptive: each query may depend on the answers to earlier queries."

`L ∈ PNP` if there are a language `B ∈ NP` and a clocked deterministic oracle machine `M` such
that `x ∈ L` exactly when `M` with oracle `B` accepts `x`.

**Formalization Note.** NP is the base mission's `NP ∅`. The oracle ranges over every NP language
instead of one fixed NP-complete language: this gives the same class (an NP-complete oracle is in
NP, and a query to any `B ∈ NP` is answered by one query to an NP-complete language after a
polynomial-time reduction). Queries are adaptive (the machine sees each answer before the next
query). The clock holds for every oracle (`IsClocked`, p.15). -/
def PNP : Set (Set (List Bool)) :=
  {L | ∃ B ∈ NP ∅, ∃ (M : HMBinPacking.OracleMachine) (t : Polynomial ℕ), IsClocked M t ∧
    ∀ x : List Bool, x ∈ L ↔ output M B x = [true]}

end Supplement

end UniqueOptScores


