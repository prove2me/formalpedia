-- Prove2me | Definitions.Def_KarpLiptonOM_InP
-- name    : KarpLiptonOM_InP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:34.792201+00:00
-- url     : https://prove2.me/theorems/b790fa6c-88ea-4294-8ea3-2f4b25c1677d
-- title:
--   $L \in \mathrm P^\Pi$ (Definition A.2.1)
-- statement:
--   Let $\Pi$ be a promise problem. A language $L$ is in $\mathrm P^\Pi$ if there is a deterministic polynomial-time oracle machine $M$ such that
--   $$
--   M^O \text{ decides } L \quad \text{for every language } O \text{ consistent with } \Pi .
--   $$
--   Queries in $\Pi_{\mathrm{YES}} \cup \Pi_{\mathrm{NO}}$ are answered correctly and all other queries arbitrarily (loose access); for deterministic machines this is the same as correctness with every consistent oracle language. For a language $A$, $\mathrm P^A = \mathrm P^{(A, \overline A)}$ is the usual class.
--
--   **Formalization Note** Machines may repeat queries; with a fixed oracle language the answers repeat, so the paper's convention that machines never repeat a query changes nothing.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.1, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_Accepts
import Definitions.Def_KarpLiptonOM_Consistent
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- `L ∈ P^Π` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Definition A.2.1, p.21): a deterministic polynomial-time oracle machine `M`
such that `M^O` decides `L` for **every** language `O` consistent with `Π`.

**Formalization Note** This is loose access in the form the paper fixes for deterministic machines
(p.21: "We use the latter form throughout"). The paper also assumes such machines never repeat a
query; with a fixed oracle language a repeated query gets the same answer, so this changes no class. -/
def InP (PP : PromiseProblem) (L : Set (List Bool)) : Prop :=
  ∃ (M : OracleTM) (k : ℕ), M.IsPolyTime k ∧
    ∀ O, Consistent O PP → ∀ x : List Bool, x ∈ L ↔ M.Accepts O (tupleEnc [x])

end KarpLiptonOM


