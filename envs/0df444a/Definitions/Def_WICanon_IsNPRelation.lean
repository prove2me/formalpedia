-- Prove2me | Definitions.Def_WICanon_IsNPRelation
-- name    : WICanon_IsNPRelation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:40.463132+00:00
-- url     : https://prove2.me/theorems/64ceff21-95c7-43d0-a66c-6671a911150a
-- title:
--   NP relations, $\mathcal L(\mathcal R)$ and witness bounds
-- statement:
--   A relation $\mathcal R\subseteq\{0,1\}^*\times\{0,1\}^*$ has the language $\mathcal L(\mathcal R)=\{x\mid\exists w:(x,w)\in\mathcal R\}$. It is an **NP relation** with witness bound $q$ if membership of $(x,w)$ is decidable in polynomial time and $(x,w)\in\mathcal R$ implies $|w|\le q(|x|)$.
--
--   **Formalization Note** The paper names no machine model. Polynomial time is the published `QAlgorithms.Complexity.PolyTimeComputable`, Mathlib's `TM2ComputableInPolyTime` on `List Bool`, in all items of the mission.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), §2.1, p.12; p.31

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_pair

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QiOPoQ

/-- A relation `R ⊆ {0,1}* × {0,1}*` (Arnon, Mazor, Pass, Silbak, STOC 2027 submission manuscript,
sha256 3f78ec3d…, §2.1, p.12). -/
abbrev Relation := Str → Str → Prop

/-- `x ∈ L(R) = {x | ∃w : (x, w) ∈ R}` (§2.1, p.12). -/
def InLang (R : Relation) (x : Str) : Prop := ∃ w, R x w

/-- Witnesses of `R` have length at most `q(|x|)` ("Let p_R be a polynomial upper bound on the
witness length of R", p.31). -/
def WitnessBound (R : Relation) (q : Polynomial ℕ) : Prop :=
  ∀ x w, R x w → w.length ≤ q.eval x.length

/-- **NP relation** (§2.1, p.12; p.31): polynomial-time decidable, with polynomially bounded
witnesses.

**Formalization Note.** Decidability uses the published `PolyTimeComputable` (Mathlib
`TM2ComputableInPolyTime` on `List Bool`), the one machine model of the whole mission; the paper
names none. -/
def IsNPRelation (R : Relation) (q : Polynomial ℕ) : Prop :=
  (∃ χ : Str → Str, PolyTimeComputable χ ∧ ∀ x w, χ (pair x w) = bitStr true ↔ R x w) ∧
    WitnessBound R q

end WICanon


