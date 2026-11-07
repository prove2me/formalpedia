-- Prove2me | Definitions.Def_TangleStructTree_IsRich
-- name    : TangleStructTree_IsRich
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:00.695212+00:00
-- url     : https://prove2.me/theorems/450ffdb1-ca4e-4180-a9be-dd8ac865bb41
-- title:
--   Rich sets $\mathcal F$
-- statement:
--   Let $\vec S$ be an ordered separation system.
--
--   **Definition 4.3.** A set $\mathcal F$ is **rich** for $\vec S$ if every consistent orientation $\tau$ of $S$ that has a subset in $\mathcal F$ also has a subset in $\mathcal F$ that is strongly efficient in $\tau$.
--
--   Richness is the condition on $\mathcal F$ under which thoroughly ordered $\mathcal F$-tangle structure trees exist, and for injective order functions it is also necessary.
--
--   **Formalization Note** Strong efficiency depends on the order function, which is an argument `ord` of the predicate.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Definition 4.3, p.9 (PDF 20)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_StronglyEfficient

namespace TangleStructTree

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Definition 4.3** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.9 (PDF 20)): a set `ℱ` is
**rich** for `S⃗` if every consistent orientation `τ` of `S` that has a subset in `ℱ` also has a
subset in `ℱ` that is strongly efficient in `τ` (footnote 11: "in this orientation of S").

**Formalization Note** `ord` is the order function of the ordered separation system (strong
efficiency depends on it). -/
def IsRich (ord : E → ℝ) (ℱ : Set (Set E)) : Prop :=
  ∀ τ : Set E, IsOrientation τ → IsConsistent τ → ¬ Avoids ℱ τ →
    ∃ σ ∈ ℱ, StronglyEfficient ord σ τ

end TangleStructTree


