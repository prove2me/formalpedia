-- Prove2me | Definitions.Def_QSDMixing_GU_cosetFintype
-- name    : QSDMixing_GU_cosetFintype
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:15.414472+00:00
-- url     : https://prove2.me/theorems/9cd67866-d78d-4bd0-bd6e-d0df2be47d6b
-- title:
--   The finite coset space $G/H$
-- statement:
--   For a finite group $G$ and a subgroup $H$, the coset space $G/H$ carries one chosen structure of a finite type with decidable equality, which every matrix on $G/H$ in this development uses.
--
--   **Formalization Note** These are scoped typeclass instances, $\mathrm{Fintype.ofFinite}$ and classical decidable equality. Quantities defined from them do not depend on the choice.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17

import Mathlib

set_option autoImplicit false

namespace QSDMixing.GU

/-- The finite coset space `G ⧸ H`, with the one `Fintype` structure used throughout this development. -/
noncomputable scoped instance cosetFintype {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    Fintype (G ⧸ H) := Fintype.ofFinite _

/-- Classical decidable equality on `G ⧸ H`, the one used throughout this development. -/
noncomputable scoped instance cosetDecEq {G : Type} [Group G] (H : Subgroup G) :
    DecidableEq (G ⧸ H) := Classical.decEq _

end QSDMixing.GU


