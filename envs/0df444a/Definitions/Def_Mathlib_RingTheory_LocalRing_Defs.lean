-- Prove2me | Definitions.Def_Mathlib_RingTheory_LocalRing_Defs
-- name    : Mathlib_RingTheory_LocalRing_Defs
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/818eb4da-435f-5651-a031-eb112207aca5
-- title:
--   Local ring structure on quotients of a local ring
-- statement:
--   The standing context is a commutative ring $R$ that is local, an ideal $I \subseteq R$, and the assumption that the quotient ring $R/I$ is nontrivial. Two instances are registered under these hypotheses.
--
--   The first, [`IsLocalRing.quot`](../def/Mathlib_RingTheory_LocalRing_Defs.html#L7), asserts that $R/I$ is again a local ring in Mathlib's sense (nontrivial, with the non-units closed under addition, equivalently a unique maximal ideal). It is obtained from the general fact that a nontrivial ring which is the image of a local ring under a surjective ring homomorphism is local, applied to the canonical projection $R \to R/I$, whose surjectivity is `Ideal.Quotient.mk_surjective`.
--
--   The second, [`IsLocalHom.quotient_mk`](../def/Mathlib_RingTheory_LocalRing_Defs.html#L9), asserts that the canonical map $R \to R/I$, taken in its guise as the algebra map `algebraMap R (R ⧸ I)`, is a local homomorphism: an element $a \in R$ whose residue class in $R/I$ is a unit is itself a unit of $R$. Equivalently, the preimage of the maximal ideal of $R/I$ is the maximal ideal of $R$. This too comes from surjectivity of the projection, via the corresponding statement for surjective homomorphisms out of a local ring.
--
--   **Relation to Mathlib.** Both facts are instances packaging Mathlib lemmas (`IsLocalRing.of_surjective'` and `IsLocalHom.of_surjective`) for the special case of a quotient ring, so that Lean's instance search finds the local ring structure on `R ⧸ I` and the locality of `algebraMap R (R ⧸ I)` automatically; no new notion is introduced.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/RingTheory/LocalRing/Defs.lean` — © 2025 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_LocalRing_Defs.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]

open IsLocalRing

instance IsLocalRing.quot : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective

instance IsLocalHom.quotient_mk : IsLocalHom (algebraMap R (R ⧸ I)) :=
  .of_surjective _ Ideal.Quotient.mk_surjective


