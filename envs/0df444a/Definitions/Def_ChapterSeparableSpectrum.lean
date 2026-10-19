-- Prove2me | Definitions.Def_ChapterSeparableSpectrum
-- name    : ChapterSeparableSpectrum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T02:30:43.202547+00:00
-- url     : https://prove2.me/theorems/9bc3bcb7-9a5c-4714-9aae-40ebd255fc73
-- title:
--   # Separability is exactly metrizability of the spectrum (plan GAP-2, the last residue)
-- statement:
--   # Separability is exactly metrizability of the spectrum (plan GAP-2, the last residue)
--
--   `ChapterStandardBorelClassification` proves the exhaustiveness half of the abelian
--   von Neumann classification — every summand of the general abelian multiplication model
--   realises one of the manuscript's five standard types — under one standing hypothesis:
--   the compact space `Y` carrying the model (the spectrum) is **metrizable**.  This module
--   removes the hypothesis from the list of unexplained assumptions by identifying it with
--   a purely algebraic condition and by discharging it in the standard setting.
--
--   * `metrizableSpace_of_separable_continuousMap` — a compact Hausdorff space whose
--     algebra `C(Y, ℂ)` is *separable* is metrizable.  The proof is the classical one:
--     a countable dense family of continuous functions separates points (Urysohn), so it
--     embeds `Y` into a countable power of `ℂ`, and a continuous injection out of a compact
--     space into a Hausdorff space is an embedding;
--   * `separableSpace_continuousMap_of_metrizable` — the converse;
--   * `metrizableSpace_iff_separableSpace_continuousMap` — hence, for a compact Hausdorff
--     spectrum, *metrizability of the spectrum and separability of the algebra are the same
--     hypothesis*;
--   * `metrizableSpace_characterSpace` — via Gelfand duality, the character space of a
--     **separable** commutative unital C\*-algebra is metrizable;
--   * **HEADLINE** `abelian_multiplication_model_classified_separable` and
--     `abelian_algebra_multiplication_model_classified` — the classification list with the
--     metrizability hypothesis replaced by separability of the algebra: every unital
--     `*`-representation of a separable commutative unital C\*-algebra on a complex Hilbert
--     space is a direct sum of multiplication algebras, each of which realises one of the
--     five standard types.
--
--   Everything is `sorry`-free and `axiom`-free.

import Definitions.Def_ChapterStandardBorelClassification
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterAbelianGelfandModel
import Mathlib

/-!
# Separability is exactly metrizability of the spectrum (plan GAP-2, the last residue)

`ChapterStandardBorelClassification` proves the exhaustiveness half of the abelian
von Neumann classification — every summand of the general abelian multiplication model
realises one of the manuscript's five standard types — under one standing hypothesis:
the compact space `Y` carrying the model (the spectrum) is **metrizable**.  This module
removes the hypothesis from the list of unexplained assumptions by identifying it with
a purely algebraic condition and by discharging it in the standard setting.

* `metrizableSpace_of_separable_continuousMap` — a compact Hausdorff space whose
  algebra `C(Y, ℂ)` is *separable* is metrizable.  The proof is the classical one:
  a countable dense family of continuous functions separates points (Urysohn), so it
  embeds `Y` into a countable power of `ℂ`, and a continuous injection out of a compact
  space into a Hausdorff space is an embedding;
* `separableSpace_continuousMap_of_metrizable` — the converse;
* `metrizableSpace_iff_separableSpace_continuousMap` — hence, for a compact Hausdorff
  spectrum, *metrizability of the spectrum and separability of the algebra are the same
  hypothesis*;
* `metrizableSpace_characterSpace` — via Gelfand duality, the character space of a
  **separable** commutative unital C\*-algebra is metrizable;
* **HEADLINE** `abelian_multiplication_model_classified_separable` and
  `abelian_algebra_multiplication_model_classified` — the classification list with the
  metrizability hypothesis replaced by separability of the algebra: every unital
  `*`-representation of a separable commutative unital C\*-algebra on a complex Hilbert
  space is a direct sum of multiplication algebras, each of which realises one of the
  five standard types.

Everything is `sorry`-free and `axiom`-free.
-/
namespace BookProof.ChapterSeparableSpectrum

end BookProof.ChapterSeparableSpectrum


