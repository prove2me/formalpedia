-- Prove2me | Definitions.Def_FieldTheory_RatAlgClosureGalois
-- name    : FieldTheory_RatAlgClosureGalois
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/16da4bf0-16d1-56c6-b699-270c473bdfc2
-- title:
--   Galois instance for Q​ with the rational algebra structure
-- statement:
--   This module contains a single instance declaration and no new mathematical notion. The field $\overline{\mathbb{Q}}$, realised as `AlgebraicClosure ℚ`, admits two $\mathbb{Q}$-algebra structures that are definitionally equal but syntactically distinct: `AlgebraicClosure.instAlgebra ℚ`, under which Mathlib records that the extension is Galois, and `DivisionRing.toRatAlgebra`, the canonical $\mathbb{Q}$-algebra structure carried by every division ring of characteristic zero. The declaration [`AlgebraicClosure.Rat.isGalois`](../def/FieldTheory_RatAlgClosureGalois.html#L5) asserts `IsGalois ℚ (AlgebraicClosure ℚ)` with the algebra argument pinned explicitly, using `@`, to `DivisionRing.toRatAlgebra`; that is, the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, viewed through that second structure, is normal and separable in Mathlib's sense. Mathematically this is just the statement that an algebraic closure of a field of characteristic zero is a Galois extension of it; the content of the module is entirely that the statement is available with the algebra slot filled by the canonical $\mathbb{Q}$-algebra structure that Mathlib attaches to every characteristic-zero division ring (`Mathlib.Algebra.Algebra.Rat`). The proof is Mathlib's `IsAlgClosure.isGalois` applied with the other, `AlgebraicClosure.instAlgebra ℚ`, structure, the two being interchangeable by definitional unfolding. Once this instance is in scope, the derived facts keyed on `IsGalois` — normality, separability, the fixed-field correspondence, and (with the profinite material) the compactness, Hausdorffness and total disconnectedness of the Krull-topologised automorphism group `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ` — are usable with either of the two $\mathbb{Q}$-algebra structures.
--
--   **Relation to Mathlib.** Nothing here is new mathematics relative to Mathlib: the instance is Mathlib's `IsAlgClosure.isGalois` for $\mathbb{Q}$, restated with the $\mathbb{Q}$-algebra structure on `AlgebraicClosure ℚ` fixed to `DivisionRing.toRatAlgebra` rather than to `AlgebraicClosure.instAlgebra ℚ`.
--
--   **Where it is used.** It sits at the bottom of the Galois-theoretic vocabulary of the development: the modules that speak of $G_{\mathbb{Q}} = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, its profinite topology and its representations rely on this instance to obtain the Galois package on $\overline{\mathbb{Q}}$, and it is imported rather than re-declared by them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FieldTheory_RatAlgClosureGalois.lean

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

instance AlgebraicClosure.Rat.isGalois :
    @IsGalois ℚ _ (AlgebraicClosure ℚ) _ DivisionRing.toRatAlgebra :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _


