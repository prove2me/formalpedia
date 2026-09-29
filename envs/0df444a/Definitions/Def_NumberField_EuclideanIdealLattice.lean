-- Prove2me | Definitions.Def_NumberField_EuclideanIdealLattice
-- name    : NumberField_EuclideanIdealLattice
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/0d07bf2e-01b3-5b75-99f9-925b509dfc2f
-- title:
--   Ideal lattices in the Euclidean mixed space; Hecke scaling factor
-- statement:
--   Throughout, $K$ is a number field. Two total definitions are made, with no side conditions on their arguments.
--
--   For a unit $I$ of the monoid of fractional ideals of $\mathcal{O}_K$ in $K$, [`Deep.Analytic.euclideanIdealLattice K I`](../def/NumberField_EuclideanIdealLattice.html#L18) is the $\mathbb{Z}$-submodule of the Euclidean model `euclidean.mixedSpace K` of the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ obtained by transporting Mathlib's ideal lattice `NumberField.mixedEmbedding.idealLattice K I` — the image of $I$ under the canonical (mixed) embedding of $K$ — along the linear map underlying `euclidean.toMixed K`, using `ZLattice.comap` over $\mathbb{R}$. Thus a point of the Euclidean model lies in `euclideanIdealLattice K I` exactly when its image in the mixed space belongs to the image of $I$; the `ZLattice.comap` construction records this preimage as a $\mathbb{Z}$-submodule, so that the lattice structure of the ideal is available in the space carrying the Euclidean inner product rather than in the mixed space itself.
--
--   [`M4aP2.heckeScale K I`](../def/NumberField_EuclideanIdealLattice.html#L28) is the real number
--   $$\bigl(|d_K|\cdot \mathrm{N}(I)^2\bigr)^{-1/n},$$
--   formed with the real power function, where $d_K$ is the discriminant of $K$ cast to $\mathbb{R}$, $\mathrm{N}(I)$ is the absolute norm `FractionalIdeal.absNorm` of the underlying fractional ideal of $I$ cast to $\mathbb{R}$, and $n=[K:\mathbb{Q}]$ is `Module.finrank ℚ K` cast to $\mathbb{R}$ (so the exponent is $-1/n$ as a real exponent). This is the scaling factor by which Gaussians are dilated in the theta series attached to $I$, normalised so that the factors attached to $I$ and to the inverse of $\mathfrak{d}_K I$ are mutually inverse.
--
--   **Relation to Mathlib.** The lattice is built from Mathlib's `NumberField.mixedEmbedding.idealLattice`, the Euclidean model `euclidean.mixedSpace` together with `euclidean.toMixed`, and `ZLattice.comap`; it is the transport of a Mathlib object to the Euclidean model rather than a new notion. The scaling factor `heckeScale` is the project's own definition.
--
--   **Where it is used.** These definitions set up the lattice-theoretic and normalisation data for the theta series attached to a fractional ideal, used in the analytic part of the development where such series and their functional equations are treated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_EuclideanIdealLattice.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors

noncomputable section

namespace Deep.Analytic

variable (K : Type*) [Field K] [NumberField K]

open Classical in

def euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (euclidean.toMixed K).toLinearMap

end Deep.Analytic

namespace M4aP2

variable (K : Type*) [Field K] [NumberField K]

def heckeScale (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (|(discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
    ^ (-(1 : ℝ) / (Module.finrank ℚ K : ℝ))

end M4aP2

end


