-- Prove2me | Definitions.Def_AlgebraicCurve_ChordalProximity
-- name    : AlgebraicCurve_ChordalProximity
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/bba10321-a1a4-5d03-b824-9ba18f556e31
-- title:
--   Chordal proximity; place-relative values of sections
-- statement:
--   Three pieces of vocabulary attached to a curve presented by a finite coordinate family. First, for a type $L$ with multiplication and subtraction, a function $\nu : L \to \mathbb{R}$ and two families $x, y : \iota \to L$, the quantity [`AlgebraicCurve.prox`](../def/AlgebraicCurve_ChordalProximity.html#L7) is defined as
--   $$\log\Big(\sup_i \nu(x_i)\Big) + \log\Big(\sup_i \nu(y_i)\Big) - \log\Big(\sup_{(i,j)} \nu(x_i y_j - x_j y_i)\Big),$$
--   the suprema being taken in $\mathbb{R}$ over all indices, respectively over all pairs $(i,j) \in \iota \times \iota$ (including the diagonal, where the entry is $\nu$ of $x_iy_i - x_iy_i$). With $\nu$ an absolute value this is the logarithmic chordal proximity of the two tuples, their sup-norms divided by the sup-norm of the exterior-square coordinates; no positivity or multiplicativity is assumed of $\nu$, and the conventions of `Real.log` and of suprema of unbounded or empty families are inherited.
--
--   The remaining two definitions fix a field $F$ that is an algebra over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a family $s : \mathrm{Fin}\,r \to F$, and produce elements of $\overline{\mathbb{Q}}$. Here `pivotIndex s v hr` denotes an index $i$ minimising the order $v.\mathrm{ord}(s_i)$ at a place $v$ when such an index exists, and $0$ otherwise, and `Place.evalAt` denotes evaluation at $v$: the residue of an element of the valuation subring of $v$, pulled back along the (injective) map $\overline{\mathbb{Q}} \to$ residue field, and $0$ for elements outside the valuation subring. For $k : \mathbb{N}$ and $u \in F$, `secVal s v k u` is the value at $v$ of $u \cdot s_{\mathrm{pivot}}^{-k}$, that is $u$ read in the trivialisation given by the $k$-th power of the pivot coordinate; for a further element $t \in F$ and $e : \mathbb{N}$, `regVal s o t k e u` is the value at a place $o$ of $u \cdot s_{\mathrm{pivot}}^{-k} \cdot t^{-e}$, the same expression with the $e$-th power of $t$ divided out. Both are $0$ when $r = 0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of chordal proximity of coordinate tuples, nor of values of elements of a function field read in a trivialisation by a coordinate family; these are the project's own, built on the project's `Place` and `Place.evalAt` together with Mathlib's `Real.log` and suprema.
--
--   **Where it is used.** These quantities provide the per-place vocabulary accompanying the height form [`AlgebraicCurve.heightForm`](../def/ModularCurve_JZeroHeightForm.html#L58), assembled from `pointHt` and `pairHt` on divisors of the function field, and its specialisation [`ModularCurve.JZero.heightForm`](../def/ModularCurve_JZeroHeightForm.html#L113) for the modular function field of level $N$ with base place the cusp at infinity; the coordinate family $s$ there is a basis of the Riemann–Roch space of `embDivisor`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_ChordalProximity.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicCurve

def prox {L : Type*} {ι : Type*} [Mul L] [Sub L] (ν : L → ℝ) (x y : ι → L) : ℝ :=
  Real.log (⨆ i, ν (x i)) + Real.log (⨆ i, ν (y i))
    - Real.log (⨆ p : ι × ι, ν (x p.1 * y p.2 - x p.2 * y p.1))

open Classical in

def secVal {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (v : Place (AlgebraicClosure ℚ) F) (k : ℕ) (u : F) : AlgebraicClosure ℚ :=
  if hr : 0 < r then v.evalAt (u * ((s (pivotIndex s v hr))⁻¹) ^ k) else 0

open Classical in

def regVal {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (o : Place (AlgebraicClosure ℚ) F) (t : F) (k e : ℕ) (u : F) : AlgebraicClosure ℚ :=
  if hr : 0 < r then o.evalAt (u * ((s (pivotIndex s o hr))⁻¹) ^ k * (t⁻¹) ^ e) else 0

end AlgebraicCurve

end


