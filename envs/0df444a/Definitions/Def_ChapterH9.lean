-- Prove2me | Definitions.Def_ChapterH9
-- name    : ChapterH9
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:04:37.701035+00:00
-- url     : https://prove2.me/theorems/2defb5bf-cd37-42d6-bc23-eccdb8ac59d2
-- title:
--   `ChapterH8` proves that the SIRK *approximants* nest: the order-`n` reduced generator is a block of the order-`n+1` one, ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.H9`, source chapter `BookProof/ChapterH9.lean`).
--
--   `ChapterH8` proves that the SIRK *approximants* nest: the order-`n` reduced generator is a block of the order-`n+1` one, and the coarse approximant is the fine one projected back into the coarse Krylov subspace. This module proves the **spectral** side of the same statement: the sets of frequencies the reduced generators can see nest as well,
--
--   `W(Bₘ) ⊆ W(Bₙ) ⊆ W(X)` for `m ≤ n`,
--
--   where `W` is the numerical range (`ChapterH1.numericalRange`, here in its bounded operator form `numRange`) and `Bₖ = compress Vₖ X` is the order-`k` reduced generator. Refining the order can only *add* Rayleigh quotients, and never adds one that the full generator does not already have: the Krylov tower manufactures no frequencies of its own, and no order sees a frequency outside `W(X)`.
--
--   * **the compression only sees frequencies of `X`** — `numRange_compress_subset` (`W(V∗XV) ⊆ W(X)` for an isometric `V`), with the underlying isometry lemma `norm_map_of_adjoint_comp` and the quantitative form `numRange_subset_closedBall` (`W(X)` lies in the disc of radius `‖X‖`, hence so does every `W(Bₖ)`, uniformly in the order); * **the ranges nest** — `numRange_compress_mono` for an abstract nested pair `Vₙ = Vₘ ∘ J`, `numRange_compress_chain` for the two inclusions together, and `convexHull_numRange_compress_mono` for the convex hulls (the sets Crouzeix's inequality is evaluated on); * **the operator norms nest** — `norm_compress_le` (`‖Bₖ‖ ≤ ‖X‖`) and `norm_compress_mono` (`‖Bₘ‖ ≤ ‖Bₙ‖`), from `norm_adjoint_le_one_of_isometry`; * **the Ritz values nest** — `ritz_mem_numRange` (an eigenvalue of a compression is a Rayleigh quotient of `X`), `ritz_mem_numRange_compress` (an eigenvalue at the coarse order is a Rayleigh quotient at the fine order), and `ritz_re_mem_Icc_of_fine`: real bounds established at the fine order bind the coarse Ritz values; * **the Ritz spectra nest** — in finite dimensions every spectral value is an eigenvalue (`exists_unit_eigenvector`), so `spectrum_compress_subset_numRange` (`σ(B) ⊆ W(X)`), `spectrum_compress_subset_numRange_compress` (`σ(Bₘ) ⊆ W(Bₙ)`) and their hypothesis-free instance `spectrum_compress_subset_numRange_orthonormal`; * **positivity and self-adjoint bounds survive compression** — `compress_nonneg`, `compress_re_inner_mem_Icc`; * **the best-approximation error is antitone in the order** — `norm_sub_starProjection_antitone` (nested subspaces approximate better) and `krylov_bestApprox_antitone`: for `m ≤ n` the order-`n` Krylov subspace approximates any target at least as well as the order-`m` one, unconditionally (the Krylov subspaces are finite-dimensional, `krylovSpan_finiteDimensional`), with `krylov_bestApprox_tendsto_zero`: if the Krylov flag is dense (a cyclic seed) the error tends to `0` — still with no rate; * **the hypotheses are realized** — `numRange_compress_orthonormal_mono` and the headline tower `sirk_numRange_nested_orders` for any nested pair of orthonormal bases, and `sirk_numRange_krylov` for the orthonormal Krylov bases the method actually builds (`ChapterH8Bases.krylovEmbedding`).
--
--   `ChapterH1.numericalRange` and `eigenvalue_mem_numericalRange` supply the numerical range and the eigenvalue inclusion; `ChapterH6.krylov_rayleigh_transfer` is the Rayleigh–Ritz identity `⟪y, (V∗XV) y⟫ = ⟪Vy, X (Vy)⟫` that drives every proof here; `ChapterH7` supplies the self-adjoint facts; `ChapterH8` / `ChapterH8Bases` supply the nesting `Vₙ = Vₘ ∘ J` and its realization by nested orthonormal (Krylov) bases.
--
--   These are inclusions of *sets of Rayleigh quotients*. Nothing here says that the numerical ranges *converge* to `W(X)`, and nothing here is Crouzeix's inequality: the constant relating `sup_{W(B)} |f|` to `‖f(B)‖` remains a named hypothesis in `ChapterH4.sirk_error_bound_decay`, never an axiom. Note also the honest direction: since `W(Bₘ) ⊆ W(Bₙ)`, a bound of the shape `C · sup_{W(B)} |f|` i
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

import Definitions.Def_ChapterH1
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH8Bases
import Mathlib

import Mathlib

/-!
# Chapter H9 — the SIRK numerical ranges nest (plan `PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`)

`ChapterH8` proves that the SIRK *approximants* nest: the order-`n` reduced
generator is a block of the order-`n+1` one, and the coarse approximant is the
fine one projected back into the coarse Krylov subspace.  This module proves the
**spectral** side of the same statement: the sets of frequencies the reduced
generators can see nest as well,

`W(Bₘ) ⊆ W(Bₙ) ⊆ W(X)`  for `m ≤ n`,

where `W` is the numerical range (`ChapterH1.numericalRange`, here in its bounded
operator form `numRange`) and `Bₖ = compress Vₖ X` is the order-`k` reduced
generator.  Refining the order can only *add* Rayleigh quotients, and never adds
one that the full generator does not already have: the Krylov tower manufactures
no frequencies of its own, and no order sees a frequency outside `W(X)`.

## Deliverables

* **the compression only sees frequencies of `X`** — `numRange_compress_subset`
  (`W(V∗XV) ⊆ W(X)` for an isometric `V`), with the underlying isometry lemma
  `norm_map_of_adjoint_comp` and the quantitative form
  `numRange_subset_closedBall` (`W(X)` lies in the disc of radius `‖X‖`, hence so
  does every `W(Bₖ)`, uniformly in the order);
* **the ranges nest** — `numRange_compress_mono` for an abstract nested pair
  `Vₙ = Vₘ ∘ J`, `numRange_compress_chain` for the two inclusions together, and
  `convexHull_numRange_compress_mono` for the convex hulls (the sets Crouzeix's
  inequality is evaluated on);
* **the operator norms nest** — `norm_compress_le` (`‖Bₖ‖ ≤ ‖X‖`) and
  `norm_compress_mono` (`‖Bₘ‖ ≤ ‖Bₙ‖`), from `norm_adjoint_le_one_of_isometry`;
* **the Ritz values nest** — `ritz_mem_numRange` (an eigenvalue of a compression
  is a Rayleigh quotient of `X`), `ritz_mem_numRange_compress` (an eigenvalue at
  the coarse order is a Rayleigh quotient at the fine order), and
  `ritz_re_mem_Icc_of_fine`: real bounds established at the fine order bind the
  coarse Ritz values;
* **the Ritz spectra nest** — in finite dimensions every spectral value is an
  eigenvalue (`exists_unit_eigenvector`), so
  `spectrum_compress_subset_numRange` (`σ(B) ⊆ W(X)`),
  `spectrum_compress_subset_numRange_compress` (`σ(Bₘ) ⊆ W(Bₙ)`) and their
  hypothesis-free instance `spectrum_compress_subset_numRange_orthonormal`;
* **positivity and self-adjoint bounds survive compression** —
  `compress_nonneg`, `compress_re_inner_mem_Icc`;
* **the best-approximation error is antitone in the order** —
  `norm_sub_starProjection_antitone` (nested subspaces approximate better) and
  `krylov_bestApprox_antitone`: for `m ≤ n` the order-`n` Krylov subspace
  approximates any target at least as well as the order-`m` one, unconditionally
  (the Krylov subspaces are finite-dimensional, `krylovSpan_finiteDimensional`),
  with `krylov_bestApprox_tendsto_zero`: if the Krylov flag is dense (a cyclic
  seed) the error tends to `0` — still with no rate;
* **the hypotheses are realized** — `numRange_compress_orthonormal_mono` and the
  headline tower `sirk_numRange_nested_orders` for any nested pair of orthonormal
  bases, and `sirk_numRange_krylov` for the orthonormal Krylov bases the method
  actually builds (`ChapterH8Bases.krylovEmbedding`).

## Correspondence

`ChapterH1.numericalRange` and `eigenvalue_mem_numericalRange` supply the
numerical range and the eigenvalue inclusion; `ChapterH6.krylov_rayleigh_transfer`
is the Rayleigh–Ritz identity `⟪y, (V∗XV) y⟫ = ⟪Vy, X (Vy)⟫` that drives every
proof here; `ChapterH7` supplies the self-adjoint facts; `ChapterH8` /
`ChapterH8Bases` supply the nesting `Vₙ = Vₘ ∘ J` and its realization by nested
orthonormal (Krylov) bases.

## The exact boundary

These are inclusions of *sets of Rayleigh quotients*.  Nothing here says that the
numerical ranges *converge* to `W(X)`, and nothing here is Crouzeix's inequality:
the constant relating `sup_{W(B)} |f|` to `‖f(B)‖` remains a named hypothesis in
`ChapterH4.sirk_error_bound_decay`, never an axiom.  Note also the honest
direction: since `W(Bₘ) ⊆ W(Bₙ)`, a bound of the shape `C · sup_{W(B)} |f|` is
*non-decreasing* in the order — the band decay of `ChapterH6` comes from the
approximation quality, not from shrinking numerical ranges.  Convexity of the
numerical range (Toeplitz–Hausdorff) is not used and not claimed.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterH9

open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap

section NumRange

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The **numerical range** of a bounded operator: the set of Rayleigh quotients
`⟪x, X x⟫` over unit vectors.  Bounded-operator form of
`ChapterH1.numericalRange`. -/
def numRange (X : E →L[ℂ] E) : Set ℂ := numericalRange (X : E →ₗ[ℂ] E)





/-! ## Isometric embeddings -/







/-! ## The compression sees only frequencies of `X` -/







/-! ## The ranges nest -/









/-! ## The operator norms nest -/





/-! ## The Ritz values nest -/







/-! ## Positivity and self-adjoint bounds survive compression -/





/-! ## The Ritz spectra nest -/







end NumRange

/-! ## The hypotheses are realized: nested orthonormal (Krylov) bases -/

section Realization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]













end Realization

/-! ## The best-approximation error is antitone in the order -/

section BestApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]





/-- The Krylov subspaces are finite-dimensional, hence closed: the orthogonal
projection onto them exists. -/
instance krylovSpan_finiteDimensional (H : E →ₗ[ℂ] E) (v : E) (m : ℕ) :
    FiniteDimensional ℂ (krylovSpan H v m) := by
  have hfin : {x | ∃ i < m, x = (H ^ i) v}.Finite := by
    apply Set.Finite.subset (Set.finite_range (fun i : Fin m => (H ^ (i : ℕ)) v))
    rintro x ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  exact FiniteDimensional.span_of_finite ℂ hfin





end BestApprox

end BookProof.ChapterH9

end


