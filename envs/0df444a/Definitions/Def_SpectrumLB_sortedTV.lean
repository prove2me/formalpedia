-- Prove2me | Definitions.Def_SpectrumLB_sortedTV
-- name    : SpectrumLB_sortedTV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:20.201947+00:00
-- url     : https://prove2.me/theorems/2975e984-7686-494b-a635-9636b008d71b
-- title:
--   Definition 2.1 — sorted total-variation distance $d^{\downarrow}_{\mathrm{TV}}(p,q)$
-- statement:
--   For vectors $p,q\in\mathbb R^d$ let $p^{\downarrow},q^{\downarrow}$ be their entries rearranged in nonincreasing order. The sorted total-variation distance is
--
--   $$
--   d^{\downarrow}_{\mathrm{TV}}(p,q)=\frac12\sum_{i=1}^d\big|p^{\downarrow}_i-q^{\downarrow}_i\big| .
--   $$
--
--   On probability distributions this is Definition 2.1: the total-variation distance between the sorted distributions. It measures how far apart two spectra are, irrespective of the order in which their eigenvalues are listed, and is the separation measure of Proposition 5.8.
--
--   **Formalization Note** The rearrangement is obtained from Mathlib's sorting permutation `Tuple.sort` followed by index reversal; the formula is applied to any real vectors.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 2.1, p. 11

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Sorted total-variation distance `d↓TV(p, q)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 2.1, p. 11: "d↓TV(p, q) := dTV(p↓, q↓), where p↓, q↓ are distributions formed by sorting
the entries of p, q in non-increasing order", with `dTV(p, q) = ½‖p − q‖₁`.

For `p q : ℝ^d`, `sortedTV p q = ½ Σ_i |p↓_i − q↓_i|`.

**Formalization Note.** `p↓_i = p(σ_p(rev i))` where `σ_p = Tuple.sort p` makes `p ∘ σ_p` nondecreasing;
reversing the index gives the nonincreasing rearrangement. The formula is applied to any real vectors; on
probability vectors it is the paper's distance. -/
noncomputable def sortedTV {d : ℕ} (p q : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |p (Tuple.sort p (Fin.rev i)) - q (Tuple.sort q (Fin.rev i))|

end SpectrumLB


