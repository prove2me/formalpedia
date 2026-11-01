-- Prove2me | Definitions.Def_ScutaruFid_L2R
-- name    : ScutaruFid_L2R
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:05.56609+00:00
-- url     : https://prove2.me/theorems/3e356417-3877-4fe8-af91-7369dd0ab594
-- title:
--   The state space $L^2(\mathbb R)$
-- statement:
--   The state space of a single quantum oscillator (one mode) is the complex Hilbert space
--
--   $$
--   L^2(\mathbb R)=\Big\{\psi:\mathbb R\to\mathbb C\ \text{measurable}\ :\ \int_{\mathbb R}|\psi(x)|^2\,dx<\infty\Big\}
--   $$
--
--   of square-integrable functions modulo equality almost everywhere, with inner product $\langle\varphi,\psi\rangle=\int\overline{\varphi(x)}\psi(x)\,dx$. Density operators, Weyl operators and fidelities in this mission are bounded operators on $L^2(\mathbb R)$.
--
--   **Formalization Note** This is Mathlib's `MeasureTheory.Lp ℂ 2 volume` on $\mathbb R$. Its elements are almost-everywhere classes, so every pointwise formula about them is stated for almost every $x$.
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, p.1 ("the semigroup of integral operators on L2(R) whose integral kernels are Gaussians")

import Mathlib

namespace ScutaruFid

/-- **The state space `L²(ℝ)`.** Scutaru, *Fidelity for displaced squeezed thermal states and the
oscillator semigroup*, arXiv:quant-ph/9708013v1, p.1: "the semigroup of integral operators on
L2(R) whose integral kernels are Gaussians".

`L2R` is the complex Hilbert space of square-integrable functions `ℝ → ℂ` with respect to
Lebesgue measure. Density operators, Weyl operators and fidelities in this mission are bounded
operators `L2R →L[ℂ] L2R`.

**Formalization Note** Mathlib's `MeasureTheory.Lp ℂ 2 volume`: elements are a.e.-classes of
functions, so every pointwise formula about them is stated `volume`-almost everywhere. -/
abbrev L2R : Type := MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)

end ScutaruFid


