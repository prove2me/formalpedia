-- Prove2me | Definitions.Def_PosIndexNash_PPADS_PositivePayoffShift
-- name    : PosIndexNash_PPADS_PositivePayoffShift
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:05.789157+00:00
-- url     : https://prove2.me/theorems/000bd838-0b69-4cd5-a5ad-703279f9e055
-- title:
--   The polynomial-size common payoff shift making a rational game strictly positive (§3.1)
-- statement:
--   For a rational bimatrix game $G=(A,B)$, define
--   $$c(G)=1+\sum_{i,j}|A_{ij}|+\sum_{i,j}|B_{ij}|,\qquad
--   \widehat G=(A+c(G)\mathbf1\mathbf1^\top,B+c(G)\mathbf1\mathbf1^\top).$$
--   The definition gives the explicit rational constant used for the normalization in §3.1. Its use of absolute-value sums, rather than an unspecified sufficiently large constant, also exposes a polynomial-time algorithm on the standard binary game encoding. Since $c(G)>|A_{ij}|,|B_{ij}|$, every entry of $\widehat G$ is strictly positive.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, proof of Theorem 3.2, p.14, §3.1: "Shift each payoff matrix by a rational constant so that A > 0 and B > 0 entrywise, using e.g. c := 1 + ∑_{i,j} |A_{ij}| + ∑_{i,j} |B_{ij}| (polynomially computable, output size polynomial)."

import Mathlib
import Definitions.Def_QuasiStrictNE_RatGame

namespace PosIndexNash.PPADS

/-- One plus the sum of the absolute values of all entries of both payoff matrices of `G`.
This explicit rational bound is polynomially computable from the binary encoding of `G`. -/
def payoffShiftAmount (G : QuasiStrictNE.RatGame) : ℚ :=
  1 + (∑ i, ∑ j, |G.A i j|) + (∑ i, ∑ j, |G.B i j|)

/-- Shift both payoff matrices of a rational bimatrix game by `payoffShiftAmount G`.
The numbers `m,n` of pure strategies are unchanged. -/
def positivePayoffShift (G : QuasiStrictNE.RatGame) : QuasiStrictNE.RatGame where
  m := G.m
  n := G.n
  A := G.A + Matrix.of fun _ _ => payoffShiftAmount G
  B := G.B + Matrix.of fun _ _ => payoffShiftAmount G

end PosIndexNash.PPADS


