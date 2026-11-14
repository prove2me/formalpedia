-- Prove2me | Definitions.Def_NarrowDNF_BourgainNoise
-- name    : NarrowDNF_BourgainNoise
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:59.226143+00:00
-- url     : https://prove2.me/theorems/bbdd5969-38c1-4931-a22d-041c5e6d85b7
-- title:
--   Coordinate noise, ordered noise compositions, and tensor Fourier multipliers
-- statement:
--   For a real function $f$ on a finite Boolean cube, let
--   $$M_i f(x)=(1-p)f(x^{i\leftarrow0})+p f(x^{i\leftarrow1})$$
--   be conditional averaging in coordinate $i$. For a real multiplier $\rho$, the coordinate noise operator is $N_{i,\rho}f=M_i f+\rho(f-M_i f)$. The definition allows negative multipliers as well as ordinary positive noise parameters.
--
--   For a list $[i_1,\ldots,i_m]$ and coordinate-dependent multipliers $(\rho_i)$, the recursive list operator is the composition $N_{i_1,\rho_{i_1}}\circ\cdots\circ N_{i_m,\rho_{i_m}}$, with the empty list acting as the identity. Repeated coordinates are permitted.
--
--   The spectral tensor operator is
--   $$T_\rho f(x)=\sum_{S\subseteq I}\left(\prod_{i\in S}\rho_i\right)\widehat f_p(S)\chi_{p,S}(x).$$
--   The finite formalization indexes $S$ by Boolean support masks. These formulas provide the signed-noise operators used in the Bourgain square-function argument; they do not assume a contraction estimate or a commutation theorem.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainNoise.lean#L19-L22
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainNoise.lean#L127-L131
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainNoise.lean#L176-L179

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier

namespace NarrowDNF.BourgainNoise
end NarrowDNF.BourgainNoise


/-!
# Signed noise contraction for Bourgain's square-function argument

These are actual finite fourth-moment contraction theorems, uniform in the
Bernoulli bias. They do not assume a hypercontractive inequality. The negative
noise parameter is `-1/3`; using this slightly weaker parameter avoids any
unproved sharp-constant assertion from the cited appendix.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.BourgainNoise

/-- One-coordinate signed noise, including negative noise parameters. -/
def coordinateNoise {ι : Type*} [DecidableEq ι] (p ρ : ℝ)
    (f : (ι → Bool) → ℝ) (i : ι) (x : ι → Bool) : ℝ :=
  Fourier.coordinateMean p f i x + ρ * Fourier.coordinateResidual p f i x









section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- A list of coordinate noises. No commutation or distinctness hypothesis is
needed for the contraction theorem. -/
def noiseList (p : ℝ) (ρ : ι → ℝ) : List ι → ((ι → Bool) → ℝ) → ((ι → Bool) → ℝ)
  | [], f => f
  | i :: L, f => coordinateNoise p (ρ i) (noiseList p ρ L f) i







/-- Spectral signed noise with an independently selected multiplier per coordinate. -/
def tensorNoise (p : ℝ) (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ s : ι → Bool, (∏ i, if s i then ρ i else 1) *
    Fourier.coefficient p f s * Fourier.character p s x















end Cube
end NarrowDNF.BourgainNoise


