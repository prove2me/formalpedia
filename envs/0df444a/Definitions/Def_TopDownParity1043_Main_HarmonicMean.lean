-- Prove2me | Definitions.Def_TopDownParity1043_Main_HarmonicMean
-- name    : TopDownParity1043_Main_HarmonicMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:19:23.042207+00:00
-- url     : https://prove2.me/theorems/9cd13387-9a15-4283-8f97-19382850e592
-- title:
--   Definition 5 — conditional averages and harmonic mean coefficients
-- statement:
--   For $f:\{0,1\}^V\to\mathbb R_{\ge0}$, define the uniform mean $\mathbb E f$ and the conditional average $f_R(z)$ over all completions of a pattern $z\in\{0,1\}^R$. The harmonic coefficient is
--   $$H_f(R)=\left(2^{-|R|}\sum_{z\in\{0,1\}^R}f_R(z)^{-1}\right)^{-1}.$$
--
--   Inverses use $0^{-1}=+\infty$ and $(+\infty)^{-1}=0$. Thus a zero conditional average makes $H_f(R)=0$. The coefficient is retained as an extended nonnegative real, although it is finite for every finite-valued $f$.
--
--   The general weighted harmonic mean for support weights $p_z$ and values $g_z$ is $(\sum_zp_zg_z^{-1})^{-1}$, and its quadratic objective is $\sum_zp_zg_zw_z^2$. Lemma 11 imposes positive support weights summing to one. These objects connect its general variational formula to the cube coefficients without assigning real division's default zero to an inverse of zero.
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Definition 5 and Lemma 11, p. 16

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Cube
import Definitions.Def_TopDownParity1043_Main_Subcubes

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Weighted harmonic mean on a finite support. For positive weights of total mass one,
a zero g-value makes this zero, with 0 inverse = infinity and infinity inverse = 0. -/
noncomputable def weightedHarmonic {A : Type} [Fintype A]
    (p g : A → ℝ≥0) : ℝ≥0∞ :=
  (∑ z, (p z : ℝ≥0∞) * (g z : ℝ≥0∞)⁻¹)⁻¹

/-- The nonnegative quadratic objective in Lemma 11. -/
noncomputable def weightedEnergy {A : Type} [Fintype A]
    (p g w : A → ℝ≥0) : ℝ≥0 :=
  ∑ z, p z * g z * w z ^ 2

/-- Uniform finite mean of a nonnegative cube function; the cube is always nonempty. -/
noncomputable def cubeMean {V : Type} [Fintype V] [DecidableEq V] (f : (V → Bool) → ℝ≥0) : ℝ≥0 :=
  (∑ x, f x) / Fintype.card (V → Bool)

/-- Definition 5, p.16: uniform average over all completions of a pattern z on R.
Every z has exactly 2^(|V|-|R|) completions. -/
noncomputable def conditionalMean {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (R : Finset V) (z : R → Bool) : ℝ≥0 := by
  classical
  exact (∑ x : V → Bool, if project R x = z then f x else 0) /
    (2 : ℝ≥0) ^ (Fintype.card V - R.card)

/-- Definition 5: H_f(R), retained in ENNReal. It is finite for every finite-valued f.
All inverses are taken in ENNReal, in particular at zero. -/
noncomputable def harmonicMean {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (R : Finset V) : ℝ≥0∞ :=
  (((2 : ℝ≥0∞) ^ R.card)⁻¹ *
    ∑ z : R → Bool, (conditionalMean f R z : ℝ≥0∞)⁻¹)⁻¹

end TopDownParity1043.Main


