-- Prove2me | Definitions.Def_GeneralCK_entropy_flow
-- name    : GeneralCK_entropy_flow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:21:14.467058+00:00
-- url     : https://prove2.me/theorems/c24c7a74-a7d9-4db1-9357-474ebea3989c
-- title:
--   The regularized Boolean entropy flow
-- statement:
--   For a Boolean function $f$ and parameter $\varepsilon$, regularize its indicator to $v_\varepsilon(x)=\varepsilon+(1-2\varepsilon)\mathbf1_{f(x)=\mathrm{true}}$. The flow is $T_{p(t)}v_\varepsilon$ with $p(t)=(1-e^{-2t})/2$. Let $m_0=\mathbb Ev_\varepsilon$ and $\gamma(t)=\mathbb EH(T_{p(t)}v_\varepsilon)$. The entropy comparison quantity is $$\delta(t)=\gamma(t)+1-H(m_0).$$ These definitions connect the static cube energy inequality to a scalar differential inequality.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyFlow.lean#L11-L24

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_cube_analysis
import Definitions.Def_GeneralCK_noise_evolution
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Flow
open scoped BigOperators
open CubeAnalysis

noncomputable def regularized {n : ℕ} (f : Cube n → Bool) (eps : ℝ) (x : Cube n) : ℝ :=
  eps + (1 - 2 * eps) * (if f x = true then 1 else 0)

noncomputable def flow {n : ℕ} (f : Cube n → Bool) (eps t : ℝ) : Cube n → ℝ :=
  Noise.applyNoise (Noise.crossover t) (regularized f eps)

noncomputable def initialMean {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : ℝ :=
  mean (regularized f eps)

noncomputable def gamma {n : ℕ} (f : Cube n → Bool) (eps t : ℝ) : ℝ :=
  mean (H ∘ flow f eps t)

noncomputable def delta {n : ℕ} (f : Cube n → Bool) (eps t : ℝ) : ℝ :=
  gamma f eps t + 1 - H (initialMean f eps)





































end GeneralCK.Flow


