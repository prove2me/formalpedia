-- Prove2me | Definitions.Def_LogSobolevMC_Entropy_Setting
-- name    : LogSobolevMC_Entropy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:45.037462+00:00
-- url     : https://prove2.me/theorems/655bdfbb-2a77-4fc9-9a11-e468234a6890
-- title:
--   §2.1, p. 701; Theorem 3.6, p. 722 — the relative entropy Ent_π(μ), the entropy Ent_π(f) of a density, and the semigroup acting on measures μH_t
-- statement:
--   Let $\mathcal X$ be a finite set, $K$ a Markov kernel on $\mathcal X$ and $\pi$ a probability on $\mathcal X$, invariant for $K$ and charging every point. Let $H_t=e^{-t(I-K)}=e^{-t}\sum_{n\ge0}\frac{t^n}{n!}K^n$ be the associated continuous-time semigroup. This file adds three objects to the shared setting of the series (norms, $\mathcal E$, $\mathcal L$, $\lambda$, $\alpha$).
--
--   1. The **relative entropy** of a probability measure $\mu$ on $\mathcal X$ with respect to $\pi$:
--   $$\mathrm{Ent}_\pi(\mu)=\sum_x\mu(x)\log\frac{\mu(x)}{\pi(x)}.$$
--   2. The **entropy of a density**, for a nonnegative function $f$ with $E_\pi f=1$:
--   $$\mathrm{Ent}_\pi(f)=\sum_x f(x)\log f(x)\,\pi(x).$$
--   When $\mu=f\pi$ the two agree, which is why the paper writes $\mathrm{Ent}_\pi(f)=\mathrm{Ent}_\pi(\mu)$.
--   3. The **semigroup acting on measures**, $\mu H_t(y)=\sum_x H_t(x,y)\mu(x)$.
--
--   These are the objects in which the entropy decay $\mathrm{Ent}_\pi(\mu H_t)\le e^{-2\alpha t}\mathrm{Ent}_\pi(\mu)$ of Theorem 3.6 and its supporting lemmas are stated.
--
--   **Formalization Note** The definitions are total functions of real vectors: that $\mu$ is a probability, that $f\ge0$ with $E_\pi f=1$, and that $\pi(x)>0$ are hypotheses of the theorems that use them. `Real.log 0 = 0` gives the convention $0\log 0=0$, so points with $\mu(x)=0$ or $f(x)=0$ contribute nothing. $H_t$ is the published `MarkovMixing.heatKernel K t`, and $\mu H_t$ is the row vector $\mu$ times that matrix. The module imports the shared setting `LogSobolevMC.ChiSquare.Setting`, which the theorems built on it also use.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 701, §2.1 (Ent_π(f), Ent_π(μ)); p. 710, §2.4; p. 722, Theorem 3.6 (μH_t); https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.Entropy

open scoped BigOperators

/-- The relative entropy `Ent_π(μ) = Σ_x μ(x) log(μ(x)/π(x))` of a probability measure `μ`
with respect to `π` (§2.1, p. 701; §2.4, p. 710). Terms with `μ(x) = 0` vanish. -/
noncomputable def relEnt {V : Type*} [Fintype V] (π μ : V → ℝ) : ℝ :=
  ∑ x, μ x * Real.log (μ x / π x)

/-- The entropy `Ent_π(f) = Σ_x f(x) log f(x) π(x)` of a density `f` (§2.1, p. 701). -/
noncomputable def entF {V : Type*} [Fintype V] (π f : V → ℝ) : ℝ :=
  ∑ x, f x * Real.log (f x) * π x

/-- The semigroup acting on measures, `μH_t(y) = Σ_x H_t(x, y) μ(x)` (Theorem 3.6, p. 722). -/
noncomputable def measHeat {V : Type*} [Fintype V] [DecidableEq V] (K : Matrix V V ℝ) (t : ℝ)
    (μ : V → ℝ) : V → ℝ :=
  Matrix.vecMul μ (MarkovMixing.heatKernel K t)

end LogSobolevMC.Entropy


