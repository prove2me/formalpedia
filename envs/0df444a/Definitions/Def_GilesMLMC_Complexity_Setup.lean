-- Prove2me | Definitions.Def_GilesMLMC_Complexity_Setup
-- name    : GilesMLMC_Complexity_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:30.229992+00:00
-- url     : https://prove2.me/theorems/69b340b1-9987-4d11-8869-4a3a648176c0
-- title:
--   Timesteps $h_l=M^{-l}T$, the multilevel estimator $\widehat Y=\sum_{l=0}^L\widehat Y_l$, its mean-square error and its total cost (§2–§3)
-- statement:
--   This file fixes the objects of the multilevel Monte Carlo method of Giles.
--
--   Let $M$ be an integer (the **refinement factor**, $M\ge2$ in every statement) and $T>0$ a time horizon. The **timestep of level** $l=0,1,2,\dots$ is
--   $$h_l = M^{-l}\,T .$$
--   For the choice of the finest level, which is an integer ceiling, the same formula is also used at an integer level $L\in\mathbb Z$, $h_L=T\,M^{-L}$; on natural numbers the two agree.
--
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space. For each level $l$ and each sample size $n\ge1$, $\widehat Y_l^{(n)}:\Omega\to\mathbb R$ is a level-$l$ estimator based on $n$ Monte Carlo samples, and $C_l^{(n)}$ is its computational complexity. Given sample sizes $N=(N_0,N_1,\dots)$ and a finest level $L$, the **multilevel estimator** and its **computational complexity** are
--   $$\widehat Y=\sum_{l=0}^{L}\widehat Y_l^{(N_l)},\qquad C=\sum_{l=0}^{L} C_l^{(N_l)} .$$
--   For a random variable $X$ estimating $E[P]$, the **mean-square error** is
--   $$\mathrm{MSE}\equiv E\big[(X-E[P])^2\big].$$
--
--   These are the objects of Theorem 3.1 and of every step of its proof.
--
--   **Formalization Note** Expectations are Bochner integrals against $\mu$; the estimators are indexed by both the level and the sample size, because the theorem chooses the sample sizes. The cost $C_l^{(n)}$ is an abstract real number, constrained only by hypothesis (iv) of the theorems.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §1, p. 607 (h_l = M^{-l}T, integer M ⩾ 2); §2, p. 608 (Ŷ = Σ Ŷ_l); Theorem 3.1, p. 609 (MSE ≡ E[(Ŷ − E[P])²], C)

import Mathlib

namespace GilesMLMC.Complexity

/-- The timestep of level `l`, `h_l = M^{-l} T` (Giles 2008, §1, p. 607 and §2, p. 608;
PDF 1–2). The refinement factor `M` is an integer `≥ 2` and `T > 0` is the time horizon; both
are hypotheses of the theorems that use `h`, not of this definition. -/
noncomputable def h (M : ℕ) (T : ℝ) (l : ℕ) : ℝ := T / (M : ℝ) ^ l

/-- The timestep `h_L = M^{-L} T` at an *integer* level `L`, used for the choice of `L` in (6)
(Giles 2008, §3, proof of Theorem 3.1, p. 609, PDF 3), where `L` is defined as an integer
ceiling. For a natural number `l`, `hz M T l = h M T l` (when `M ≠ 0`). -/
noncomputable def hz (M : ℕ) (T : ℝ) (L : ℤ) : ℝ := T * (M : ℝ) ^ (-L)

/-- The multilevel estimator `Ŷ = Σ_{l=0}^{L} Ŷ_l` (Giles 2008, §2, p. 608 and Theorem 3.1,
p. 609; PDF 2–3). Here `Y l n` is the level-`l` estimator `Ŷ_l` built from `n` Monte Carlo
samples, and `N l` is the number of samples used on level `l`. -/
noncomputable def estimator {Ω : Type*} (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ → ℕ) (L : ℕ) : Ω → ℝ :=
  fun ω => ∑ l ∈ Finset.range (L + 1), Y l (N l) ω

/-- The mean-square error `MSE ≡ E[(X − E[P])²]` of an estimator `X` of `E[P]`
(Giles 2008, Theorem 3.1, p. 609, PDF 3). Expectations are Bochner integrals against `μ`. -/
noncomputable def mse {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X P : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - ∫ ω', P ω' ∂μ) ^ 2 ∂μ

/-- The computational complexity `C = Σ_{l=0}^{L} C_l` of the multilevel estimator, where
`cost l n` is the computational complexity `C_l` of the level-`l` estimator `Ŷ_l` built from `n`
samples (Giles 2008, Theorem 3.1 (iv) and the proof, pp. 609–610, PDF 3–4). -/
noncomputable def totalCost (cost : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (L : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (L + 1), cost l (N l)

end GilesMLMC.Complexity


