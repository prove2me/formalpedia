-- Prove2me | Definitions.Def_QuantumMC_MeanEst_Setting
-- name    : QuantumMC_MeanEst_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:02.332436+00:00
-- url     : https://prove2.me/theorems/7cfdb1bb-dc43-4db2-896a-331d129d5bd1
-- title:
--   §2.2–2.3, pp. 9–12 — truncations, dyadic parameters and Algorithm 3 output
-- statement:
--   For a real output $X=v(𝒜)$, the three truncations retain $X$ on $[x,y)$, $(-\infty,x)$ and $[y,\infty)$, respectively, and return zero elsewhere. Its $L^2$ size is $\|X\|_2=\sqrt{\mathbb E[X^2]}$.
--
--   Algorithm 2 sets $k=\lceil\log_2(1/\epsilon)\rceil$ and $t_0=\lceil D\sqrt{\log_2(1/\epsilon)}/\epsilon\rceil$, then returns the base estimate plus its scaled dyadic estimates. The Algorithm 1 accuracy predicate records the bound $C(\sqrt{\mathbb E[Y]}/t+1/t^2)$ for one call; the Algorithm 2 success predicate requires it for every call. Algorithm 3 centers $X/\sigma$ at the sampled value $m$, splits its negative and nonnegative parts, divides each by four, and returns $\sigma(m-4\widetilde\mu^-+4\widetilde\mu^+)$.
--
--   These definitions provide the common interface for the accuracy statements. **Formalization Note** The output law is represented by a probability measure and a real random variable; the $L^2$ definition is used under an $L^2$ hypothesis, and the dyadic band is used only at indices $\ell\ge1$.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.2–2.3, Algorithms 2 and 3, pp. 9–12

import Mathlib

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.2, p. 9: the output of 𝒜_{x,y}, with half-open interval [x,y). -/
noncomputable def truncIco (x y : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => if x ≤ X ω ∧ X ω < y then X ω else 0

/-- §2.2, p. 9: the output of 𝒜_{<x}. -/
noncomputable def truncLt (x : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => if X ω < x then X ω else 0

/-- §2.2, p. 9: the output of 𝒜_{≥y}. -/
noncomputable def truncGe (y : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => if y ≤ X ω then X ω else 0

/-- §2.2, p. 10: ‖v(𝒜)‖₂ = √𝔼[v(𝒜)²], used only when `X ∈ L²(P)`. -/
noncomputable def l2norm (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ ω, X ω ^ 2 ∂P)

/-- Algorithm 2, p. 10: k = ⌈log₂(1/ϵ)⌉. Statements assume 0 < ϵ < 1/2. -/
noncomputable def alg2K (ε : ℝ) : ℕ := ⌈Real.logb 2 (1 / ε)⌉₊

/-- Algorithm 2, p. 10: t₀ = ⌈D√(log₂(1/ϵ))/ϵ⌉. -/
noncomputable def alg2T (D ε : ℝ) : ℕ :=
  ⌈D * Real.sqrt (Real.logb 2 (1 / ε)) / ε⌉₊

/-- Algorithm 2, p. 10, step 4: μ̃₀ + ∑_{ℓ=1}^k 2^ℓ μ̃_ℓ. -/
noncomputable def alg2Output (k : ℕ) (μ : ℕ → ℝ) : ℝ :=
  μ 0 + ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * μ ℓ

/-- Algorithm 2, p. 10, step 3: v(𝒜_{2^{ℓ−1},2^ℓ})/2^ℓ; used for ℓ ≥ 1. -/
noncomputable def band (X : Ω → ℝ) (ℓ : ℕ) : Ω → ℝ :=
  fun ω => truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω / (2 : ℝ) ^ ℓ

/-- Theorem 3, pp. 8–9: the accuracy event of one Algorithm 1 call on a [0,1]-valued output. -/
noncomputable def Alg1Accurate (C : ℝ) (t : ℕ) (P : Measure Ω) (Y : Ω → ℝ) (est : ℝ) : Prop :=
  |est - ∫ ω, Y ω ∂P| ≤ C * (Real.sqrt (∫ ω, Y ω ∂P) / (t : ℝ) + 1 / (t : ℝ) ^ 2)

/-- Proof of Lemma 4, p. 10: every Algorithm 1 call in Algorithm 2 meets Theorem 3's bound. -/
noncomputable def Alg2Succeeds (C D ε : ℝ) (P : Measure Ω) (X : Ω → ℝ) (μ : ℕ → ℝ) : Prop :=
  Alg1Accurate C (alg2T D ε) P (truncIco 0 1 X) (μ 0) ∧
    ∀ ℓ ∈ Finset.Icc 1 (alg2K ε), Alg1Accurate C (alg2T D ε) P (band X ℓ) (μ ℓ)

/-- Algorithm 3, p. 12, step 3: v(ℬ) = v(𝒜)/σ − m̃. -/
noncomputable def alg3B (σ m : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => X ω / σ - m

/-- Algorithm 3, p. 12, step 4: v(−ℬ_{<0})/4. -/
noncomputable def alg3NegQuarter (σ m : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => -(truncLt 0 (alg3B σ m X) ω) / 4

/-- Algorithm 3, p. 12, step 4: v(ℬ_{≥0})/4. -/
noncomputable def alg3PosQuarter (σ m : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => truncGe 0 (alg3B σ m X) ω / 4

/-- Algorithm 3, p. 12, steps 5–6: σ(m̃ − 4μ̃⁻ + 4μ̃⁺). -/
noncomputable def alg3Output (σ m : ℝ) (k : ℕ) (μneg μpos : ℕ → ℝ) : ℝ :=
  σ * (m - 4 * alg2Output k μneg + 4 * alg2Output k μpos)

end QuantumMC.MeanEst


