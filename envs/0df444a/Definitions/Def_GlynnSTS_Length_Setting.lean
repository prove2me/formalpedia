-- Prove2me | Definitions.Def_GlynnSTS_Length_Setting
-- name    : GlynnSTS_Length_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:49.209908+00:00
-- url     : https://prove2.me/theorems/cf3da071-fb57-44fa-b9f6-58b7db507d14
-- title:
--   §§2 and 4 — Brownian paths, STS class, functional CLT, and interval width
-- statement:
--   Let $C[0,1]$ be the continuous real paths on $[0,1]$ with the uniform metric, and let $B$ be standard Brownian motion viewed as a random path. Define $k(t)=t$ and the bridge map $(\Gamma x)(t)=x(t)-t x(1)$. The discontinuity set $D(g)$ contains the paths at which a functional $g:C[0,1]\to\mathbb R$ is not continuous.
--
--   The class $\mathcal M$ consists of measurable functionals $g$ satisfying $g(ax)=a g(x)$ for $a>0$, $g(x-\beta k)=g(x)$ for every real $\beta$, $g(B)>0$ almost surely, and $P\{B\in D(g)\}=0$. The class $\mathcal N$ comprises measurable, positively homogeneous functionals $b$ for which $b(\Gamma B)>0$ almost surely and $P\{B\in D(b\circ\Gamma)\}=0$.
--
--   For a measurable simulation output process $Y$, $\overline Y_n(t)=n^{-1}\int_0^{nt}Y(s)\,ds$ and $X_n(t)=\sqrt n(\overline Y_n(t)-\mu t)$. Assumption (2.1) asserts $X_n\Rightarrow\sigma B$ in $C[0,1]$ for finite $\mu$ and $\sigma>0$. The standardized endpoint distribution and the interval width are
--   $$
--   H(x)=P\{B(1)/g(B)\le x\},\qquad
--   L_n=g(\overline Y_n)(\beta-\alpha).
--   $$
--
--   These definitions fix the common objects used by the lower-bound results.
--
--   **Formalization Note** The process has jointly measurable sample values and integrable paths on finite intervals so the displayed primitive is defined. Each $\overline Y_n$ is pinned pointwise by that equation. The path space carries its Borel sigma algebra. The source treats measurability of $b$ as a standing convention; it is made explicit here. Natural numbers index $n$, with zero harmless by Lean's total division.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), pp. 2–5 and 9, (2.1), (2.3), (2.6), (2.9), (2.10)

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

instance : MeasurableSpace C(unitInterval, ℝ) := borel _
instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

/-- The bridge map `(Γx)(t) = x(t) - t x(1)`, p. 4. -/
def Gamma (x : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  x - x 1 • GlynnSTS.Limit.kfun

/-- The class `𝒩` of (2.6). Measurability is the standing convention for functionals. -/
def ClassN {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → C(unitInterval, ℝ)) (b : C(unitInterval, ℝ) → ℝ) : Prop :=
  Measurable b ∧
  (∀ a : ℝ, 0 < a → ∀ x, b (a • x) = a * b x) ∧
  (∀ᵐ ω ∂P, 0 < b (Gamma (B ω))) ∧
  P {ω | B ω ∈ GlynnSTS.Limit.D (b ∘ Gamma)} = 0

/-- Assumption (2.1), including measurability and the integrability needed for `Ȳₙ`. -/
structure Assumption21 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ))
    (μ σ : ℝ) (B : Ω → C(unitInterval, ℝ)) : Prop where
  measurable : Measurable (fun p : ℝ × Ω => Y p.1 p.2)
  integrable : ∀ ω (T : ℝ), IntervalIntegrable (fun s => Y s ω) volume 0 T
  ybar_eq : ∀ (n : ℕ) ω (t : unitInterval),
    Ybar n ω t = (∫ s in (0 : ℝ)..((n : ℝ) * t), Y s ω) / n
  sigma_pos : 0 < σ
  fclt : TendstoInDistribution (GlynnSTS.Limit.Xn Ybar μ) atTop (fun ω => σ • B ω) (fun _ => P) P

/-- `H(x) = P{B(1)/g(B) ≤ x}` on p. 4. -/
noncomputable def H {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → C(unitInterval, ℝ)) (g : C(unitInterval, ℝ) → ℝ) (x : ℝ) : ℝ :=
  (P {ω | B ω 1 / g (B ω) ≤ x}).toReal

/-- Width `Lₙ = g(Ȳₙ)(β - α)` of the interval (2.10). -/
def Ln {Ω : Type*} (g : C(unitInterval, ℝ) → ℝ)
    (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (α β : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  g (Ybar n ω) * (β - α)

end GlynnSTS.Length


