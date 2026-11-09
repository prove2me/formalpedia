-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Params
-- name    : HardCoreLocalSampling_Local_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:42.571214+00:00
-- url     : https://prove2.me/theorems/fa97be56-c142-42f9-877c-bfdf49a0f9b6
-- title:
--   Fixed-parameter constants and finite codes of rationals
-- statement:
--   The standing assumptions are an integer $\Delta\ge3$ and a rational $0<\lambda<\lambda_c(\Delta)$; $b=\Delta-1$. The explicit constants are
--
--   $$
--   r=\frac1{32\Delta},\qquad M=8+2^{\Delta+2}(1+\lambda),\qquad
--   m=\min\Bigl\{\frac1{1+\lambda},\frac{\lambda}{(1+\lambda)^\Delta+\lambda},\frac14\Bigr\}.
--   $$
--
--   A rational $\rho\in(0,1)$ is a contraction constant if $\sum_i|\partial_iF_d(y)|\le\rho$ for all $0\le d\le b$ and $y\in[0,\infty)^d$. With $g=1-\rho$ and $t=\eta/r$, a positive rational $\eta$ satisfies (11) when
--
--   $$
--   t\le\frac12,\qquad \frac M\eta\bigl[bt(1-t)^{-b-1}-bt\bigr]\le\frac g8,\qquad (1-t)^{-\Delta}-1\le\frac m2,
--   $$
--
--   and a positive rational $\tau$ satisfies (12) when $\tau\le\eta g/(16(1+\rho))$. The aggregate tail mass (19) at arity $d$ is $(M/\eta)[(1-t)^{-d}-1-dt]$.
--
--   These constants are the common vocabulary of Lemmas 7–13. Finite codes of rationals are triples (sign, numerator, denominator), used only to state effectivity with Mathlib's `Computable`.
--
--   **Formalization Note** `(1-t)⁻¹` is meaningful under $t\le1/2$. Natural-number subtraction in $b=\Delta-1$ is exact under $\Delta\ge3$.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §6 eq. (6), printed p.7 (PDF p.8); §7 eqs. (10)–(12), printed p.8 (PDF p.9); eq. (19), printed p.9 (PDF p.10)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Potential

namespace HardCoreLocalSampling.Local

/-! The fixed-parameter constants of §6–§7: r and M (6), m (10), conditions (11)–(12),
printed pp.7–8 / PDF pp.8–9, and the finite codes of rationals used to state effectivity. -/

/-- The standing assumptions of §2: integer `Δ ≥ 3`, rational `0 < λ < λ_c(Δ)`. -/
def Standing (Delta : ℕ) (lam : ℚ) : Prop :=
  3 ≤ Delta ∧ 0 < lam ∧ lam < criticalFugacity Delta

/-- `b = Δ - 1`, the internal arity bound. Used only with `Δ ≥ 3`. -/
def bParam (Delta : ℕ) : ℕ := Delta - 1

/-- `r = 1/(32Δ)`, eq. (6). -/
def rParam (Delta : ℕ) : ℚ := 1 / (32 * (Delta : ℚ))

/-- `M = 8 + 2^{Δ+2}(1+λ)`, eq. (6). -/
def MParam (Delta : ℕ) (lam : ℚ) : ℚ := 8 + 2 ^ (Delta + 2) * (1 + lam)

/-- `m = min{1/(1+λ), λ/((1+λ)^Δ+λ), 1/4}`, eq. (10). -/
def mParam (Delta : ℕ) (lam : ℚ) : ℚ :=
  min (min (1 / (1 + lam)) (lam / ((1 + lam) ^ Delta + lam))) (1 / 4)

/-- `t = η/r`. -/
def tParam (Delta : ℕ) (eta : ℚ) : ℚ := eta / rParam Delta

/-- `ρ` satisfies the conclusion of Lemma 7, eq. (3): for all `0 ≤ d ≤ b` and `y ∈ [0,∞)^d`,
`∑ |∂_i F_d(y)| ≤ ρ`, with `ρ ∈ (0,1)`. -/
def IsContractionConstant (Delta : ℕ) (lam rho : ℚ) : Prop :=
  0 < rho ∧ rho < 1 ∧ ∀ (d : ℕ), d ≤ bParam Delta → ∀ y : Fin d → ℝ, (∀ i, 0 ≤ y i) →
    ∑ i, |partialD i (Fd (lam : ℝ)) y| ≤ (rho : ℝ)

/-- The middle expression of (11): `(M/η)[b t (1-t)^{-b-1} - b t]`. -/
def middleExpr (b : ℕ) (M eta t : ℚ) : ℚ :=
  (M / eta) * ((b : ℚ) * t * ((1 - t)⁻¹) ^ (b + 1) - (b : ℚ) * t)

/-- The three conditions (11) on `η`, with `g = 1 - ρ`. -/
def IsEta (Delta : ℕ) (lam rho eta : ℚ) : Prop :=
  0 < eta ∧ tParam Delta eta ≤ 1 / 2 ∧
    middleExpr (bParam Delta) (MParam Delta lam) eta (tParam Delta eta) ≤ (1 - rho) / 8 ∧
    ((1 - tParam Delta eta)⁻¹) ^ Delta - 1 ≤ mParam Delta lam / 2

/-- Condition (12): `0 < τ ≤ ηg/(16(1+ρ))`. -/
def IsTau (rho eta tau : ℚ) : Prop :=
  0 < tau ∧ tau ≤ eta * (1 - rho) / (16 * (1 + rho))

/-- The aggregate tail mass of eq. (19) in terms of `scale = M/η`:
`scale * [(1-t)^{-d} - 1 - d t]`. -/
def tailMass (scale t : ℚ) (d : ℕ) : ℚ :=
  scale * (((1 - t)⁻¹) ^ d - 1 - (d : ℚ) * t)

/-- A finite code `(sign, numerator, denominator)` of a rational, so that effectivity can be
stated with Mathlib's `Computable`. -/
abbrev RatCode := ℕ × ℕ × ℕ

/-- The canonical code of a rational. -/
def codeOfRat (q : ℚ) : RatCode := (if q < 0 then 1 else 0, q.num.natAbs, q.den)

/-- The rational with a given code: `(sign = 0 ? + : -) numerator / denominator`. -/
def ratOfCode (x : RatCode) : ℚ :=
  (if x.1 = 0 then 1 else -1) * ((x.2.1 : ℚ) / (x.2.2 : ℚ))

/-- Parameters `(b, r, M, ρ, η, τ)` of Theorem 4, as finite data. -/
abbrev Thm4Code := ℕ × RatCode × RatCode × RatCode × RatCode × RatCode

end HardCoreLocalSampling.Local


