-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_Bidding
-- name    : BetterKMedian_LMPGreedy_Bidding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:13.950291+00:00
-- url     : https://prove2.me/theorems/e9ec4370-e1a5-4698-a016-8fd52ae44d9a
-- title:
--   Definition 3.1 — admissible bidding functions, and $\beta_\gamma(\alpha,d)=[\alpha-\gamma d]^+$
-- statement:
--   A bidding function is $\beta:\mathbb R_{\ge0}^2\to\mathbb R_{\ge0}$, represented as `β : ℝ → ℝ → ℝ` with every property required for nonnegative arguments. It is **admissible** (`IsAdmissibleBid β`) when
--   1. $\beta(\alpha,d)\ge0$ for $\alpha,d\ge0$;
--   2. $\beta(\alpha,d)\le[\alpha-d]^+$ for $\alpha,d\ge0$ (budget feasibility);
--   3. $\beta$ is (jointly) continuous on $\mathbb R_{\ge0}^2$;
--   4. $\beta$ is non-decreasing in $\alpha$ and non-increasing in $d$;
--   5. $\beta(\alpha,d)=\alpha\,\beta(1,d/\alpha)$ for $\alpha>0$, $d\ge0$ (scale equivariance);
--   6. $\beta(x_1,x_2)+\beta(x_2,x_3)\le\beta(x_1,x_3)$ whenever $x_1\ge x_2\ge x_3\ge0$ (superadditivity).
--
--   `betaGamma γ α d` $=\beta_\gamma(\alpha,d)=[\alpha-\gamma d]^+=\max(\alpha-\gamma d,0)$ (§3.4).
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Definition 3.1, printed p. 11 (PDF 13); β_γ, printed p. 14 (PDF 16)

import Mathlib

set_option autoImplicit false

/-!
# Admissible bidding functions and the linear bids `β_γ` (Definition 3.1, §3.4)

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, Definition 3.1, printed p. 11 (PDF 13); `β_γ`, printed p. 14 (PDF 16).

A bidding function is `β : ℝ≥0² → ℝ≥0`; here it is a function `ℝ → ℝ → ℝ` and every property is
required on the nonnegative quadrant only (Algorithm 1 and the factor-revealing program evaluate
`β` only there; its values elsewhere are irrelevant). The codomain `ℝ≥0` is Property 1.
-/

namespace BetterKMedian.LMPGreedy

/-- **Definition 3.1** (p. 11). `β` is an admissible bidding function:
1. non-negative: `β(α, d) ≥ 0` for `α, d ≥ 0`;
2. budget-feasible: `β(α, d) ≤ [α − d]⁺` for `α, d ≥ 0`;
3. continuous in both arguments (jointly, on `ℝ≥0²`);
4. monotonic: non-decreasing in `α`, non-increasing in `d`;
5. scale equivariant: `β(α, d) = α · β(1, d/α)` for `α > 0`, `d ≥ 0`;
6. superadditive: `β(x₁, x₂) + β(x₂, x₃) ≤ β(x₁, x₃)` whenever `x₁ ≥ x₂ ≥ x₃ ≥ 0`. -/
def IsAdmissibleBid (β : ℝ → ℝ → ℝ) : Prop :=
  (∀ α d : ℝ, 0 ≤ α → 0 ≤ d → 0 ≤ β α d) ∧
  (∀ α d : ℝ, 0 ≤ α → 0 ≤ d → β α d ≤ max (α - d) 0) ∧
  ContinuousOn (fun p : ℝ × ℝ => β p.1 p.2) (Set.Ici 0 ×ˢ Set.Ici 0) ∧
  ((∀ α α' d : ℝ, 0 ≤ α → α ≤ α' → 0 ≤ d → β α d ≤ β α' d) ∧
    (∀ α d d' : ℝ, 0 ≤ α → 0 ≤ d → d ≤ d' → β α d' ≤ β α d)) ∧
  (∀ α d : ℝ, 0 < α → 0 ≤ d → β α d = α * β 1 (d / α)) ∧
  (∀ x₁ x₂ x₃ : ℝ, 0 ≤ x₃ → x₃ ≤ x₂ → x₂ ≤ x₁ → β x₁ x₂ + β x₂ x₃ ≤ β x₁ x₃)

/-- The bidding function `β_γ(α, d) = [α − γ · d]⁺` (§3.4, p. 14). -/
noncomputable def betaGamma (γ : ℝ) (α d : ℝ) : ℝ :=
  max (α - γ * d) 0

end BetterKMedian.LMPGreedy


