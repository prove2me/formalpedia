-- Prove2me | Definitions.Def_MasulloGRH_SlowGrowthNearPoles
-- name    : MasulloGRH_SlowGrowthNearPoles
-- status  : Definition
-- author  : @koffie
-- created : 2026-11-21T00:00:26.754592+00:00
-- url     : https://prove2.me/theorems/af44e10e-af0a-4d72-b8c4-1fbade7cb72f
-- title:
--   Definition B.3.1.1 — meromorphic functions with slow growth near their poles
-- statement:
--   Let $a<b$ and let $\mathbb C_{(a,b)}=\{s: a<\operatorname{Re}s<b\}$. A meromorphic function $f$ on $\mathbb C_{(a,b)}$ has **slow growth near its poles**, witnessed by real numbers $(T_k)_{k\in\mathbb Z}$, if:
--
--   1. there is $\alpha>0$ with $|T_{\pm(k+1)}|\ge|T_{\pm k}|$ for $k\ge0$, $|T_k|\to\infty$ as $|k|\to\infty$, and $T_k=O(|k|^{\alpha})$; moreover $f$ is holomorphic on a horizontal strip of $\mathbb C_{(a,b)}$ containing each line $\mathbb R+iT_k$;
--   2. there are $\beta>0$ and $A>0$, independent of $\sigma$, with
--   $$|f(\sigma+iT_k)|\le A\,|k|^{\beta}\qquad(k\ne0,\ a<\sigma<b);$$
--   3. there are $0<\varepsilon_1<\varepsilon_2<(b-a)/2$ such that $t\mapsto f(a+\varepsilon_1+it)$ and $t\mapsto f(b-\varepsilon_2+it)$ are continuous, grow at most polynomially, and $f$ has no pole on these two vertical lines.
--
--   This is Masullo's hypothesis for the Asymptotic Residue Theorem B.3.2.1, which is used throughout the draft, from Chapter 2 to Chapter 10.
--
--   **Formalization Note** Meromorphy is Mathlib's `MeromorphicOn` on the open strip. In condition 2 the index $k=0$ is excluded: read literally, $A|0|^{\beta}=0$ would force $f$ to vanish on the line $\mathbb R+iT_0$, which is clearly not intended. "No pole on the lines" is encoded as analyticity at every point of the two lines.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix B, Definition B.3.1.1, p. 604. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib
import Definitions.Def_MasulloGRH_MellinRpos

/-!
# Meromorphic functions with slow growth near their poles

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix B, §B.3.1,
Definition B.3.1.1 (p. 604).
-/

namespace MasulloGRH

open Complex Filter

/-- Definition B.3.1.1: `f` is meromorphic on the open vertical strip `ℂ_{(a,b)}` and has *slow
growth near its poles*, witnessed by the sequence `(T k)_{k ∈ ℤ}`:

1. there is `α > 0` such that `|T_{±(k+1)}| ≥ |T_{±k}|`, `|T_k| → ∞` as `|k| → ∞`,
   `T_k = O(|k|^α)`, and `f` is holomorphic on a horizontal strip of `ℂ_{(a,b)}` containing the
   line `ℝ + i T_k`;
2. there are `β > 0` and `A > 0` (independent of `σ`) with `|f(σ + i T_k)| ≤ A |k|^β` for all
   integers `k` and all `a < σ < b`;
3. there are `0 < ε₁ < ε₂ < (b - a)/2` such that `t ↦ f(a + ε₁ + it)` and `t ↦ f(b - ε₂ + it)`
   are continuous and grow at most polynomially, and `f` has no pole on these two lines. -/
def HasSlowGrowthNearPoles (f : ℂ → ℂ) (a b : ℝ) (T : ℤ → ℝ) : Prop :=
  MeromorphicOn f (openStrip a b) ∧
  (∃ α : ℝ, 0 < α ∧
    (∀ k : ℕ, |T (k : ℤ)| ≤ |T ((k : ℤ) + 1)| ∧ |T (-(k : ℤ))| ≤ |T (-((k : ℤ) + 1))|) ∧
    Tendsto (fun k : ℤ => |T k|) cofinite atTop ∧
    (fun k : ℤ => T k) =O[cofinite] (fun k : ℤ => |(k : ℝ)| ^ α) ∧
    ∀ k : ℤ, ∃ δ : ℝ, 0 < δ ∧
      DifferentiableOn ℂ f {s : ℂ | a < s.re ∧ s.re < b ∧ |s.im - T k| < δ}) ∧
  (∃ β A : ℝ, 0 < β ∧ 0 < A ∧ ∀ k : ℤ, k ≠ 0 → ∀ σ : ℝ, a < σ → σ < b →
      ‖f ((σ : ℂ) + (T k : ℂ) * I)‖ ≤ A * |(k : ℝ)| ^ β) ∧
  (∃ ε₁ ε₂ : ℝ, 0 < ε₁ ∧ ε₁ < ε₂ ∧ ε₂ < (b - a) / 2 ∧
    Continuous (fun t : ℝ => f (((a + ε₁ : ℝ) : ℂ) + (t : ℂ) * I)) ∧
    Continuous (fun t : ℝ => f (((b - ε₂ : ℝ) : ℂ) + (t : ℂ) * I)) ∧
    (∃ C M : ℝ, ∀ t : ℝ,
      ‖f (((a + ε₁ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ M ∧
      ‖f (((b - ε₂ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ M) ∧
    ∀ t : ℝ, AnalyticAt ℂ f (((a + ε₁ : ℝ) : ℂ) + (t : ℂ) * I) ∧
      AnalyticAt ℂ f (((b - ε₂ : ℝ) : ℂ) + (t : ℂ) * I))

end MasulloGRH


