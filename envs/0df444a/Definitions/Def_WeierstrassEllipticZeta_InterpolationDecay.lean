-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterpolationDecay
-- name    : WeierstrassEllipticZeta_InterpolationDecay
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T15:27:23.040188+00:00
-- url     : https://prove2.me/theorems/fba0d46c-d789-4db5-a18d-a0e4e72a4b8b
-- title:
--   Exponential interpolation bounds on translated auxiliary grids
-- statement:
--   For fixed complex $\omega,u_1,u_2$, put
--
--   $$m=\lfloor N/\log N\rfloor,\quad s=\lfloor N^{3/16}\rfloor,\quad
--   q=\lfloor N^{5/8}\log N/64\rfloor,\quad R=N^{49/72},$$
--
--   $$r=4q(|u_1|+|u_2|+|\omega|+1),\qquad
--   \Gamma_N=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--   0\le a_1,a_2<s,\ 0\le a_3<q,\ a_i\in\mathbb Z\}.$$
--
--   The decay data assert the following proposition for every fixed $B\ge0$ and $K>0$, for all sufficiently large integers $N$, uniformly in all subsequent choices.
--
--   Let $|v|\le r$ and write $\Delta=\Gamma_N-v$. Supply functions $f,G,\psi$ such that $G$ is entire, while $f,\psi$ are analytic near every point of $\Delta$ and satisfy $G=\psi f$ locally there. Assume
--
--   $$f^{(j)}(x)=0\quad(x\in\Delta,\ 0\le j<m+1),\qquad
--   \max_{|z|=R}|G(z)|\le e^{BN^2}.$$
--
--   For every complex $w$ and nonnegative integer $n$ with
--
--   $$|w|+1\le 2r,\qquad n\le Km,$$
--
--   the regularized derivative satisfies
--
--   $$|G^{(n)}(w)|\le \exp\!\left(-\frac{N^2\log N}{73728}\right).$$
--
--   If $f,\psi$ are also analytic near $w$, with $G=\psi f$ there, and
--
--   $$f^{(j)}(w)=0\quad(0\le j<n),\qquad \psi(w)\ne0,\qquad
--   |\psi(w)|^{-1}\le e^{BN^2},$$
--
--   then
--
--   $$|f^{(n)}(w)|\le \exp\!\left(-\frac{N^2\log N}{73728}\right).$$
--
--   The double inner radius accommodates arbitrary translates with $|v|\le r$. The constant $1/73728$ is a coarse explicit choice, not a quoted constant from the source. This predicate supplies the interpolation implication; construction and growth of the basic sigma factors, the inverse multiplier bound, and a nonzero test derivative remain separate obligations. No regularity or nonvanishing is inferred from totalized meromorphic values.
-- source:
--   Conditional interface for Senthil Kumar K (2026), Lemma 6 and Section 5 equations (30)-(35), including the translated zero set before (35). The doubled inner radius and constant 1/73728 are coarse explicit formalization choices. This definition asserts only the stated interpolation implication. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters
import Mathlib.Analysis.Analytic.Order

noncomputable section

open Filter Metric Set
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Uniform smallness of regularized jets on arbitrary translates of the source
grid, with explicit assumptions for recovering the first unregularized jet. -/
def AuxiliaryGridDecayData (ω u₁ u₂ : ℂ) : Prop :=
  ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
    let m := auxiliaryL0 N
    let s := auxiliaryS N
    let q := auxiliaryS3 N
    let R := auxiliaryRadius N
    let r := 4 * q * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
    let Γ := shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, q]
    ∀ (v : ℂ), ‖v‖ ≤ r →
    ∀ f G ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ G univ →
      (∀ x ∈ Γ.image (fun z => z - v), AnalyticAt ℂ f x) →
      (∀ x ∈ Γ.image (fun z => z - v), AnalyticAt ℂ ψ x) →
      (∀ x ∈ Γ.image (fun z => z - v), G =ᶠ[𝓝 x] fun z => ψ z * f z) →
      (∀ x ∈ Γ.image (fun z => z - v), ∀ j < m + 1, iteratedDeriv j f x = 0) →
      (∀ z ∈ sphere (0 : ℂ) R, ‖G z‖ ≤ Real.exp (B * (N : ℝ) ^ 2)) →
    ∀ (w : ℂ), ‖w‖ + 1 ≤ 2 * r →
    ∀ n : ℕ, (n : ℝ) ≤ K * m →
      ‖iteratedDeriv n G w‖ ≤ Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) ∧
      (AnalyticAt ℂ f w → AnalyticAt ℂ ψ w →
        G =ᶠ[𝓝 w] (fun z => ψ z * f z) →
        (∀ j < n, iteratedDeriv j f w = 0) → ψ w ≠ 0 →
        ‖ψ w‖⁻¹ ≤ Real.exp (B * (N : ℝ) ^ 2) →
        ‖iteratedDeriv n f w‖ ≤ Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728))

end WeierstrassEllipticZeta


