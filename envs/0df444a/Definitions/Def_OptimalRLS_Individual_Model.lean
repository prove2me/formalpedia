-- Prove2me | Definitions.Def_OptimalRLS_Individual_Model
-- name    : OptimalRLS_Individual_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:55:28.615983+00:00
-- url     : https://prove2.me/theorems/918cc030-8cb6-4330-8989-ce41c2c214a2
-- title:
--   Proof of Theorem 3, pp. 26–28 — the hard distributions: γₙ, gₙ, m^(s), σ², ρ_s with Gaussian noise, cₙ, c̃ₙ, Φ, and the law of the random signs S
-- statement:
--   These are the objects of the proof of Theorem 3 (Section 5.4).
--
--   Fix a probability measure $\nu$ on $X$ whose operator $T$ has an eigen-system $(t_n, e_n)_{n \ge 1}$. Fix $B > b$, put $\epsilon = (B - b)c > 0$, and set $d = \dim Y$.
--
--   1. $\gamma_n := n^{-(bc + \epsilon + 1)} \dfrac{\epsilon}{\epsilon + 1} \alpha^c R$, and $g_n := \sqrt{t_n^{-1}\gamma_n}\, e_n$.
--   2. For a sign sequence $s = (s_n) \in \{+1, -1\}^\infty$,
--   $$m^{(s)} := \sum_{n=1}^{\infty} s_n \sqrt{t_n^{-1}\gamma_n}\, e_n = \sum_{n=1}^\infty s_n g_n \in \mathcal H .$$
--   3. $S^d = 2\pi^{d/2}/\Gamma(d/2)$ is the surface area of the unit sphere of $\mathbb R^d$, and
--   $$\sigma^2 = \min\Big(\frac{M^2}{2},\ \frac{\pi^{d/2}\Sigma^2}{4 S^d \int_0^{\infty} e^{-z^2 + z} z^{d+1}\, dz}\Big).$$
--   4. $\rho_s$ is the distribution on $X \times Y$ with marginal $\nu$ and conditional distribution $\rho_s(y \mid x) = \mathcal N(m^{(s)}(x), \sigma^2 \mathrm{Id})$. It is the law of $(x, m^{(s)}(x) + \sigma\xi)$, where $x \sim \nu$ and $\xi$ is an independent standard Gaussian vector in $Y$.
--   5. For $f \in \mathcal H$, $c_n(f) = \sqrt{t_n/\gamma_n}\,\langle f, e_n\rangle_{\mathcal H}$, and $\tilde c_n(f)$ is $1$ if $c_n(f) \ge 0$ and $-1$ otherwise.
--   6. $\Phi$ is the standard normal distribution function.
--   7. The random sign sequence $S = (S_i)$ has independent coordinates with $P[S_i = +1] = P[S_i = -1] = 1/2$.
--
--   The distributions $\rho_s$ form the subset $\mathcal P'$ of $\mathcal P(b, c)$ on which the individual lower rate is proved.
--
--   **Formalization Note** The paper's index $n \ge 1$ is shifted to $n \in \mathbb N$ starting at $0$, so $\gamma_n$ is `gam b c ε α R (n-1)`.
--   - $m^{(s)}$ is a `tsum` in $\mathcal H$. In the theorems that use it, the terms are orthogonal and $\sum \gamma_n/t_n \le \sum (n^b/\alpha)\gamma_n < \infty$, so the series converges and the `tsum` is its sum.
--   - The integral in $\sigma^2$ is of an integrable function, so the Bochner integral is honest.
--   - "The volume of the surface of the $d$-dimensional unit radius sphere" is read as the surface area of the unit sphere in $\mathbb R^d$, which is what the polar-coordinate formula on p. 27 requires.
--   - The sign sequence $S$ is encoded as independent fair coins on `Bool` (`signLaw`), mapped to $\pm 1$ by `sgn`.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proof of Th. 3, pp. 26–28: definitions of γₙ, gₙ, m^(s), P′ and σ² (p. 26), c_{z,n} and c̃_{z,n} (p. 27), S (p. 28); Prop. 7 (Φ), pp. 25–26

import Mathlib
import Definitions.Def_OptimalRLS_Individual_Setting

/-!
# Caponnetto–De Vito (2007), §5.4: the hard distributions of the individual lower rate

Proof of Theorem 3 (p. 26): for `B > b` and `ε := (B − b)c > 0`, an eigen-system `(t_n, e_n)` of the
operator `T` of a fixed marginal `ν` ((52), p. 21), and a sign sequence `s ∈ {+1, −1}^∞`,
`γ_n := n^{−(bc+ε+1)} (ε/(ε+1)) α^c R`, `g_n := √(t_n^{−1} γ_n) e_n`, `m^{(s)} := ∑ s_n g_n`, and the
distribution with marginal `ν` and conditional `ρ(y|x) = N(m^{(s)}(x), σ² Id)`, with
`σ² = min(M²/2, π^{d/2} Σ² / (4 S^d ∫_0^∞ e^{−z²+z} z^{d+1} dz))`.

Index shift: the paper's `t_n, e_n, γ_n, g_n, s_n` (`n ≥ 1`) are `t (n-1)`, `e (n-1)`, `gam … (n-1)`,
`gvec … (n-1)`, `s (n-1)` here, for `n : ℕ` starting at `0`.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace OptimalRLS.Individual

variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [RKHS ℝ H X Y]

/-- `γ_n := n^{−(bc+ε+1)} (ε/(ε+1)) α^c R` (proof of Theorem 3, p. 26), with the index shift: the
paper's `γ_n` (`n ≥ 1`) is `gam b c ε α R (n - 1)`. -/
noncomputable def gam (b c ε α R : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-(b * c + ε + 1)) * (ε / (ε + 1)) * α ^ c * R

/-- `g_n := √(t_n^{−1} γ_n) e_n` (p. 26). -/
noncomputable def gvec (e : ℕ → H) (t : ℕ → ℝ) (γ : ℕ → ℝ) (n : ℕ) : H :=
  Real.sqrt (γ n / t n) • e n

/-- `m^{(s)} := ∑_n s_n √(t_n^{−1} γ_n) e_n = ∑_n s_n g_n ∈ H` (p. 26), for a sign sequence `s`.
In the setting of the theorems that use it (`e` orthonormal, `α ≤ n^b t_n`, `γ` as in `gam` with
`ε > 0`, `c ≥ 1`, `|s_n| = 1`) the terms are orthogonal with `∑ ‖s_n g_n‖² = ∑ γ_n/t_n ≤
∑ (n^b/α) γ_n < ∞`, so the series converges in `H` and the `tsum` is its sum (not the junk value
`0`). -/
noncomputable def mS (e : ℕ → H) (t : ℕ → ℝ) (γ : ℕ → ℝ) (s : ℕ → ℝ) : H :=
  ∑' n, s n • gvec e t γ n

/-- `S^d`, "the volume of the surface of the d-dimensional unit radius sphere" (p. 26), read as the
surface area `2 π^{d/2} / Γ(d/2)` of the unit sphere of `ℝ^d` — the reading required by the
polar-coordinate formula `(2πσ²)^{−d/2} S^d ∫_0^∞ … z^{d−1} dz` for the `N(0, σ² Id)` density on
`ℝ^d` (p. 27). -/
noncomputable def Sd (d : ℕ) : ℝ :=
  2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)

/-- The noise variance of the hard distributions (p. 26):
`σ² = min(M²/2, π^{d/2} Σ² / (4 S^d ∫_0^∞ e^{−z²+z} z^{d+1} dz))`.
The integrand is integrable on `(0, ∞)`, so the Bochner integral is the genuine (positive) value. -/
noncomputable def sig2 (M Sig : ℝ) (d : ℕ) : ℝ :=
  min (M ^ 2 / 2)
    (Real.pi ^ ((d : ℝ) / 2) * Sig ^ 2 /
      (4 * Sd d * ∫ z in Set.Ioi (0 : ℝ), Real.exp (-z ^ 2 + z) * z ^ (d + 1)))

/-- The distribution on `Z = X × Y` with marginal `ν` and conditional distribution
`ρ(y|x) = N(m(x), s2 · Id)`: the law of `(x, m(x) + √s2 · ξ)` with `x ∼ ν` and `ξ` an independent
standard Gaussian vector of the finite-dimensional space `Y` (`stdGaussian Y`, identity
covariance). -/
noncomputable def rhoS [FiniteDimensional ℝ Y] (ν : Measure X) (m : H) (s2 : ℝ) :
    Measure (X × Y) :=
  (ν.prod (stdGaussian Y)).map (fun p : X × Y => (p.1, m p.1 + Real.sqrt s2 • p.2))

/-- The coefficients `c_{z,n} = √(t_n/γ_n) ⟨f, e_n⟩_H` of (63) (p. 27), for an estimate `f = f_z^ℓ`. -/
noncomputable def cn (e : ℕ → H) (t : ℕ → ℝ) (γ : ℕ → ℝ) (f : H) (n : ℕ) : ℝ :=
  Real.sqrt (t n / γ n) * ⟪f, e n⟫_ℝ

/-- `c̃_{z,n}`: `1` if `c_{z,n} ≥ 0` and `−1` otherwise (p. 27). -/
noncomputable def ctil (e : ℕ → H) (t : ℕ → ℝ) (γ : ℕ → ℝ) (f : H) (n : ℕ) : ℝ :=
  if 0 ≤ cn e t γ f n then 1 else -1

/-- `Φ`, the standard normal distribution function: `Φ(x) = P[N(0, 1) ≤ x]`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

/-- The sign map `Bool → {+1, −1}` (`true ↦ 1`, `false ↦ −1`), used to encode the random sign
sequence `S` of p. 28 as a fair coin sequence. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The law of `S = (S_i)_{i ∈ ℕ}` (p. 28): independent fair coins on `Bool`, read as signs through
`sgn`, so that `P[S_i = +1] = P[S_i = −1] = 1/2` for every `i`. -/
noncomputable def signLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

end OptimalRLS.Individual


