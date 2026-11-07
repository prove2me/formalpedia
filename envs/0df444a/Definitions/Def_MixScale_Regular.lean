-- Prove2me | Definitions.Def_MixScale_Regular
-- name    : MixScale_Regular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:48.937259+00:00
-- url     : https://prove2.me/theorems/7d52f047-2bb9-4ab8-b80f-75f4f52e6fdf
-- title:
--   Regular scale-cancellation profiles (Definition F.1) and the dyadic local estimates of Lemma F.3
-- statement:
--   With $r=q+\alpha$, $\tau=\min(q,1)$, integers $m>r-\tau/2$ and $M_{\mathrm{der}}>m+r+4$, and $I=[3/4,5/4]$, an effective profile is **regular** if its one-dimensional law has an even density $f$ with the following properties, writing $f_v(x)=v^{-1/2}f(x/\sqrt v)$:
--
--   1. $f$ is positive and continuous off zero; for some $r_0\in(0,1)$ and $c>0$, $f_v(x)\ge cB_q(|x|)$ for $0<|x|\le r_0$, $v\in I$, where $B_q(u)=u^{q-1}$ for $q<1$, $\log(e/u)$ for $q=1$, and $1$ for $q>1$; and $f_v$ is bounded below uniformly in $v$ on each compact set not containing zero.
--   2. $v\mapsto v^{q/2}f_v$ is continuously differentiable in $L^1$ on $I$, with derivative $h_v$; $\hat h_v$ is bounded on $[-2,2]$, and $|\partial_s^j\hat h_v(s)|\le C_j|s|^{-r-j}$ for $|s|\ge1$, $0\le j\le M_{\mathrm{der}}$, uniformly in $v$, where $\hat g(s)=\int e^{isx}g(x)\,dx$.
--   3. For $|x|\ge r_0/2$, uniformly in $v\in I$, either $f_v(x)\ge c(1+|x|)^{-b}$ and $|h_v^{(m)}(x)|\le C(1+|x|)^{-a}$ with $2a-b>1$, or $f_v(x)\ge ce^{-A|x|}$ and $|h_v^{(m)}(x)|\le Ce^{-B|x|}$ with $2B>A$.
--
--   The module also records the hypotheses and the conclusions of Lemma F.3 as `SymbolBounds` and `DyadicBounds`. These conditions control the numerator and denominator of the testing divergence behind the lower bounds.
--
--   **Formalization Note** $L^1$-differentiability is the $L^1$ limit of difference quotients within $I$, written with lower integrals, and $L^1$-continuity of $v\mapsto h_v$ on $I$. Derivatives of $\hat h_v$ are taken within the closed set $\{|s|\ge1\}$, on which $\hat h_v$ is assumed $C^{M_{\mathrm{der}}}$. Spatial derivatives of $h_v$ are those of a representative $C^m$ off zero, which is existentially quantified (Lemma F.3 supplies it, and it is unique off zero by continuity). The density value at $0$ is irrelevant.
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Definition F.1, p.35 (PDF p.37); (72), p.35; §F.1, p.34; Lemma F.3, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_MixScale_Profile

open MeasureTheory Filter Topology

namespace MixScale

/-!
# Regular scale-cancellation profiles (Definition F.1)

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). Definition F.1, p.35 (PDF p.37), with
(72) on p.35, the Fourier convention and `f_v`, `h_v` of §F.1, p.34 (PDF p.36).

"Definition F.1 (Regular scale-cancellation profile). Let `q, α > 0`, `r = q + α`, and choose an
integer `m > r − τ/2`. An effective profile in definition A.1 is regular for the lower bound if its
one-dimensional law has an even density `f` with the following properties. All constants below are
fixed and uniform for `v ∈ I = [3/4, 5/4]`. 1. The density is positive and continuous off zero. For
some `r₀ ∈ (0, 1)`, `f_v(x) ≥ c B_q(|x|)`, `0 < |x| ≤ r₀` […] (73) The lower bound is uniform on
compact sets separated from zero as well. 2. The map `v ↦ v^{q/2} f_v` is continuously
differentiable in `L¹`, with derivative `h_v`. Its Fourier transform is bounded on `[−2, 2]` and,
for `|s| ≥ 1`, `|∂_s^j ĥ_v(s)| ≤ C_j|s|^{−r−j}`, `0 ≤ j ≤ M_der`, (74) for one specified integer
`M_der > m + r + 4`. […] Spatial derivatives through order `m` use the continuous representatives
supplied by lemma F.3. […] 3. A uniform tail condition holds for `|x| ≥ r₀/2`. Either
`f_v(x) ≥ c(1 + |x|)^{−b}`, `|h_v^{(m)}(x)| ≤ C(1 + |x|)^{−a}`, `2a − b > 1`, (75) or
`f_v(x) ≥ c e^{−A_tail|x|}`, `|h_v^{(m)}(x)| ≤ C e^{−B_tail|x|}`, `2B_tail > A_tail`. (76) […] At
isolated infinite-density points, inequalities and integrals have their almost-everywhere meaning."

Here `f_v(x) = v^{−1/2} f(x/√v)` and `ĝ(s) = ∫ e^{isx} g(x) dx` (p.34, the opposite sign of
Mathlib's `𝓕`).

**Formalization Note.**
* The integers `m`, `M_der` are parameters of `IsRegularProfileAt`; `m > r − τ/2` and
  `M_der > m + r + 4` are strict real inequalities.
* "Its one-dimensional law has density `f`": `f` is measurable, nonnegative and even, `f dx` is a
  probability measure on `ℝ` and its characteristic function is `s ↦ χ(|s|)`.
* `f` is real valued; the value at `0` (the only possible infinite-density point, by continuity off
  zero) is irrelevant to every condition.
* Item 1: `f(x) > 0` for `x ≠ 0` and `f` is continuous on `ℝ ∖ {0}`; one `c > 0` and one
  `r₀ ∈ (0, 1)` serve every `v ∈ I` in (73); for every compact `K ⊆ ℝ ∖ {0}` there is `c_K > 0` with
  `f_v ≥ c_K` on `K` for every `v ∈ I`.
* Item 2: `h : ℝ → ℝ → ℝ` with each `h v` integrable; "continuously differentiable in `L¹`" on `I`
  is the `L¹` difference-quotient limit within `I` and the `L¹` continuity of `v ↦ h v` on `I`, both
  written with lower Lebesgue integrals (so a non-integrable difference has infinite norm). The
  bound on `[−2, 2]` and the constants `C_j` are uniform in `v ∈ I`. The derivatives of `ĥ_v` in
  (74) are derivatives within the closed set `{|s| ≥ 1}`, on which `ĥ_v` is assumed `C^{M_der}`.
* Item 3: the `m`-th spatial derivative of `h_v` is that of a representative `hrep v`, a.e. equal
  to `h v` and `C^m` on `ℝ ∖ {0}` (unique there by continuity). The tail alternative is chosen once,
  with constants uniform in `v ∈ I`; the same `r₀` as in item 1.
-/

/-- The rescaled density `f_v(x) = v^{−1/2} f(x/√v)`. -/
noncomputable def fv (f : ℝ → ℝ) (v x : ℝ) : ℝ := (Real.sqrt v)⁻¹ * f (x / Real.sqrt v)

/-- The central profile `B_q(u)` of (73): `u^{q−1}` (`q < 1`), `log(e/u)` (`q = 1`), `1` (`q > 1`). -/
noncomputable def Bq (q u : ℝ) : ℝ :=
  if q < 1 then u ^ (q - 1) else if q = 1 then Real.log (Real.exp 1 / u) else 1

/-- The Fourier transform with the paper's sign, `ĝ(s) = ∫ e^{isx} g(x) dx`. -/
noncomputable def fourierR (g : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ x, Complex.exp ((s * x : ℝ) * Complex.I) * (g x : ℂ)

/-- The scale interval `I = [3/4, 5/4]`. -/
def scaleI : Set ℝ := Set.Icc (3 / 4) (5 / 4)

/-- Definition F.1 with the integers `m` and `M_der`: `S` is an effective profile (Definition A.1)
whose one-dimensional law has an even density `f` satisfying items 1–3. -/
def IsRegularProfileAt (S : ProfileSpec) (m Mder : ℕ) : Prop :=
  IsEffectiveProfile S ∧
  S.q + S.α - min S.q 1 / 2 < (m : ℝ) ∧
  (m : ℝ) + (S.q + S.α) + 4 < (Mder : ℝ) ∧
  ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f (-x) = f x) ∧
    IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (f x)) ∧
    (∀ s : ℝ, charFun (volume.withDensity fun x => ENNReal.ofReal (f x)) s = (S.χ |s| : ℂ)) ∧
    -- item 1
    (∀ x, x ≠ 0 → 0 < f x) ∧ ContinuousOn f {x | x ≠ 0} ∧
    ∃ c r0 : ℝ, 0 < c ∧ 0 < r0 ∧ r0 < 1 ∧
      (∀ v ∈ scaleI, ∀ x : ℝ, 0 < |x| → |x| ≤ r0 → c * Bq S.q |x| ≤ fv f v x) ∧
      (∀ K : Set ℝ, IsCompact K → (0 : ℝ) ∉ K →
        ∃ cK : ℝ, 0 < cK ∧ ∀ v ∈ scaleI, ∀ x ∈ K, cK ≤ fv f v x) ∧
    -- item 2
    ∃ h : ℝ → ℝ → ℝ, (∀ v ∈ scaleI, Integrable (h v)) ∧
      (∀ v ∈ scaleI, Tendsto (fun v' => ∫⁻ x, ENNReal.ofReal
          |(v' ^ (S.q / 2) * fv f v' x - v ^ (S.q / 2) * fv f v x) / (v' - v) - h v x|)
        (𝓝[scaleI \ {v}] v) (𝓝 0)) ∧
      (∀ v ∈ scaleI, Tendsto (fun v' => ∫⁻ x, ENNReal.ofReal |h v' x - h v x|)
        (𝓝[scaleI] v) (𝓝 0)) ∧
      (∃ C0 : ℝ, ∀ v ∈ scaleI, ∀ s ∈ Set.Icc (-2 : ℝ) 2, ‖fourierR (h v) s‖ ≤ C0) ∧
      (∀ v ∈ scaleI, ContDiffOn ℝ Mder (fourierR (h v)) {s | 1 ≤ |s|}) ∧
      (∃ Cj : ℕ → ℝ, ∀ v ∈ scaleI, ∀ j ≤ Mder, ∀ s : ℝ, 1 ≤ |s| →
        ‖iteratedDerivWithin j (fourierR (h v)) {s | 1 ≤ |s|} s‖ ≤
          Cj j * |s| ^ (-(S.q + S.α) - j)) ∧
    -- item 3
      ∃ hrep : ℝ → ℝ → ℝ,
        (∀ v ∈ scaleI, hrep v =ᵐ[volume] h v ∧ ContDiffOn ℝ m (hrep v) {x | x ≠ 0}) ∧
        ((∃ c' C' a b : ℝ, 0 < c' ∧ 1 < 2 * a - b ∧ ∀ v ∈ scaleI, ∀ x : ℝ, r0 / 2 ≤ |x| →
            c' * (1 + |x|) ^ (-b) ≤ fv f v x ∧ |iteratedDeriv m (hrep v) x| ≤ C' * (1 + |x|) ^ (-a)) ∨
         (∃ c' C' At Bt : ℝ, 0 < c' ∧ At < 2 * Bt ∧ ∀ v ∈ scaleI, ∀ x : ℝ, r0 / 2 ≤ |x| →
            c' * Real.exp (-At * |x|) ≤ fv f v x ∧
              |iteratedDeriv m (hrep v) x| ≤ C' * Real.exp (-Bt * |x|)))

/-- The hypotheses of Lemma F.3 on `g` with constants `C0`, `C_j`: `g ∈ L¹(ℝ)` is even, `|ĝ| ≤ C0`
on `[−2, 2]`, `ĝ` is `C^{N_der}` on `{|s| ≥ 1}` and `|∂_s^j ĝ(s)| ≤ C_j|s|^{−r−j}` there for
`j ≤ N_der` (derivatives within `{|s| ≥ 1}`). -/
def SymbolBounds (r : ℝ) (Nder : ℕ) (C0 : ℝ) (Cj : ℕ → ℝ) (g : ℝ → ℝ) : Prop :=
  Integrable g ∧ (∀ x, g (-x) = g x) ∧ (∀ s ∈ Set.Icc (-2 : ℝ) 2, ‖fourierR g s‖ ≤ C0) ∧
    ContDiffOn ℝ Nder (fourierR g) {s | 1 ≤ |s|} ∧
    ∀ j ≤ Nder, ∀ s : ℝ, 1 ≤ |s| →
      ‖iteratedDerivWithin j (fourierR g) {s | 1 ≤ |s|} s‖ ≤ Cj j * |s| ^ (-r - j)

/-- The conclusions of Lemma F.3 for `g` with the representative `gt` and the constant `C`:
`gt = g` a.e. and `gt` is `C^J` off zero; for `0 < |x| ≤ 1`, (80) `|gt| ≤ C|x|^{r−1}` if `r < 1`,
(81) `|gt′| ≤ C|x|^{−1}` if `r = 1`, (82) `|gt^{(m)}| ≤ C|x|^{r−1−m}` for `r − 1 < m ≤ J`, and
`|gt| ≤ C log(e/|x|)` if `r = 1`; if `r > 1`, `ĝ ∈ L¹` and `|gt| ≤ C` off zero. -/
def DyadicBounds (J : ℕ) (r C : ℝ) (g gt : ℝ → ℝ) : Prop :=
  gt =ᵐ[volume] g ∧ ContDiffOn ℝ J gt {x | x ≠ 0} ∧
    (r < 1 → ∀ x : ℝ, 0 < |x| → |x| ≤ 1 → |gt x| ≤ C * |x| ^ (r - 1)) ∧
    (r = 1 → ∀ x : ℝ, 0 < |x| → |x| ≤ 1 → |deriv gt x| ≤ C * |x|⁻¹) ∧
    (∀ m : ℕ, r - 1 < m → m ≤ J → ∀ x : ℝ, 0 < |x| → |x| ≤ 1 →
      |iteratedDeriv m gt x| ≤ C * |x| ^ (r - 1 - m)) ∧
    (r = 1 → ∀ x : ℝ, 0 < |x| → |x| ≤ 1 → |gt x| ≤ C * Real.log (Real.exp 1 / |x|)) ∧
    (1 < r → Integrable (fourierR g) ∧ ∀ x : ℝ, x ≠ 0 → |gt x| ≤ C)

end MixScale


