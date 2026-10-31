-- Prove2me | Definitions.Def_FairDiffusionLimit_DCP
-- name    : FairDiffusionLimit_DCP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:28:02.235678+00:00
-- url     : https://prove2.me/theorems/ef857f4e-329a-40cc-baa8-c1fcf9311be9
-- title:
--   The DCP (27)–(32) and (38)–(43), stability, the diffusion limit and its stationary law, the fluid model (55)–(59), weak convergence, uniform integrability, return time
-- statement:
--   This module defines the limit objects of the paper.
--
--   1. **DCP** (27)–(32), p. 13, driven by a path $X$: $w(t)=w(0)+X(t)+BGy(t)+BHz(t)\ge0$, $G^Tw(t)\ge0$, $y_\ell$ nondecreasing with $y_\ell(0)=0$, $\int_0^\infty w(t)^TG\,dy(t)=0$, $H^Tw(t)=0$, $z(0)=0$. With $X(t)=\theta t$ it is the deterministic DCP (38)–(43), p. 14.
--   2. **Stability** (p. 15): there is $T$ such that every solution of (38)–(43) with $|\hat w(0)|\le1$ has $\hat w(t)=0$ for $t\ge T$.
--   3. **The diffusion limit**: $\hat X$ is a Brownian motion with drift $\theta$ and covariance $\Upsilon$, independent of $\hat W(0)$, and $(\hat W,\hat Y,\hat Z)$ solves (27)–(32) almost surely. A stationary distribution $\mu$ of $\hat W$ is carried by $\mathcal W$, can be used as an initial law, and is preserved: $\hat W(0)\sim\mu$ implies $\hat W(t)\sim\mu$. Positive recurrence (Dupuis–Williams): from every $x\in\mathcal W$ the expected hitting time of every open set meeting $\mathcal W$ is finite.
--   4. **The fluid model of network $k$** (55)–(59), p. 17:
--   $$\hat w^k(t)=\hat w^k(0)-k\rho^k\big(te\wedge\bar u^k(1)/k\big)+k\big(\bar d^k(t)\wedge\bar v^k(1)/k\big)+k\rho^kt-k\bar d^k(t),$$
--   $\bar d^k(t)=\int_0^t\bar\Lambda(\hat n^k(s))\,ds$ with $\bar\Lambda_r(n)=\Lambda_r(n)$ if $n_r>0$ and $\rho^k_r$ if $n_r=0$, $\hat y^k(t)=k[ct-A\bar d^k(t)]$ nondecreasing, $\hat z^k(t)=kH^T[\rho t-\bar d^k(t)]$, and $\hat w^k\ge0$.
--   5. **Weak convergence of processes** u.o.c. on $[0,\infty)$, in coupling form on every $[0,T]$; **uniform integrability** of a family of nonnegative random variables on different spaces, $\lim_{K\to\infty}\sup_iE[Y_i;Y_i>K]=0$; the **return time** $\tau^k_C(\delta)=\inf\{t\ge\delta:\hat\Xi^k(t)\in C\}$ (p. 23).
--
--   **Formalization Note** DCP solutions are continuous, and the complementarity (30) is stated as "$y_\ell$ is constant on every interval on which $(G^Tw)_\ell>0$", equivalent for continuous paths. In (59) and in $\hat n^k_r=\hat w^k_r/\nu^k_r$ the $k$-th network's $\rho^k_r$, $\nu^k_r$ are used where the page prints $\rho_r$, $\nu_r$: with $\rho_r$ a fluid class at $0$ is drained at the wrong rate and the model has no nonnegative solution (example: $L=R=1$, $\lambda^k=1-1/k$). Hitting and return times take values in $[0,\infty]$ with $\inf\emptyset=\infty$.
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), pp.13–17: (27)–(33), (38)–(43), stability p.15, Theorem 4 p.16, (55)–(59) p.17, p.12 (u.o.c.), p.23 (τ^k_C(δ))

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_FairDiffusionLimit_Dynamics

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

namespace NetSeq

variable {L R : ℕ} (S : NetSeq L R)

/-- `(w, y, z)` solves the **dynamic complementarity problem** (DCP) driven by the input path `X`,
(27)–(32), p. 13 (with `X = X̂`), and (38)–(43), p. 14 (with `X(t) = θt`): for all `t ≥ 0`,
* (27)/(38) `w(t) = w(0) + X(t) + BGy(t) + BHz(t) ≥ 0`;
* (28)/(39) `Gᵀw(t) ≥ 0`;
* (29)/(40) every `y_ℓ` is nondecreasing on `[0, ∞)` with `y_ℓ(0) = 0`;
* (30)/(41) `∫₀^∞ w(t)ᵀG dy(t) = 0`, encoded as: `y_ℓ` is constant on every interval `[s, t]` on
  which `(Gᵀw)_ℓ > 0`;
* (31)/(42) `Hᵀw(t) = 0`;
* (32)/(43) `z(0) = 0`.
(28) and (31) at `t = 0` say `w(0) ∈ 𝒲`, by (21).

**Formalization Note.** Solutions are continuous on `[0, ∞)` (the DCP is posed for the continuous
limit processes, p. 12–13). For continuous paths with `Gᵀw ≥ 0` and `y` nondecreasing, (30) is
equivalent to the interval form used here. -/
def IsDCPSol (H : Matrix (Fin R) (Fin (R - L)) ℝ) (X : ℝ → Fin R → ℝ) (w : ℝ → Fin R → ℝ)
    (y : ℝ → Fin L → ℝ) (z : ℝ → Fin (R - L) → ℝ) : Prop :=
  ContinuousOn w (Set.Ici 0) ∧ ContinuousOn y (Set.Ici 0) ∧ ContinuousOn z (Set.Ici 0) ∧
  (∀ t : ℝ, 0 ≤ t → w t = w 0 + X t + S.B *ᵥ (S.G *ᵥ y t) + S.B *ᵥ (H *ᵥ z t)) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ w t) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ S.Gᵀ *ᵥ w t) ∧
  MonotoneOn y (Set.Ici 0) ∧ y 0 = 0 ∧
  (∀ ℓ : Fin L, ∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ q ∈ Set.Icc s t, 0 < (S.Gᵀ *ᵥ w q) ℓ) →
    y t ℓ = y s ℓ) ∧
  (∀ t : ℝ, 0 ≤ t → Hᵀ *ᵥ w t = 0) ∧
  z 0 = 0

/-- The deterministic DCP (38)–(43) is **stable** (p. 15): there is a time `T` such that every
solution with `|ŵ(0)| ≤ 1` has `ŵ(t) = 0` for all `t ≥ T`. -/
def DetStable (H : Matrix (Fin R) (Fin (R - L)) ℝ) : Prop :=
  ∃ T : ℝ, ∀ (w : ℝ → Fin R → ℝ) (y : ℝ → Fin L → ℝ) (z : ℝ → Fin (R - L) → ℝ),
    S.IsDCPSol H (fun t => t • S.θ) w y z → l1 (w 0) ≤ 1 → ∀ t : ℝ, T ≤ t → w t = 0

/-- `(W, X, Y, Z)` on `(Ω, P)` is **the diffusion limit** of Theorem 1 (p. 13): `X̂ = X` is a
Brownian motion with drift `θ`, covariance `Υ` (33) and `X(0) = 0` (published
`Reiman84.QueueLength.IsDriftedBM`), the initial state `Ŵ(0) = W(·, 0)` is independent of `X`,
every `Ŵ(t)` is a random vector, and almost surely `(W, Y, Z)` solves the DCP (27)–(32) driven by
`X`. -/
def IsDiffSol (H : Matrix (Fin R) (Fin (R - L)) ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W X : Ω → ℝ → Fin R → ℝ) (Y : Ω → ℝ → Fin L → ℝ) (Z : Ω → ℝ → Fin (R - L) → ℝ) : Prop :=
  Reiman84.QueueLength.IsDriftedBM S.θ S.Upsilon P X ∧
  IndepFun (fun ω => W ω 0) X P ∧
  (∀ t, Measurable fun ω => W ω t) ∧
  ∀ᵐ ω ∂P, S.IsDCPSol H (X ω) (W ω) (Y ω) (Z ω)

/-- `μ` is a **stationary distribution of the diffusion limit** `Ŵ` (the `π̂₁` of p. 24): `μ` is a
probability measure carried by `𝒲`, the diffusion can be started from `μ`, and whenever
`Ŵ(0) ∼ μ` (independent of the Brownian motion `X̂`), `Ŵ(t) ∼ μ` for all `t ≥ 0`.

**Formalization Note.** The existence conjunct prevents the definition from holding vacuously. -/
def IsDiffStationary (H : Matrix (Fin R) (Fin (R - L)) ℝ) (μ : Measure (Fin R → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ S.Wconeᶜ = 0 ∧
  (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W X : Ω → ℝ → Fin R → ℝ)
      (Y : Ω → ℝ → Fin L → ℝ) (Z : Ω → ℝ → Fin (R - L) → ℝ),
      S.IsDiffSol H P W X Y Z ∧ P.map (fun ω => W ω 0) = μ) ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W X : Ω → ℝ → Fin R → ℝ)
      (Y : Ω → ℝ → Fin L → ℝ) (Z : Ω → ℝ → Fin (R - L) → ℝ),
      S.IsDiffSol H P W X Y Z → P.map (fun ω => W ω 0) = μ →
      ∀ t : ℝ, 0 ≤ t → P.map (fun ω => W ω t) = μ

/-- The hitting time `inf{t ≥ 0 : w(t) ∈ U}` of a path, in `[0, ∞]` (`inf ∅ = ∞`). -/
noncomputable def hitTime (U : Set (Fin R → ℝ)) (w : ℝ → Fin R → ℝ) : ENNReal :=
  ⨅ t ∈ {t : ℝ | 0 ≤ t ∧ w t ∈ U}, ENNReal.ofReal t

/-- The diffusion limit `Ŵ` is **positive recurrent** (Theorem 4, p. 16, in the sense of
Dupuis–Williams [17]): from every initial state `x ∈ 𝒲`, the expected hitting time of every open set
`U` that meets `𝒲` is finite. -/
def PosRecurrentDiff (H : Matrix (Fin R) (Fin (R - L)) ℝ) : Prop :=
  ∀ x ∈ S.Wcone, ∀ U : Set (Fin R → ℝ), IsOpen U → (U ∩ S.Wcone).Nonempty →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W X : Ω → ℝ → Fin R → ℝ)
      (Y : Ω → ℝ → Fin L → ℝ) (Z : Ω → ℝ → Fin (R - L) → ℝ),
      S.IsDiffSol H P W X Y Z → (∀ ω, W ω 0 = x) → ∫⁻ ω, hitTime U (W ω) ∂P < ⊤

/-- `Λ̄^k(n)`, (59), p. 17, for the fluid model of network `k`: `Λ̄_r(n) = Λ_r(n)` if `n_r > 0` and
`ρ^k_r` if `n_r = 0` (the paper prints `ρ_r`; see the Formalization Note of `IsFluidSol`). -/
noncomputable def LamBar (k : ℕ) (n : Fin R → ℝ) : Fin R → ℝ :=
  fun r => if 0 < n r then S.Lam n r else S.rhoK k r

/-- `(ŵ^k, d̄^k, ŷ^k, ẑ^k)` with residual parameters `ū^k(1) = ub`, `v̄^k(1) = vb` solves the
**fluid model of network `k`**, (55)–(59), p. 17: with `ŵ^k(0) = w(0)`, `ub, vb ≥ 0`, `e` the all-ones
vector and `∧` the componentwise minimum, for all `t ≥ 0`,
* (55) `ŵ^k(t) = ŵ^k(0) − kρ^k(te ∧ ū^k(1)/k) + k(d̄^k(t) ∧ v̄^k(1)/k) + kρ^kt − kd̄^k(t)`, and
  `ŵ^k(t) ≥ 0`;
* (56) `d̄^k(t) = ∫₀ᵗ Λ̄(n̂^k(s)) ds`, with `n̂^k_r = ŵ^k_r/ν^k_r` (the convention `w_r = ν_r n_r` of the
  `k`-th network) and the integrand integrable on `[0, t]`;
* (57) `ŷ^k(t) = k[ct − Ad̄^k(t)]` is nondecreasing;
* (58) `ẑ^k(t) = kHᵀ[ρt − d̄^k(t)]`.

**Formalization Note.** The `k`-th network's parameters are used in (59) (`ρ^k_r`) and in the
convention `ŵ^k_r = ν^k_r n̂^k_r`, where the page prints `ρ_r` and `ν_r`. With `ρ_r` a class whose
fluid workload is `0` would be drained at rate `ρ_r ≠ ρ^k_r`: for `L = R = 1`, `A = c = β = ν^k = 1`,
`λ^k = 1 − 1/k`, `ŵ^k` started at `1/2` with zero residuals decreases at slope `−1` until it hits `0`
and then can neither stay at `0` (that needs `d̄' = ρ^k`) nor stay nonnegative. Nonnegativity of
`ŵ^k` (the state space) is part of the model. -/
def IsFluidSol (H : Matrix (Fin R) (Fin (R - L)) ℝ) (k : ℕ) (ub vb : Fin R → ℝ)
    (w d : ℝ → Fin R → ℝ) (y : ℝ → Fin L → ℝ) (z : ℝ → Fin (R - L) → ℝ) : Prop :=
  0 ≤ w 0 ∧ 0 ≤ ub ∧ 0 ≤ vb ∧
  (∀ t : ℝ, 0 ≤ t → ∀ r, w t r = w 0 r - (k : ℝ) * S.rhoK k r * min t (ub r / k)
      + (k : ℝ) * min (d t r) (vb r / k) + (k : ℝ) * S.rhoK k r * t - (k : ℝ) * d t r) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ w t) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ r,
    IntervalIntegrable (fun s => S.LamBar k (fun r' => w s r' / S.nu k r') r) volume 0 t ∧
    d t r = ∫ s in (0 : ℝ)..t, S.LamBar k (fun r' => w s r' / S.nu k r') r) ∧
  (∀ t : ℝ, 0 ≤ t → y t = (k : ℝ) • (t • S.c - S.A *ᵥ d t)) ∧ MonotoneOn y (Set.Ici 0) ∧
  (∀ t : ℝ, 0 ≤ t → z t = (k : ℝ) • (Hᵀ *ᵥ (t • S.rho - d t)))

end NetSeq

/-- The path `x` restricted to `[0, T]` and extended constantly outside. -/
noncomputable def onIcc {E : Type} (T : ℝ) (x : ℝ → E) : ℝ → E :=
  fun t => x (min (max t 0) T)

/-- **Weak convergence `Xⁿ ⇒ X` of processes, u.o.c. on `[0, ∞)`** (pp. 12–13), in coupling
(Skorohod representation) form: for every `T ≥ 0` there is a probability space carrying paths `Yⁿ`,
`Y` with `Yⁿ` distributed as `Xⁿ` on `[0, T]`, `Y` distributed as `X` on `[0, T]`, and
`sup_{0≤t≤T} ‖Yⁿ(t) − Y(t)‖ → 0` almost surely. Paths take values in a normed space `E` (a product
of the coordinate spaces of the jointly converging processes), so the convergence is joint.

**Formalization Note.** The paper works in `D` with the u.o.c. topology, equivalent to Skorohod's
because the limits are continuous (p. 12); weak convergence in it is equivalent to weak convergence
of the restrictions to every `[0, T]` in the uniform topology. -/
def WeakConvUoc {E : Type} [NormedAddCommGroup E] [MeasurableSpace E]
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ → E)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X' : Ω' → ℝ → E) : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (Y : ℕ → Ω₀ → ℝ → E)
      (Y' : Ω₀ → ℝ → E),
      IsProbabilityMeasure Q ∧ (∀ n, Measurable (Y n)) ∧ Measurable Y' ∧
      (∀ n, Q.map (Y n) = (P n).map (fun ω => onIcc T (X n ω))) ∧
      Q.map Y' = P'.map (fun ω => onIcc T (X' ω)) ∧
      ∀ᵐ ω ∂Q, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖Y n ω t - Y' ω t‖ < ε

/-- **Uniform integrability** of a family `(Yᵢ)_{i ∈ s}` of `[0, ∞]`-valued random variables, each on
its own probability space: `lim_{K→∞} sup_{i ∈ s} E[Yᵢ; Yᵢ > K] = 0`. -/
def UnifIntegrableOn {ι : Type} (s : Set ι) (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) (Y : ∀ i, Ω i → ENNReal) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ K : ENNReal, K < ⊤ ∧
    ∀ i ∈ s, ∫⁻ ω, {ω | K < Y i ω}.indicator (Y i) ω ∂(P i) ≤ ε

namespace NetSeq

variable {L R : ℕ} (S : NetSeq L R)

/-- The return time `τ^k_C(δ) = inf{t ≥ δ : Ξ̂^k(t) ∈ C}` to a set `C ⊆ 𝒳` after an initial period `δ`
(p. 23), along a sample path of network `k`, in `[0, ∞]` (`inf ∅ = ∞`). -/
noncomputable def returnTime (k : ℕ) (C : Set (State R)) (δ : ℝ) (π : PathData R) : ENNReal :=
  ⨅ t ∈ {t : ℝ | δ ≤ t ∧ S.hatXi k π t ∈ C}, ENNReal.ofReal t

end NetSeq

end FairDiffusionLimit


