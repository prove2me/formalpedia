-- Prove2me | Definitions.Def_ViscosityPPDE_Comparison_Calculus
-- name    : ViscosityPPDE_Comparison_Calculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:05.027597+00:00
-- url     : https://prove2.me/theorems/31a1dba8-c2ec-459c-8a8f-d3c9326f31ae
-- title:
--   Definitions 2.1, 2.3, (2.2)–(2.4), (2.7), (2.11) — $C^0$, $C^0_b$, $C^{1,2}_b$, Dupire derivatives, $\mathcal T^t$, $\mathcal T^t_+$
-- statement:
--   Let $t \le T$ and work on $\Lambda^t = [t,T] \times \Omega^t$ and $\hat\Lambda^t = [t,T]\times\hat\Omega^t$.
--
--   1. A field $u : \Lambda^t \to \mathbb R$ is in $C^0(\Lambda^t)$ if it is $\mathbb F^t$-progressively measurable and continuous in $(s,\omega)$ under $d_\infty$; $u \in C^0_b(\Lambda^t)$ if moreover $u$ is bounded. The same definitions on $\hat\Lambda^t$ give $C^0(\hat\Lambda^t)$ and $C^0_b(\hat\Lambda^t)$.
--   2. For $\hat u$ on $\hat\Lambda^t$, the **Dupire space derivatives** (2.2) are
--   $$\partial_{\omega_i}\hat u(s,\hat\omega) = \lim_{h\to0}\frac1h\big[\hat u(s,\hat\omega + h\mathbf 1_{[s,T]}e_i) - \hat u(s,\hat\omega)\big],\qquad \partial_{\omega_i\omega_j}\hat u = \partial_{\omega_i}(\partial_{\omega_j}\hat u),$$
--   the **right time derivative** (2.3) is $\partial_t\hat u(s,\hat\omega) = \lim_{h\downarrow0}\frac1h[\hat u(s+h,\hat\omega_{\cdot\wedge s}) - \hat u(s,\hat\omega)]$ for $s<T$, and at $T$ it is the limit (2.4) of $\partial_t \hat u(s,\hat\omega)$ as $s\uparrow T$.
--   3. $\hat u \in C^{1,2}_b(\hat\Lambda^t)$ if $\hat u \in C^0(\hat\Lambda^t)$ and $\partial_t\hat u$, $\partial_\omega\hat u$, $\partial^2_{\omega\omega}\hat u$ exist and lie in $C^0_b(\hat\Lambda^t)$ (Definition 2.1(iii)); $\hat u$ itself need not be bounded.
--   4. $\varphi : \Lambda^t \to \mathbb R$ is in $C^{1,2}_b(\Lambda^t)$ if it is progressively measurable and some $\hat\varphi \in C^{1,2}_b(\hat\Lambda^t)$ is consistent with it, $\hat\varphi = \varphi$ on $\Lambda^t$ (2.5), Definition 2.3(iii).
--   5. $\mathcal T^t$ (2.7) is the set of $\mathbb F^t$-stopping times $\tau$ with values in $[t,T]$ such that for every $s\in[t,T)$ the set $\{\tau > s\}$ is open in $(\Omega^t, \|\cdot\|_T)$; $\mathcal T^t_+ = \{\tau\in\mathcal T^t : \tau > t\}$ for $t<T$ and $\mathcal T^T_+ = \{T\}$ (2.11).
--   6. For $u$ on $\Lambda$ and a constant $c$, the hitting time $\tau = \inf\{s : u(s,\omega)\ge c\}\wedge T$ of Example 2.5, with the infimum over $[0,T]$ read as $+\infty$ when the set is empty.
--
--   These classes are the regularity scale of the paper: viscosity solutions are $C^0_b$, test functions are $C^{1,2}_b$, and localisation uses the stopping times of $\mathcal T^t$.
--
--   **Formalization Note** A field on $\hat\Lambda^t$ is a function of all paths; only its values on $\hat\Omega^t$ enter. A candidate $C^{1,2}_b$ field is a tuple $(\hat u, \partial_t\hat u, \partial_\omega\hat u, \partial^2_{\omega\omega}\hat u)$ and the predicate says the last three are its derivatives; by Theorem 2.4(i) of the paper the derivatives of $\varphi$ on $\Lambda^t$ do not depend on the extension, and every later definition quantifies over all such tuples. With the convention that paths of $\hat\Omega^t$ are constant on $[0,t]$, the bump $h\mathbf 1_{[s,T]}e_i$ at $s=t$ moves the whole path. Progressive measurability is required of the field clamped to $[t,T]$, so its values outside $[t,T]$ are unconstrained.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, (2.2)–(2.4), Definition 2.1, p. 4; Definition 2.3, (2.5), (2.7), p. 5; Example 2.5, p. 6; Sec. 2.4, (2.11), pp. 7–8

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

variable {d : ℕ}

/-- The time `s` clamped to `[t, T]`: `t ∨ (s ∧ T)`. Fields on `Λ^t` are only read on `[t, T]`. -/
def clampT (T t s : ℝ≥0) : ℝ≥0 := max t (min s T)

/-- `u : Λ^t → ℝ` is `𝔽^t`-progressively measurable (its values outside `[t, T]` are ignored). -/
def IsProg (T t : ℝ≥0) (u : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  IsStronglyProgressive (filt d T t) (fun s ω => u (clampT T t s) ω)

/-- `u ∈ C^0(Λ^t)`: progressively measurable and continuous in `(s, ω)` on `[t,T] × Ω^t`
under `d_∞`. -/
def IsC0 (T t : ℝ≥0) (u : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  IsProg T t u ∧
    ∀ s ω, t ≤ s → s ≤ T → ∀ ε > 0, ∃ δ > 0, ∀ s' ω', t ≤ s' → s' ≤ T →
      DInfLt T s ω.1 s' ω'.1 δ → |u s ω - u s' ω'| < ε

/-- `u ∈ C^0_b(Λ^t)`: `u ∈ C^0(Λ^t)` and `u` is bounded on `[t,T] × Ω^t`. -/
def IsC0b (T t : ℝ≥0) (u : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  IsC0 T t u ∧ ∃ C, ∀ s ω, t ≤ s → s ≤ T → |u s ω| ≤ C

/-- A field on `Λ̂^t = [t,T] × Ω̂^t`, given as a function on all paths; only its values at
`s ∈ [t,T]` and `ω̂ ∈ Ω̂^t` matter. `û ∈ C^0(Λ̂^t)`: progressively measurable for `𝔽̂^t` and
continuous under `d_∞` on `[t,T] × Ω̂^t`. -/
def IsC0Hat (T t : ℝ≥0) (u : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ) : Prop :=
  IsStronglyProgressive (filtHat d T t) (fun s (ω : OmegaHat d T t) => u (clampT T t s) ω.1) ∧
    ∀ s ω, t ≤ s → s ≤ T → ω ∈ OmegaHatSet d T t → ∀ ε > 0, ∃ δ > 0, ∀ s' ω', t ≤ s' → s' ≤ T →
      ω' ∈ OmegaHatSet d T t → DInfLt T s ω s' ω' δ → |u s ω - u s' ω'| < ε

/-- `û ∈ C^0_b(Λ̂^t)`: `û ∈ C^0(Λ̂^t)` and bounded on `[t,T] × Ω̂^t`. -/
def IsC0bHat (T t : ℝ≥0) (u : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ) : Prop :=
  IsC0Hat T t u ∧ ∃ C, ∀ s ω, t ≤ s → s ≤ T → ω ∈ OmegaHatSet d T t → |u s ω| ≤ C

/-- The bumped path `ω̂ + h 1_{[s,T]} e_i` of (2.2) in `Ω̂^t`. With the convention that paths of
`Ω̂^t` are constant on `[0,t]`, the bump at `s = t` moves the whole path. -/
noncomputable def bump (t s : ℝ≥0) (ω : ℝ≥0 → Rd d) (i : Fin d) (h : ℝ) : ℝ≥0 → Rd d :=
  fun r => if s ≤ max r t then ω r + h • EuclideanSpace.single i (1 : ℝ) else ω r

/-- The stopped path `ω̂_{· ∧ s}`. -/
def stopPath (ω : ℝ≥0 → Rd d) (s : ℝ≥0) : ℝ≥0 → Rd d := fun r => ω (min r s)

/-- Candidate data `(û, ∂_t û, ∂_ω û, ∂²_{ωω} û)` for a field on `Λ̂^t`; `∂_ω û` is a vector of
`ℝ^d` (a row vector in the paper) and `∂²_{ωω} û` a `d × d` matrix. -/
structure C12Data (d : ℕ) where
  fn : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ
  dt : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ
  dw : ℝ≥0 → (ℝ≥0 → Rd d) → Rd d
  dww : ℝ≥0 → (ℝ≥0 → Rd d) → Matrix (Fin d) (Fin d) ℝ

/-- `X.fn ∈ C^{1,2}_b(Λ̂^t)` with derivatives `X.dt, X.dw, X.dww` (Definition 2.1(iii), shifted):
`X.fn ∈ C^0(Λ̂^t)`; the Dupire space derivatives (2.2) exist, `∂_{ω_i} û(s, ω̂)` being the
two-sided derivative at `h = 0` of `h ↦ û(s, ω̂ + h 1_{[s,T]} e_i)` and
`∂_{ω_i ω_j} û = ∂_{ω_i}(∂_{ω_j} û)`; the right time derivative (2.3)
`∂_t û(s, ω̂) = lim_{h ↓ 0} (û(s+h, ω̂_{·∧s}) − û(s, ω̂))/h` exists for `s < T`, and at `T` it is the
limit (2.4) of `∂_t û(s, ω̂)` as `s ↑ T`; and `∂_t û`, `∂_ω û`, `∂²_{ωω} û ∈ C^0_b(Λ̂^t)`. -/
def IsC12bHat (T t : ℝ≥0) (X : C12Data d) : Prop :=
  IsC0Hat T t X.fn ∧ IsC0bHat T t X.dt ∧ (∀ i, IsC0bHat T t (fun s ω => X.dw s ω i)) ∧
    (∀ i j, IsC0bHat T t (fun s ω => X.dww s ω i j)) ∧
    (∀ s ω, t ≤ s → s ≤ T → ω ∈ OmegaHatSet d T t → ∀ i,
      HasDerivAt (fun h => X.fn s (bump t s ω i h)) (X.dw s ω i) 0) ∧
    (∀ s ω, t ≤ s → s ≤ T → ω ∈ OmegaHatSet d T t → ∀ i j,
      HasDerivAt (fun h => X.dw s (bump t s ω i h) j) (X.dww s ω i j) 0) ∧
    (∀ s ω, t ≤ s → s < T → ω ∈ OmegaHatSet d T t →
      Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ * (X.fn (s + h) (stopPath ω s) - X.fn s ω))
        (𝓝[>] 0) (𝓝 (X.dt s ω))) ∧
    (∀ ω, ω ∈ OmegaHatSet d T t →
      Tendsto (fun s => X.dt s ω) (𝓝[Set.Ico t T] T) (𝓝 (X.dt T ω)))

/-- `φ ∈ C^{1,2}_b(Λ^t)` witnessed by `X` (Definition 2.3(iii), shifted): `φ` is progressively
measurable, `X.fn ∈ C^{1,2}_b(Λ̂^t)`, and `X.fn` is consistent with `φ` on `Λ^t` (2.5). -/
def ExtC12b (T t : ℝ≥0) (φ : ℝ≥0 → Omega d T t → ℝ) (X : C12Data d) : Prop :=
  IsProg T t φ ∧ IsC12bHat T t X ∧ ∀ s (ω : Omega d T t), t ≤ s → s ≤ T → X.fn s ω.1 = φ s ω

/-- `τ` is an `𝔽^t`-stopping time with values in `[t, T]`. -/
def IsStop (T t : ℝ≥0) (τ : Omega d T t → ℝ≥0) : Prop :=
  (∀ ω, t ≤ τ ω ∧ τ ω ≤ T) ∧ ∀ s, MeasurableSet[filt d T t s] {ω | τ ω ≤ s}

/-- `τ ∈ 𝒯^t` ((2.7), shifted): an `𝔽^t`-stopping time with values in `[t,T]` such that for
every `s ∈ [t, T)` the set `{τ > s}` is open in `(Ω^t, ‖·‖_T)`. -/
def IsStopT (T t : ℝ≥0) (τ : Omega d T t → ℝ≥0) : Prop :=
  IsStop T t τ ∧ ∀ s, t ≤ s → s < T → ∀ ω, s < τ ω →
    ∃ η > 0, ∀ ω', SupNormLt T (ω'.1 - ω.1) η → s < τ ω'

/-- `τ ∈ 𝒯^t_+` (2.11): `τ ∈ 𝒯^t` and `τ > t` when `t < T` (for `t = T`, `τ ≡ T`). -/
def IsStopTPlus (T t : ℝ≥0) (τ : Omega d T t → ℝ≥0) : Prop :=
  IsStopT T t τ ∧ (t < T → ∀ ω, t < τ ω)

/-- The hitting time `τ = inf{s : u(s, ω) ≥ c} ∧ T` of Example 2.5, the infimum taken over
`s ∈ [0, T]` and read as `+∞` (so `τ = T`) when no such `s` exists. -/
noncomputable def hitTime (T : ℝ≥0) (u : ℝ≥0 → Omega d T 0 → ℝ) (c : ℝ) (ω : Omega d T 0) :
    ℝ≥0 :=
  open Classical in
  if ∃ s, s ≤ T ∧ c ≤ u s ω then min (sInf {s | s ≤ T ∧ c ≤ u s ω}) T else T

end ViscosityPPDE.Comparison


