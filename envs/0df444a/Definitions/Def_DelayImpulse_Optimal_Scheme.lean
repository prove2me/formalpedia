-- Prove2me | Definitions.Def_DelayImpulse_Optimal_Scheme
-- name    : DelayImpulse_Optimal_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:23.630989+00:00
-- url     : https://prove2.me/theorems/50674e63-3e8d-4cd7-bc36-8f553b62f052
-- title:
--   §4, pp. 5–6, (4.4)–(4.6), (4.13)–(4.14); Theorem 6.1 — the iterated Snell-envelope scheme Yⁿ, Oⁿ, its limit Y, the obstacle O, and the strategy δ*
-- statement:
--   The iterative optimal-stopping scheme of §4 and the strategy $\delta^*$ of Theorem 6.1, over the model of `DelayImpulse.Optimal.Model`.
--
--   **Indices.** An index $(\nu,\xi)$ is an $(\mathcal F_t)$-stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable random vector $\xi$. Its running reward is $e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}$, and $\mathcal T_t$ denotes the stopping times $\tau\ge t$, possibly $+\infty$.
--
--   **The scheme.** Families $Y^n_t(\nu,\xi)$, $O^n_t(\nu,\xi)$ form a scheme when, for every index, $Y^n$ and $O^n$ are adapted with continuous paths,
--   $$Y^0_t(\nu,\xi)=\mathbb E\Big[\int_t^\infty e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}\,ds\,\Big|\,\mathcal F_t\Big]\quad(4.4),$$
--   $$O^n_t(\nu,\xi)=\mathbb E\Big[\int_t^{t+\Delta} e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}ds\,\Big|\,\mathcal F_t\Big]+\max_{\beta\in U}\mathbb E\big[-e^{-r(t+\Delta)}\psi(\beta)+Y^{n-1}_{t+\Delta}(\nu,\xi+\beta)\,\big|\,\mathcal F_t\big]\quad(4.5\text{ ii}))$$
--   a.s. at each $t$, and
--   $$Y^n_t(\nu,\xi)=\operatorname*{ess\,sup}_{\tau\in\mathcal T_t}\mathbb E\Big[\int_t^\tau e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}ds+O^n_\tau(\nu,\xi)\,\Big|\,\mathcal F_t\Big]\quad(4.6).$$
--
--   **The limit.** $Y_t(\nu,\xi)=\lim_n Y^n_t(\nu,\xi)$ is defined as $\sup_n Y^n_t(\nu,\xi)$. A family $O$ is a *limit obstacle* for $Y$ if, for every index, it is adapted with right-continuous paths and equals the right-hand side of (4.14) — the formula above with $Y$ in place of $Y^{n-1}$ — a.s. at each $t$.
--
--   **The strategy $\delta^*$.** Given $Y$ and $O$, a strategy is a $\delta^*$-strategy when its times are stopping times, $P$-a.s. equal to the hitting times
--   $$\tau^*_0=\inf\{s\ge0:O_s(0,0)\ge Y_s(0,0)\},\qquad \tau^*_n=\inf\{s\ge\tau^*_{n-1}+\Delta:O_s(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})\ge Y_s(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})\}$$
--   (with $\inf\emptyset=+\infty$), each $\beta^*_n$ is $U$-valued and $\mathcal F_{\tau^*_n}$-measurable, and a.s.
--   $$O_{\tau^*_n}(\text{prev}_n)=\mathbb E\Big[\int_{\tau^*_n}^{\tau^*_n+\Delta}e^{-rs}h(s,L_s+\beta^*_0+\dots+\beta^*_{n-1})ds-e^{-r(\tau^*_n+\Delta)}\psi(\beta^*_n)+Y_{\tau^*_n+\Delta}(\tau^*_n,\beta^*_0+\dots+\beta^*_n)\,\Big|\,\mathcal F_{\tau^*_n}\Big],$$
--   where $\text{prev}_0=(0,0)$ and $\text{prev}_n=(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})$.
--
--   These are the objects the main theorem is about: $Y_0(0,0)$ is the value of the impulse control problem and $\delta^*$ an optimal strategy.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. The essential supremum is `ReflectedBSDE.Existence.IsEssSupOver` relative to $\mathcal F_t$. $\int_a^b$ for $a\le b$ in $[0,+\infty]$ is the integral over $[a,b)$, over $[a,\infty)$ if $b=+\infty$, and $0$ if $a=+\infty$. The maximum over $U$ is the pointwise maximum of the conditional expectations. Theorem 6.1 does not say that $\beta^*_0$ is $U$-valued; it is required here, as for $\beta^*_n$, $n\ge1$. The ":=" of the paper's condition on $\beta^*_0$ is read as an a.s. equation. Also defined: $\|\psi\|=\max_{\beta\in U}|\psi(\beta)|$, used in (6.27). The hitting times are taken up to a $P$-null set: Lean's $\sigma$-algebras are not complete, so the hitting time itself is only a stopping time for the completed filtration, and the statement uses a stopping time equal to it almost surely (which changes no expectation).
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, pp. 2–3 (conventions, 𝒯_t), p. 5 (4.4)–(4.5), Proposition 4.1 (4.6), p. 6 Proposition 4.2 (4.13)–(4.14), p. 14 Theorem 6.1

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Model
import Definitions.Def_ReflectedBSDE_Existence_OptimalStopping

namespace DelayImpulse.Optimal

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {l : ℕ}

/-- A real process `X` evaluated at a random time `σ` with values in `[0, +∞]`; the value at
`σ = +∞` is `0` (the paper's `y_∞ = lim_{t→∞} y_t`, which is `0` for its processes). -/
noncomputable def atTime (X : ℝ≥0 → Ω → ℝ) (σ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  match σ ω with
  | ⊤ => 0
  | (t : ℝ≥0) => X t ω

/-- `∫_a^b f(s) ds` for `a, b ∈ [0, +∞]`: the integral over `[a, b)` if `b < +∞`, over `[a, ∞)` if
`b = +∞`, and `0` if `a = +∞`. -/
noncomputable def segInt (f : ℝ → ℝ) : WithTop ℝ≥0 → WithTop ℝ≥0 → ℝ
  | ⊤, _ => 0
  | (a : ℝ≥0), ⊤ => ∫ s in Ici (a : ℝ), f s
  | (a : ℝ≥0), (b : ℝ≥0) => ∫ s in Ico (a : ℝ) b, f s

/-- The running reward of the scheme, `e^{−rs} h(s, L_s + ξ) 1[s ≥ ν]` ((4.3)–(4.6)). -/
noncomputable def run (D : Data Ω l) (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (s : ℝ)
    (ω : Ω) : ℝ :=
  if ν ω ≤ (s.toNNReal : WithTop ℝ≥0) then
    Real.exp (-D.r * s) * D.h s.toNNReal ω (D.L s.toNNReal ω + ξ ω) else 0

/-- `(ν, ξ)` is an index of the scheme (p. 5): `ν` an `𝓕`-stopping time (possibly `+∞`) and `ξ` a
finite `𝓕_ν`-random variable, `card(ξ(Ω)) < ∞`. -/
structure IsIndex (𝓕 : Filtration ℝ≥0 mΩ) (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) : Prop where
  stop : IsStoppingTime 𝓕 ν
  meas : Measurable[stop.measurableSpace] ξ
  finite : (Set.range ξ).Finite

/-- `𝒯_t` (p. 3, vi)): the `𝓕`-stopping times `τ` with `τ ≥ t`, possibly `+∞`. -/
def StopAfter (𝓕 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) : Type :=
  {τ : Ω → WithTop ℝ≥0 // IsStoppingTime 𝓕 τ ∧ ∀ ω, (t : WithTop ℝ≥0) ≤ τ ω}

/-- Stopping times after a random starting time `θ`, as in (8.54). -/
def StopAfterTime (𝓕 : Filtration ℝ≥0 mΩ) (θ : Ω → WithTop ℝ≥0) : Type :=
  {τ : Ω → WithTop ℝ≥0 // IsStoppingTime 𝓕 τ ∧ ∀ ω, θ ω ≤ τ ω}

/-- A family of real processes indexed by `(ν, ξ)`: `W ν ξ t ω = W_t(ν, ξ)(ω)`. -/
abbrev Fam (Ω : Type) (l : ℕ) : Type :=
  (Ω → WithTop ℝ≥0) → (Ω → Fin l → ℝ) → ℝ≥0 → Ω → ℝ

/-- The right-hand side of (4.5) ii) (with `W = Y^{n−1}`) and of (4.14) (with `W = Y`), at time `t`:
`E[∫_t^{t+Δ} e^{−rs} h(s, L_s + ξ) 1[s≥ν] ds | 𝓕_t]
  + max_{β∈U} E[−e^{−r(t+Δ)} ψ(β) + W_{t+Δ}(ν, ξ + β) | 𝓕_t]`. The maximum is the pointwise
maximum of the conditional expectations. -/
noncomputable def obstacleRHS (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (D : Data Ω l)
    (hU : D.U.Nonempty) (W : Fam Ω l) (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (t : ℝ≥0) :
    Ω → ℝ :=
  fun ω =>
    P[fun ω' => segInt (fun s => run D ν ξ s ω') t (t + D.Δ) | 𝓕 t] ω
    + D.U.sup' hU (fun β =>
        P[fun ω' => -(Real.exp (-D.r * ((t : ℝ) + D.Δ))) * D.ψ β
            + W ν (fun ω'' => ξ ω'' + β) (t + D.Δ) ω' | 𝓕 t] ω)

/-- The Snell-envelope identity (4.6)/(4.13) at time `t`: `Y_t` is the essential supremum over
`τ ∈ 𝒯_t` of `E[∫_t^τ e^{−rs} h(s, L_s + ξ) 1[s≥ν] ds + O_τ | 𝓕_t]`. -/
def IsSnellAt (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (D : Data Ω l) (ν : Ω → WithTop ℝ≥0)
    (ξ : Ω → Fin l → ℝ) (O : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (Yt : Ω → ℝ) : Prop :=
  ReflectedBSDE.Existence.IsEssSupOver P (𝓕 t)
    (fun τ : StopAfter 𝓕 t =>
      P[fun ω => segInt (fun s => run D ν ξ s ω) t (τ.1 ω) + atTime O τ.1 ω | 𝓕 t]) Yt

/-- The scheme (4.4)–(4.6) as a predicate on the families `(Yⁿ)ₙ` and `(Oⁿ)ₙ`, for every index
`(ν, ξ)`: `Yⁿ` adapted with continuous paths; `Y⁰` given by (4.4); `Oⁿ⁺¹` adapted with continuous
paths and a.s. equal at each `t` to the right-hand side of (4.5) ii) built from `Yⁿ`; `Yⁿ⁺¹` the
Snell envelope (4.6) of the reward with obstacle `Oⁿ⁺¹`. `On 0` is unused. -/
structure IsScheme (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (D : Data Ω l) (hU : D.U.Nonempty)
    (Yn On : ℕ → Fam Ω l) : Prop where
  Y_adapted : ∀ n ν ξ, IsIndex 𝓕 ν ξ → Adapted 𝓕 (Yn n ν ξ)
  Y_cont : ∀ n ν ξ, IsIndex 𝓕 ν ξ → ∀ ω, Continuous fun t => Yn n ν ξ t ω
  Y_zero : ∀ ν ξ, IsIndex 𝓕 ν ξ → ∀ t,
    Yn 0 ν ξ t =ᵐ[P] P[fun ω => segInt (fun s => run D ν ξ s ω) t ⊤ | 𝓕 t]
  O_adapted : ∀ n ν ξ, IsIndex 𝓕 ν ξ → Adapted 𝓕 (On (n + 1) ν ξ)
  O_cont : ∀ n ν ξ, IsIndex 𝓕 ν ξ → ∀ ω, Continuous fun t => On (n + 1) ν ξ t ω
  O_eq : ∀ n ν ξ, IsIndex 𝓕 ν ξ → ∀ t,
    On (n + 1) ν ξ t =ᵐ[P] obstacleRHS 𝓕 P D hU (Yn n) ν ξ t
  Y_snell : ∀ n ν ξ, IsIndex 𝓕 ν ξ → ∀ t,
    IsSnellAt 𝓕 P D ν ξ (On (n + 1) ν ξ) t (Yn (n + 1) ν ξ t)

/-- `Y(ν, ξ) = lim_n Yⁿ(ν, ξ)` (Proposition 4.2 i)), written as the pointwise supremum of the
sequence (which is increasing by (4.8)). -/
noncomputable def Ylim (Yn : ℕ → Fam Ω l) : Fam Ω l := fun ν ξ t ω => ⨆ n, Yn n ν ξ t ω

/-- The obstacle `O(ν, ξ)` of (4.14) for a family `Y`: for every index, adapted, with
right-continuous paths, and a.s. equal at each `t` to the right-hand side of (4.14). -/
structure IsLimitObstacle (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (D : Data Ω l)
    (hU : D.U.Nonempty) (Y O : Fam Ω l) : Prop where
  adapted : ∀ ν ξ, IsIndex 𝓕 ν ξ → Adapted 𝓕 (O ν ξ)
  rcont : ∀ ν ξ, IsIndex 𝓕 ν ξ → ∀ ω t, ContinuousWithinAt (fun s => O ν ξ s ω) (Ici t) t
  eq : ∀ ν ξ, IsIndex 𝓕 ν ξ → ∀ t, O ν ξ t =ᵐ[P] obstacleRHS 𝓕 P D hU Y ν ξ t

open Classical in
/-- The first time after `a` at which `O ≥ Y`: `inf{s ≥ a : O_s ≥ Y_s}`, and `+∞` if the set is
empty (Theorem 6.1). -/
noncomputable def firstHit (O Y : ℝ≥0 → Ω → ℝ) (a : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  if ∃ s : ℝ≥0, a ω ≤ s ∧ Y s ω ≤ O s ω
  then ((sInf {s : ℝ≥0 | a ω ≤ s ∧ Y s ω ≤ O s ω} : ℝ≥0) : WithTop ℝ≥0) else ⊤

/-- The partial sum `ξ₀ + ⋯ + ξ_{m−1}` of the impulses of a strategy (`0` for `m = 0`). -/
def psum (δ : Strategy Ω l) (m : ℕ) : Ω → Fin l → ℝ := fun ω => ∑ j ∈ Finset.range m, δ.ξ j ω

/-- The index from which decision `n` is taken: `(0, 0)` for `n = 0` and
`(τ_{n−1}, ξ₀ + ⋯ + ξ_{n−1})` for `n ≥ 1`. -/
def prevIdx (δ : Strategy Ω l) : ℕ → (Ω → WithTop ℝ≥0) × (Ω → Fin l → ℝ)
  | 0 => (fun _ => 0, fun _ => 0)
  | n + 1 => (δ.τ n, psum δ (n + 1))

/-- The strategy `δ* = (τ*ₙ, β*ₙ)` of Theorem 6.1 for given families `Y`, `O` (index 0 is the
paper's `(τ*₀, β*₀)`): `τ*₀ = inf{s ≥ 0 : O_s(0,0) ≥ Y_s(0,0)}`,
`τ*ₙ = inf{s ≥ τ*ₙ₋₁ + Δ : O_s(τ*ₙ₋₁, β*₀+⋯+β*ₙ₋₁) ≥ Y_s(τ*ₙ₋₁, β*₀+⋯+β*ₙ₋₁)}` (`+∞` if empty),
each `τ*ₙ` being a stopping time equal `P`-a.s. to that hitting time;
each `β*ₙ` is `U`-valued and `𝓕_{τ*ₙ}`-measurable with
`O_{τ*ₙ}(prev) = E[∫_{τ*ₙ}^{τ*ₙ+Δ} e^{−rs} h(s, L_s + β*₀+⋯+β*ₙ₋₁) ds − e^{−r(τ*ₙ+Δ)} ψ(β*ₙ)
  + Y_{τ*ₙ+Δ}(τ*ₙ, β*₀+⋯+β*ₙ) | 𝓕_{τ*ₙ}]` a.s. -/
structure IsStarStrategy (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (D : Data Ω l) (Y O : Fam Ω l)
    (δ : Strategy Ω l) : Prop where
  stop : ∀ n, IsStoppingTime 𝓕 (δ.τ n)
  hit_zero : δ.τ 0 =ᵐ[P] firstHit (O (fun _ => 0) (fun _ => 0)) (Y (fun _ => 0) (fun _ => 0))
    (fun _ => 0)
  hit_succ : ∀ n, δ.τ (n + 1) =ᵐ[P]
    firstHit (O (δ.τ n) (psum δ (n + 1))) (Y (δ.τ n) (psum δ (n + 1)))
      (fun ω => δ.τ n ω + (D.Δ : WithTop ℝ≥0))
  mem : ∀ n ω, δ.ξ n ω ∈ D.U
  meas : ∀ n, Measurable[(stop n).measurableSpace] (δ.ξ n)
  attain : ∀ n,
    atTime (O (prevIdx δ n).1 (prevIdx δ n).2) (δ.τ n) =ᵐ[P]
      P[fun ω => segInt (fun s => Real.exp (-D.r * s) *
                      D.h s.toNNReal ω (D.L s.toNNReal ω + psum δ n ω))
                    (δ.τ n ω) (δ.τ n ω + (D.Δ : WithTop ℝ≥0))
                 - disc D.r (δ.τ n ω + (D.Δ : WithTop ℝ≥0)) * D.ψ (δ.ξ n ω)
                 + atTime (Y (δ.τ n) (psum δ (n + 1)))
                     (fun ω' => δ.τ n ω' + (D.Δ : WithTop ℝ≥0)) ω
        | (stop n).measurableSpace]

/-- `‖ψ‖ = max_{β∈U} |ψ(β)|` (used in (6.27)). -/
noncomputable def psiNorm (D : Data Ω l) (hU : D.U.Nonempty) : ℝ := D.U.sup' hU (fun β => |D.ψ β|)

end DelayImpulse.Optimal


