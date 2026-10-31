-- Prove2me | Definitions.Def_SingularStopperVI_Game
-- name    : SingularStopperVI_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:54.04985+00:00
-- url     : https://prove2.me/theorems/59d71013-bf65-48fb-9612-c5bfa49a8965
-- title:
--   The singular controller vs. stopper game: controlled equation (3.1), cost (3.2), payoff, values (3.3), stopping rule (3.11)
-- statement:
--   The game of §3. On a stochastic basis $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$, with $\mathbb F$ right-continuous and containing the null sets and $W$ a $d'$-dimensional $\mathbb F$-Brownian motion, fix $T>0$, $r\ge0$ and $t\in[0,T]$.
--
--   The stopper chooses $\tau\in\mathcal T_t$, a stopping time with $\tau\le T-t$ a.s. The controller chooses $(n,\nu)\in\mathcal A_t$: $n$ is progressive with $|n_s|_d=1$, $\nu$ is adapted, non-decreasing and right-continuous with $\nu_{0-}=0$ and $\mathsf E[\nu_{T-t}^2]<\infty$. The state solves
--
--   $$
--   X_s=x+\int_0^s b(X_u)\,du+\int_0^s\sigma(X_u)\,dW_u+\int_{[0,s]}n_u\,d\nu_u .
--   $$
--
--   The payoff is
--
--   $$
--   J_{t,x}(n,\nu,\tau)=\mathsf E_x\Big[e^{-r\tau}g(t+\tau,X_\tau)+\int_0^\tau e^{-rs}h(t+s,X_s)\,ds+\int_{[0,\tau]}e^{-rs}f(t+s,X_s)\circ d\nu_s\Big],
--   $$
--
--   where the cost (3.2) is
--
--   $$
--   \int_0^\tau e^{-rs}f(t+s,X_s)\,d\nu^c_s+\sum_{0\le s\le\tau}e^{-rs}\int_0^{\Delta\nu_s}f(t+s,X_{s-}+\lambda n_s)\,d\lambda .
--   $$
--
--   The lower and upper values are $\sup_\tau\inf_{(n,\nu)}J$ and $\inf_{(n,\nu)}\sup_\tau J$. The candidate optimal time is $\tau_*=\inf\{s\ge0\mid v(t+s,X_s)=g(t+s,X_s)\}\wedge(T-t)$.
--
--   The module also holds the generator $\mathcal L$ of p.6, with $a=\sigma\sigma^\top$.
--
--   **Formalization Note** Payoffs and values lie in $[0,\infty]$, as $J$ can be $+\infty$. The path of $\nu$ is extended by $0$ to negative times, and its Stieltjes measure then carries the jump $\nu_0$ at time $0$; the state is extended by $x$, so $X_{0-}=x$. The measure $d\nu^c$ is $d\nu$ on the times without a jump. Infima run over triples $(n,\nu,X)$. The Itô integral is the local one, given by dyadic bounded predictable approximation in probability, so no global $L^2$ condition enters.
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, §3, (3.1)–(3.3), (3.11), pp.5–7

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_SingularStopperVI_FunctionClasses

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularStopperVI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d d' : ℕ}

/-- The stochastic data of §3, p.5: a measure `P`, a filtration `𝔽 = (ℱ_s)_{s ≥ 0}` and a
`d'`-dimensional process `W`. -/
structure Basis (d' : ℕ) (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  /-- the probability measure -/
  P : Measure Ω
  /-- the filtration -/
  F : Filtration ℝ≥0 mΩ
  /-- the Brownian motion -/
  W : ℝ≥0 → Ω → Fin d' → ℝ

/-- The standing setting of §3, p.5: `P` is a probability measure, `𝔽` is right-continuous and
completed by the `P`-null sets, and `W` is a `d'`-dimensional `𝔽`-Brownian motion.

**Formalization Note** `ℱ_0` containing the `P`-null sets makes `P` complete, so that hypothesis of
the page is not repeated. "`𝔽`-adapted Brownian motion" is read as `𝔽`-Brownian motion: increments
after `s` are independent of `ℱ_s`, without which the Itô integral in (3.1) is not defined. -/
structure Basis.IsValid (B : Basis d' Ω) : Prop where
  prob : IsProbabilityMeasure B.P
  usual : You2015.Shared.UsualConditions B.P B.F
  brownian : You2015.Shared.IsFBrownian B.P B.F B.W

/-- The data of the game: horizon `T`, discount rate `r`, coefficients `b`, `σ` of (3.1), and the
payoff functions `f`, `g`, `h`. arXiv:2203.06247v3, §3, p.5. -/
structure Data (d d' : ℕ) where
  /-- the horizon -/
  T : ℝ
  /-- the discount rate -/
  r : ℝ
  /-- the drift -/
  b : Euc d → Euc d
  /-- the diffusion matrix -/
  σ : Euc d → Matrix (Fin d) (Fin d') ℝ
  /-- the cost per unit of control -/
  f : ℝ → Euc d → ℝ
  /-- the stopping payoff -/
  g : ℝ → Euc d → ℝ
  /-- the running payoff -/
  h : ℝ → Euc d → ℝ

/-- The standing conventions of §2–§3 (pp.3, 5): `d, d' ∈ ℕ`, `d ≤ d'`, `T ∈ (0,∞)`, `r ≥ 0`. -/
structure Data.Standing (D : Data d d') : Prop where
  d_pos : 0 < d
  d_le : d ≤ d'
  T_pos : 0 < D.T
  r_nonneg : 0 ≤ D.r

/-- The remaining time `T − t`, as an index of the filtration. -/
noncomputable def horizon (D : Data d d') (t : ℝ) : ℝ≥0 := (D.T - t).toNNReal

/-- `a = σσ^⊤`, p.6. -/
noncomputable def diffusionMatrix (D : Data d d') (x : Euc d) : Matrix (Fin d) (Fin d) ℝ :=
  D.σ x * (D.σ x).transpose

/-- The generator of p.6 at `x`, on a gradient `p` and a Hessian `A`:
`½ tr(a(x) A) + ⟨b(x), p⟩`. -/
noncomputable def generator (D : Data d d') (x p : Euc d) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (1 / 2) * Matrix.trace (diffusionMatrix D x * A) + inner ℝ (D.b x) p

/-- `∂_t u + Lu − ru` at `(t,x)`, with the derivatives `K`. -/
noncomputable def pdeOperator (D : Data d d') (u : ℝ → Euc d → ℝ) (K : Jet d) (t : ℝ)
    (x : Euc d) : ℝ :=
  K.ut t x + generator D x (K.Du t x) (K.D2u t x) - D.r * u t x

/-- Progressive measurability of `H` up to the time `S`. -/
def ProgressiveOn {β : Type*} [MeasurableSpace β] (F : Filtration ℝ≥0 mΩ) (S : ℝ≥0)
    (H : ℝ≥0 → Ω → β) : Prop :=
  ∀ s ≤ S, Measurable[Subtype.instMeasurableSpace.prod (F s)]
    (fun p : Iic s × Ω => H p.1 p.2)

/-- The dyadic step process on `(0,s]` with values `a k` on `(ks/2ⁿ, (k+1)s/2ⁿ]`. -/
noncomputable def stepValue (s : ℝ≥0) (n : ℕ) (a : ℕ → Ω → ℝ) (z : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), if z ∈ Ioc (s * k / 2 ^ n) (s * (k + 1) / 2 ^ n) then a k ω else 0

/-- The elementary stochastic integral of that step process against `W`. -/
noncomputable def stepSum (W : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (n : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), a k ω * (W (s * (k + 1) / 2 ^ n) ω - W (s * k / 2 ^ n) ω)

/-- `J_s = ∫_0^s H dW` for `s ≤ S`, the local Itô integral: `H` is progressive with
`∫_0^S H² < ∞` almost surely, `J` is adapted and a.s. continuous, and for each `s ≤ S` there are
bounded predictable dyadic step processes whose integrated squared error tends to `0` in
probability and whose elementary integrals tend to `J_s` in probability. -/
def IsItoIntegral (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (S : ℝ≥0)
    (H J : ℝ≥0 → Ω → ℝ) : Prop :=
  ProgressiveOn F S H ∧
  (∀ᵐ ω ∂P, ∫⁻ z in Icc (0 : ℝ) S, ENNReal.ofReal (H z.toNNReal ω ^ 2) < ⊤) ∧
  (∀ s ≤ S, Measurable[F s] (J s)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => J s ω) (Icc 0 S)) ∧
  ∀ s ≤ S, ∃ a : ℕ → ℕ → Ω → ℝ,
    (∀ n k : ℕ, k < 2 ^ n → Measurable[F (s * (k : ℝ≥0) / 2 ^ n)] (a n k)) ∧
    (∀ n, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ n → ∀ ω, |a n k ω| ≤ C) ∧
    TendstoInMeasure P
      (fun n ω => ∫ z in Icc (0 : ℝ) s, (stepValue s n (a n) z.toNNReal ω - H z.toNNReal ω) ^ 2)
      atTop (fun _ => (0 : ℝ)) ∧
    TendstoInMeasure P (fun n => stepSum W s n (a n)) atTop (J s)

/-- `τ ∈ 𝒯_t`, p.5, with `S = T − t`: a stopping time with `τ ≤ S` almost surely. -/
def IsStoppingRule (B : Basis d' Ω) (S : ℝ≥0) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime B.F (fun ω => (τ ω : WithTop ℝ≥0)) ∧ ∀ᵐ ω ∂B.P, τ ω ≤ S

/-- `(n,ν) ∈ 𝒜_t`, p.5, with `S = T − t`: `n` is progressive with `|n_s|_d = 1` for all `s`,
almost surely; `ν` is adapted, a.s. non-negative, non-decreasing and right-continuous; and
`E[ν_S²] < ∞`.

**Formalization Note** "`|n_s|_d = 1`, P-a.s. for all `s`" is read `∀ᵐ ω, ∀ s`. Non-negativity of `ν`
is `ν_{0−} = 0` with monotonicity; the mass `ν_0` at time `0` is in `stMeas`. -/
structure IsControl (B : Basis d' Ω) (S : ℝ≥0) (n : ℝ≥0 → Ω → Euc d) (ν : ℝ≥0 → Ω → ℝ) :
    Prop where
  prog : IsProgressive B.F n
  unit : ∀ᵐ ω ∂B.P, ∀ s, ‖n s ω‖ = 1
  adapted : ∀ s, Measurable[B.F s] (ν s)
  path : ∀ᵐ ω ∂B.P, (∀ s, 0 ≤ ν s ω) ∧ Monotone (fun s => ν s ω) ∧
    ∀ s, ContinuousWithinAt (fun s => ν s ω) (Ici s) s
  square : ∫⁻ ω, ENNReal.ofReal (ν S ω ^ 2) ∂B.P < ⊤

/-- The path of `ν` on `ℝ`, with value `0` at negative times: this is `ν_{0−} = 0`. -/
noncomputable def extPath (ν : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun s => if s < 0 then 0 else ν s.toNNReal ω

open Classical in
/-- The Lebesgue–Stieltjes measure `dν(ω)` of `extPath`, which charges `{0}` with the jump `ν_0(ω)`.
It is the zero measure on the null set of non-monotone paths. -/
noncomputable def stMeas (ν : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  if h : Monotone (extPath ν ω) then h.stieltjesFunction.measure else 0

/-- The jump `Δν_s = ν_s − ν_{s−}`, with `ν_{0−} = 0`. -/
noncomputable def jump (ν : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  extPath ν ω s - Function.leftLim (extPath ν ω) s

/-- `dν^c`, the part of `dν` without atoms, which is `dν` on the times where `ν` does not jump. -/
noncomputable def contPart (ν : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  (stMeas ν ω).restrict {s | jump ν ω s = 0}

/-- The path of `X` on `ℝ`, with value `x` at negative times: this is `X_{0−} = x`. -/
noncomputable def extState (x : Euc d) (X : ℝ≥0 → Ω → Euc d) (ω : Ω) : ℝ → Euc d :=
  fun s => if s < 0 then x else X s.toNNReal ω

/-- The left limit `X_{s−}`, with `X_{0−} = x`. -/
noncomputable def leftState (x : Euc d) (X : ℝ≥0 → Ω → Euc d) (ω : Ω) (s : ℝ) : Euc d :=
  Function.leftLim (extState x X ω) s

/-- A path that is right-continuous with left limits on `[0,S]`. -/
def IsCadlagOn (S : ℝ≥0) (path : ℝ≥0 → Euc d) : Prop :=
  (∀ s ≤ S, ContinuousWithinAt path (Icc s S) s) ∧
    ∀ s ∈ Ioc 0 S, ∃ l, Tendsto path (𝓝[<] s) (𝓝 l)

/-- The vector with coordinates `i ↦ Σ_j M i j s ω`: coordinatewise, `∫_0^s σ dW`. -/
noncomputable def itoVector (M : Fin d → Fin d' → ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : Euc d :=
  WithLp.toLp 2 (fun i => ∑ j, M i j s ω)

/-- `X` solves the controlled equation (3.1), p.5, from `x` on `[0,S]`, `S = T − t`:
`X_s = x + ∫_0^s b(X_u) du + ∫_0^s σ(X_u) dW_u + ∫_{[0,s]} n_u dν_u`, with `X` adapted and a.s. càdlàg.
The last integral is over the Stieltjes measure `stMeas`, so it contains the jump at time `0`. -/
structure IsStateSol (B : Basis d' Ω) (D : Data d d') (S : ℝ≥0) (x : Euc d)
    (n : ℝ≥0 → Ω → Euc d) (ν : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) : Prop where
  adapted : ∀ s ≤ S, Measurable[B.F s] (X s)
  cadlag : ∀ᵐ ω ∂B.P, IsCadlagOn S (fun s => X s ω)
  equation : ∃ M : Fin d → Fin d' → ℝ≥0 → Ω → ℝ,
    (∀ i j, IsItoIntegral B.P B.F (fun s ω => B.W s ω j) S
      (fun s ω => D.σ (X s ω) i j) (M i j)) ∧
    ∀ᵐ ω ∂B.P, ∀ s ≤ S,
      X s ω = x + (∫ u in Icc (0 : ℝ) s, D.b (X u.toNNReal ω)) + itoVector M s ω +
        ∫ u in Icc (0 : ℝ) s, n u.toNNReal ω ∂(stMeas ν ω)

/-- The cost (3.2), p.5, on `[0,τ]`, at one `ω`:
`∫_0^τ e^{−rs} f(t+s,X_s) dν^c_s + Σ_{0≤s≤τ} e^{−rs} ∫_0^{Δν_s} f(t+s, X_{s−} + λ n_s) dλ`, in `[0,∞]`.
The sum runs over the jump times, including `s = 0` and `s = τ`.

**Formalization Note** It is not the Stieltjes integral of `f(t+s,X_s)` against `dν`, unless `f`
does not depend on the state (p.5). -/
noncomputable def controlCost (D : Data d d') (t : ℝ) (x : Euc d) (n : ℝ≥0 → Ω → Euc d)
    (ν : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) (τ : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (∫⁻ s in Icc (0 : ℝ) τ,
      ENNReal.ofReal (Real.exp (-D.r * s) * D.f (t + s) (X s.toNNReal ω)) ∂(contPart ν ω)) +
    ∑' s : {s : ℝ // s ∈ Icc (0 : ℝ) τ ∧ 0 < jump ν ω s},
      ENNReal.ofReal (Real.exp (-D.r * s)) *
        ∫⁻ l in Ioc (0 : ℝ) (jump ν ω s),
          ENNReal.ofReal (D.f (t + s) (leftState x X ω s + l • n (s : ℝ).toNNReal ω))

/-- The expected payoff `J_{t,x}(n,ν,τ)` of p.5, along the solution `X`, in `[0,∞]`:
`E[e^{−rτ} g(t+τ,X_τ) + ∫_0^τ e^{−rs} h(t+s,X_s) ds + ∫_{[0,τ]} e^{−rs} f(t+s,X_s) ∘ dν_s]`.

**Formalization Note** The value `+∞` occurs: `f` has polynomial growth of any degree and `ν` only a
second moment, so a real Bochner integral would return `0` there. -/
noncomputable def payoff (B : Basis d' Ω) (D : Data d d') (t : ℝ) (x : Euc d)
    (n : ℝ≥0 → Ω → Euc d) (ν : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) (τ : Ω → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω,
    (ENNReal.ofReal (Real.exp (-D.r * τ ω) * D.g (t + τ ω) (X (τ ω) ω)) +
      (∫⁻ s in Icc (0 : ℝ) (τ ω),
        ENNReal.ofReal (Real.exp (-D.r * s) * D.h (t + s) (X s.toNNReal ω))) +
      controlCost D t x n ν X (τ ω) ω) ∂B.P

/-- The admissible `(n,ν) ∈ 𝒜_t` together with a solution `X` of (3.1) from `x`. By the well-posedness
of (3.1), `X` is determined by `(n,ν)` up to indistinguishability. -/
abbrev ControlledState (B : Basis d' Ω) (D : Data d d') (t : ℝ) (x : Euc d) :=
  {c : (ℝ≥0 → Ω → Euc d) × (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → Euc d) //
    IsControl B (horizon D t) c.1 c.2.1 ∧ IsStateSol B D (horizon D t) x c.1 c.2.1 c.2.2}

/-- The class `𝒯_t`. -/
abbrev StoppingRule (B : Basis d' Ω) (D : Data d d') (t : ℝ) :=
  {τ : Ω → ℝ≥0 // IsStoppingRule B (horizon D t) τ}

/-- The payoff of a controlled state against a stopping time. -/
noncomputable def ControlledState.payoff {B : Basis d' Ω} {D : Data d d'} {t : ℝ} {x : Euc d}
    (c : ControlledState B D t x) (τ : Ω → ℝ≥0) : ℝ≥0∞ :=
  SingularStopperVI.payoff B D t x c.1.1 c.1.2.1 c.1.2.2 τ

/-- The lower value `sup_{τ ∈ 𝒯_t} inf_{(n,ν) ∈ 𝒜_t} J_{t,x}(n,ν,τ)`, (3.3), p.6, in `[0,∞]`. -/
noncomputable def lowerValue (B : Basis d' Ω) (D : Data d d') (t : ℝ) (x : Euc d) : ℝ≥0∞ :=
  ⨆ τ : StoppingRule B D t, ⨅ c : ControlledState B D t x, c.payoff τ.1

/-- The upper value `inf_{(n,ν) ∈ 𝒜_t} sup_{τ ∈ 𝒯_t} J_{t,x}(n,ν,τ)`, (3.3), p.6, in `[0,∞]`. -/
noncomputable def upperValue (B : Basis d' Ω) (D : Data d d') (t : ℝ) (x : Euc d) : ℝ≥0∞ :=
  ⨅ c : ControlledState B D t x, ⨆ τ : StoppingRule B D t, c.payoff τ.1

/-- The value function `v(t,x)`: the real number of `lowerValue`. Theorem 3.3 shows that this
`[0,∞]`-valued quantity is finite, so `toReal` loses nothing. -/
noncomputable def valueFn (B : Basis d' Ω) (D : Data d d') (t : ℝ) (x : Euc d) : ℝ :=
  (lowerValue B D t x).toReal

/-- The stopping rule (3.11), p.7, for a candidate value `v`, along `X`:
`τ_* = inf{s ≥ 0 | v(t+s,X_s) = g(t+s,X_s)} ∧ (T−t)`.

**Formalization Note** The set is restricted to `[0,T−t]`, where `v` and `g` are defined, which the
`∧ (T−t)` makes equivalent, and it contains `T−t` so that the infimum of an empty set does not occur. -/
noncomputable def tauStar (D : Data d d') (v : ℝ → Euc d → ℝ) (t : ℝ) (X : ℝ≥0 → Ω → Euc d)
    (ω : Ω) : ℝ≥0 :=
  sInf ({s : ℝ≥0 | s ≤ horizon D t ∧ v (t + s) (X s ω) = D.g (t + s) (X s ω)} ∪ {horizon D t})

end SingularStopperVI


