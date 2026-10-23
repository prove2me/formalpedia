-- Prove2me | Definitions.Def_CTJMDP_MarkovSuff_Setting
-- name    : CTJMDP_MarkovSuff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:03.653429+00:00
-- url     : https://prove2.me/theorems/a72065b0-b521-495b-956c-e3cce7833e90
-- title:
--   §§2–5, (2)–(16), (23)–(37), Assumption 2.1, Definitions 1–2, pp. 3–13 — CTJMDP, policies, law of the jump process, marginals, jump counts, forward equation
-- statement:
--   This file sets up a **continuous-time jump Markov decision process** (CTJMDP) $\{X, A, A(\cdot), \tilde q\}$ and the objects of Feinberg, Mandava and Shiryaev's sufficiency theorem.
--
--   1. **Model.** $X$ (states) and $A$ (actions) are standard Borel spaces; $A(x)\subseteq A$ is the set of actions available at $x$; the set $\mathrm{Gr}(A)=\{(x,a): a\in A(x)\}$ is measurable and contains the graph of a measurable selector. For $(x,a)\in \mathrm{Gr}(A)$ the transition rate is given by its off-diagonal part, a finite measure $Z\mapsto \tilde q(x,a,Z\setminus\{x\})$, measurable in $(x,a)$; the jump intensity is $\tilde q(x,a)=\tilde q(x,a,X\setminus\{x\})$, and $\tilde q:=0$ off $\mathrm{Gr}(A)$. **Assumption 2.1** requires $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x$. For a probability measure $p$ on $A$, the relaxed quantities are $\tilde q(z,p)=\int \tilde q(z,a)\,p(da)$ and $\tilde q(z,p,Z\setminus\{z\})=\int \tilde q(z,a,Z\setminus\{z\})\,p(da)$, (4)–(5).
--
--   2. **Trajectories and policies.** A trajectory is $\omega=(x_0,t_1,x_1,t_2,x_2,\dots)$ with jump epochs $t_n\in(0,\infty]$, $t_0=0$. A **policy** is a sequence of transition probabilities $\pi_n(\cdot\mid x_0,t_1,\dots,t_n,x_n,s)$, $s=t-t_n>0$, concentrated on $A(x_n)$, as in (2). A **Markov policy** is a transition probability $\phi(\cdot\mid z,t)$ from $X\times\mathbb R_+$ to $A$ with $\phi(A(z)\mid z,t)=1$; it acts as $\pi_n(\cdot\mid\dots,x_n,s)=\phi(\cdot\mid x_n,t_n+s)$.
--
--   3. **Law of the process.** For an initial distribution $\gamma$, the law $\mathbb P^\pi_\gamma$ is the probability measure on trajectories with $x_0\sim\gamma$ such that, given the history up to the $n$th jump with $t_n<\infty$, $x=x_n$ and $\Lambda(s)=\tilde q(x,\pi_n(\cdot\mid\dots,s))$, the next jump occurs at $t_n+s$ into $dy$ with density $e^{-\int_0^s\Lambda}\,\tilde q(x,\pi_n(\cdot\mid\dots,s),dy\setminus\{x\})$, and with the remaining probability $e^{-\int_0^\infty\Lambda}$ there is no further jump. This is the explicit construction (75)–(76) of the measure that Jacod's theorem associates with the compensator $\nu^\pi$ of (9).
--
--   4. **Marginals.** $P^\pi_\gamma(t,Z)=\mathbb P^\pi_\gamma(\xi_{t-}\in Z)$ and $P^\pi_\gamma(t,Z,B)=\mathbb E^\pi_\gamma[I\{\xi_{t-}\in Z\}\pi(B\mid\omega,t)]$, (11)–(14); a Markov policy $\phi$ satisfies **(16)** for $(\gamma,\pi)$ if
--   $$P^\pi_\gamma(t,Z,B)=\int_Z \phi(B\mid z,t)\,P^\pi_\gamma(t,dz),\qquad t>0,\ Z\in\mathfrak B(X),\ B\in\mathfrak B(A).$$
--
--   5. **Jump counts and compensators.** The expected numbers of jumps into and out of $Z$ by time $t$, $\mathbb E\mu([0,t],Z)$ and $\mathbb E\tilde\mu([0,t],Z)$ of (7) and (36), and the expected cumulative intensities $\mathbb E\nu^\pi([0,t],Z)$ and $\mathbb E\tilde\nu^\pi([0,t],Z)$ of (9) and (35), also at a random time $T$ in place of $t$; the process $\xi_s=x_n$ for $t_n\le s<t_{n+1}$ of (1), its natural filtration $\mathscr F_t=\sigma(\xi_s:0\le s\le t)$ (p. 4) and stopping times with values in $\mathbb R_+$; Definition 2 of an $(x,\pi)$-bounded set.
--
--   6. **Forward equation.** For a Q-function $q(z,t,\cdot)$ (p. 8), the class $\mathcal Y$ of $q$-bounded sets (29), Definition 1 of a solution of Kolmogorov's forward equation (30), Feller's series $\bar P^{(n)}(u,x;t,Z)$ and $\bar P(u,x;t,Z)=\sum_n\bar P^{(n)}(u,x;t,Z)$ of (25)–(27), and, for a Markov policy $\phi$, the Q-function $\tilde q(z,\phi_t,\cdot)$, the class $\mathcal Y^\phi$ (33) and equation (32).
--
--   These are the shared objects of every statement in the mission.
--
--   **Formalization Note** All quantities take values in $[0,\infty]$. A trajectory is `X × (ℕ → ℝ≥0∞ × X)`; the cemetery $x_\infty$ is not a separate point: $x_n$ is ignored when $t_n=\infty$. Marginals use the left limit $\xi_{t-}$, which agrees with $\xi_t$ almost surely at each fixed $t$ by (10). The survival factor $e^{-I}$ is set to $0$ when $I=\infty$. Kolmogorov's equation is written additively, $Q(t,Z)+\int_0^t\!\int_Z q\,dQ\,ds=\delta_x(Z)+\int_0^t\!\int_X q(z,s,Z\setminus\{z\})\,Q(s,dz)\,ds$, with the subtracted term finite, which is equivalent to the real equation; a solution's measures are finite (the paper's solutions are real valued). Measurability of policies and Q-functions is required for $s,t>0$ only.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, pp. 3–13, §§2–5, (2)–(16), (23)–(37), Assumption 2.1, Definitions 1–2; explicit kernel (75)–(76), p. 20

import Mathlib

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ### The model (§2, p. 3, items (i)–(iv), Assumption 2.1) -/

/-- The primitives of a CTJMDP `{X, A, A(·), q̃}`: the action sets `A(x)` and, for each pair `(x, a)`,
the off-diagonal jump measure `Z ↦ q̃(x, a, Z \ {x})`. -/
structure Model (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the set `A(x)` of actions available at `x` -/
  Aset : X → Set A
  /-- the jump measure `Z ↦ q̃(x, a, Z \ {x})` -/
  qJ : X → A → Measure X

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- The jump measure with the paper's convention `q̃(x, a, ·) := 0` for `(x, a) ∉ Gr(A)` (p. 5). -/
def Model.jumpM (M : Model X A) (x : X) (a : A) : Measure X :=
  open Classical in if a ∈ M.Aset x then M.qJ x a else 0

/-- The jump rate `q̃(x, a) = q̃(x, a, X \ {x})`, and `0` off `Gr(A)`. -/
def Model.rate (M : Model X A) (x : X) (a : A) : ℝ≥0∞ :=
  M.jumpM x a univ

/-- The standing assumptions (iii)–(iv) of §2, p. 3: `Gr(A)` is measurable and contains the graph of a
measurable selector; each `q̃(x, a, · \ {x})` is a finite measure not charging `{x}`; and
`(x, a) ↦ q̃(x, a, Z)` is measurable on `Gr(A)` (stated for the extension by `0` off `Gr(A)`). -/
structure Model.Standing (M : Model X A) : Prop where
  graph_measurable : MeasurableSet {p : X × A | p.2 ∈ M.Aset p.1}
  selector : ∃ f : X → A, Measurable f ∧ ∀ x, f x ∈ M.Aset x
  finite : ∀ x, ∀ a ∈ M.Aset x, IsFiniteMeasure (M.qJ x a)
  no_self : ∀ x, ∀ a ∈ M.Aset x, M.qJ x a {x} = 0
  measurable : ∀ Z : Set X, MeasurableSet Z → Measurable (fun p : X × A => M.jumpM p.1 p.2 Z)

/-- Assumption 2.1: `q̄(x) = sup_{a ∈ A(x)} q̃(x, a) < ∞` for every `x`. -/
def Model.Assumption21 (M : Model X A) : Prop :=
  ∀ x, (⨆ a ∈ M.Aset x, M.rate x a) < ⊤

/-- (5): the relaxed rate `q̃(z, p) = ∫ q̃(z, a) p(da)`. -/
def rateP (M : Model X A) (z : X) (p : Measure A) : ℝ≥0∞ :=
  ∫⁻ a, M.rate z a ∂p

/-- (4): the relaxed jump measure `Z ↦ q̃(z, p, Z \ {z}) = ∫ q̃(z, a, Z \ {z}) p(da)`. -/
def jumpP (M : Model X A) (z : X) (p : Measure A) : Measure X :=
  p.bind (fun a => M.jumpM z a)

/-! ### Trajectories (p. 4) -/

/-- A trajectory `ω = (x₀, t₁, x₁, t₂, x₂, …)`; the cemetery `x_∞` is not a separate point: `x_n` is
ignored when `t_n = ∞`. -/
abbrev Traj (X : Type*) := X × (ℕ → ℝ≥0∞ × X)

/-- The jump epochs `t₀ = 0, t₁, t₂, …`. -/
def tn (ω : Traj X) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => (ω.2 n).1

/-- The post-jump states `x₀, x₁, x₂, …`. -/
def xn (ω : Traj X) : ℕ → X
  | 0 => ω.1
  | n + 1 => (ω.2 n).2

/-- The history `(x₀, t₁, x₁, …, t_n, x_n)` up to the `n`th jump. -/
def hist (n : ℕ) (ω : Traj X) : X × (Fin n → ℝ≥0∞ × X) :=
  (ω.1, fun i => ω.2 i)

/-- `ξ_{t−}(ω) = x_n(ω)`, i.e. `t_n < t ≤ t_{n+1}`. -/
def inInt (ω : Traj X) (n : ℕ) (t : ℝ) : Prop :=
  tn ω n < ENNReal.ofReal t ∧ ENNReal.ofReal t ≤ tn ω (n + 1)

/-! ### Policies (p. 4, (2)) -/

/-- A policy as its sequence of transition probabilities: `π n ω s = π_n(· | x₀, t₁, …, t_n, x_n, s)`,
used at `s = t − t_n > 0`. -/
abbrev Policy (X A : Type*) [MeasurableSpace A] := ℕ → Traj X → ℝ → Measure A

/-- `π` is a policy: each `π_n(· | h, s)` (`s > 0`) is a probability measure concentrated on
`A(x_n)`, depends only on the history up to the `n`th jump, and is measurable in `(ω, s)`. -/
structure IsPolicy (M : Model X A) (π : Policy X A) : Prop where
  prob : ∀ n ω s, 0 < s → IsProbabilityMeasure (π n ω s)
  feasible : ∀ n ω s, 0 < s → π n ω s (M.Aset (xn ω n))ᶜ = 0
  nonanticipating : ∀ n (ω ω' : Traj X), (∀ k ≤ n, tn ω k = tn ω' k ∧ xn ω k = xn ω' k) →
    π n ω = π n ω'
  measurable : ∀ n (B : Set A), MeasurableSet B →
    Measurable (fun p : Traj X × Ioi (0 : ℝ) => π n p.1 p.2 B)

/-- A Markov policy `ϕ(· | z, t)`: a transition probability from `X × ℝ₊` to `A` with
`ϕ(A(z) | z, t) = 1`. -/
structure IsMarkovPolicy (M : Model X A) (phi : X → ℝ → Measure A) : Prop where
  prob : ∀ z t, 0 < t → IsProbabilityMeasure (phi z t)
  feasible : ∀ z t, 0 < t → phi z t (M.Aset z)ᶜ = 0
  measurable : ∀ B : Set A, MeasurableSet B →
    Measurable (fun p : X × Ioi (0 : ℝ) => phi p.1 p.2 B)

/-- The policy induced by a Markov policy: `π_n(· | x₀, …, t_n, x_n, s) = ϕ(· | x_n, t_n + s)`. -/
def markovPol (phi : X → ℝ → Measure A) : Policy X A :=
  fun n ω s => phi (xn ω n) ((tn ω n).toReal + s)

/-! ### The law `ℙ^π_γ` of the jump process (p. 5; explicit kernel (75)–(76), p. 20) -/

/-- Survival factor `e^{−I}`, equal to `0` when `I = ∞`. -/
def surv (I : ℝ≥0∞) : ℝ≥0∞ :=
  if I = ⊤ then 0 else ENNReal.ofReal (Real.exp (-I.toReal))

/-- The conditional law of `(t_{n+1}, x_{n+1})` given the history up to the `n`th jump, evaluated at
`C`: with `x = x_n` and `Λ(s) = q̃(x, π_n(· | h, s))`, the jump happens at `t_n + s` into `dy` with density
`e^{−∫_0^s Λ} q̃(x, π_n(·|h, s), dy \ {x})`, and with the remaining mass `e^{−∫_0^∞ Λ}` there is no
further jump (`t_{n+1} = ∞`). If `t_n = ∞`, then `t_{n+1} = ∞`. -/
def jumpMass (M : Model X A) (π : Policy X A) (n : ℕ) (ω : Traj X) (C : Set (ℝ≥0∞ × X)) : ℝ≥0∞ :=
  if tn ω n = ⊤ then Measure.dirac (⊤, xn ω n) C
  else
    (∫⁻ s in Ioi (0 : ℝ),
        surv (∫⁻ r in Ioc (0 : ℝ) s, rateP M (xn ω n) (π n ω r)) *
          ∫⁻ y, C.indicator (fun _ => (1 : ℝ≥0∞)) (tn ω n + ENNReal.ofReal s, y)
            ∂(jumpP M (xn ω n) (π n ω s))) +
      surv (∫⁻ r in Ioi (0 : ℝ), rateP M (xn ω n) (π n ω r)) *
        C.indicator (fun _ => (1 : ℝ≥0∞)) (⊤, xn ω n)

/-- `P` is the law `ℙ^π_γ` of the jump process defined by the initial distribution `γ` and the
policy `π`: a probability measure on trajectories with `x₀ ∼ γ` whose one-step conditional laws are
`jumpMass`. -/
structure IsLaw (M : Model X A) (gam : Measure X) (π : Policy X A) (P : Measure (Traj X)) : Prop where
  prob : IsProbabilityMeasure P
  init : ∀ Z : Set X, MeasurableSet Z → P {ω | ω.1 ∈ Z} = gam Z
  step : ∀ (n : ℕ) (S : Set (X × (Fin n → ℝ≥0∞ × X))) (C : Set (ℝ≥0∞ × X)),
    MeasurableSet S → MeasurableSet C →
      P {ω | hist n ω ∈ S ∧ ω.2 n ∈ C} = ∫⁻ ω in {ω | hist n ω ∈ S}, jumpMass M π n ω C ∂P

/-! ### Marginals and expectations along the path ((11)–(16)) -/

/-- (11): `P^π_γ(t, ·) = ℙ(ξ_{t−} ∈ ·)` restricted to `X`. -/
def stateMarg (P : Measure (Traj X)) (t : ℝ) : Measure X :=
  Measure.sum fun n => (P.restrict {ω | inInt ω n t}).map (fun ω => xn ω n)

/-- `𝔼[h(ξ_{t−}, π_t) I{ξ_{t−} ∈ X}]` for `h : X → 𝒫(A) → [0, ∞]`. -/
def expAt (P : Measure (Traj X)) (π : Policy X A) (t : ℝ) (h : X → Measure A → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n, ∫⁻ ω in {ω | inInt ω n t}, h (xn ω n) (π n ω (t - (tn ω n).toReal)) ∂P

/-- `𝔼 ∫_0^{T} h(ξ_s, π_s) I{ξ_s ∈ X} ds` for a random time `T`. -/
def expPathAt (P : Measure (Traj X)) (π : Policy X A) (T : Traj X → ℝ)
    (h : X → Measure A → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' n, ∫⁻ s in {s : ℝ | 0 < s ∧ s ≤ T ω ∧ inInt ω n s},
    h (xn ω n) (π n ω (s - (tn ω n).toReal)) ∂volume ∂P

/-- `𝔼 ∫_0^t h(ξ_s, π_s) I{ξ_s ∈ X} ds`. -/
def expPath (P : Measure (Traj X)) (π : Policy X A) (t : ℝ) (h : X → Measure A → ℝ≥0∞) : ℝ≥0∞ :=
  expPathAt P π (fun _ => t) h

/-- (12)/(14): `P^π_γ(t, Z, B) = 𝔼[I{ξ_{t−} ∈ Z} π(B | ω, t)]`. -/
def saMarg (P : Measure (Traj X)) (π : Policy X A) (t : ℝ) (Z : Set X) (B : Set A) : ℝ≥0∞ :=
  expAt P π t (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * p B)

/-- `Z ↦ P^π_γ(t, Z, B)` as a measure on `X`. -/
def saMargMeas (P : Measure (Traj X)) (π : Policy X A) (t : ℝ) (B : Set A) : Measure X :=
  Measure.sum fun n =>
    ((P.restrict {ω | inInt ω n t}).withDensity
      (fun ω => π n ω (t - (tn ω n).toReal) B)).map (fun ω => xn ω n)

/-- (16): `P^π_γ(t, Z, B) = ∫_Z ϕ(B | z, t) P^π_γ(t, dz)` for all `t > 0` and measurable `Z`, `B`. -/
def Disintegrates (P : Measure (Traj X)) (π : Policy X A) (phi : X → ℝ → Measure A) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
    saMarg P π t Z B = ∫⁻ z in Z, phi z t B ∂(stateMarg P t)

/-! ### Jump counts and their compensators ((7), (8), (9), (35), (36), Definition 2) -/

/-- `ξ_s(ω) ∈ Z` for `s ≥ 0`, by (1): `ξ_s = x_n` for `t_n ≤ s < t_{n+1}`, and `ξ_s = x_∞ ∉ X` for
`s ≥ t_∞`. -/
def xiIn (ω : Traj X) (s : ℝ) (Z : Set X) : Prop :=
  ∃ n, tn ω n ≤ ENNReal.ofReal s ∧ ENNReal.ofReal s < tn ω (n + 1) ∧ xn ω n ∈ Z

/-- The natural filtration `𝓕_t = σ(ξ_s : 0 ≤ s ≤ t)` (p. 4); `σ(ξ_s)` is generated by the events
`{ξ_s ∈ Z}`, `Z ∈ 𝔅(X)` (their complements give `{ξ_s = x_∞}`). -/
def natFilt (t : ℝ) : MeasurableSpace (Traj X) :=
  MeasurableSpace.generateFrom
    {S | ∃ (s : ℝ) (Z : Set X), 0 ≤ s ∧ s ≤ t ∧ MeasurableSet Z ∧ S = {ω | xiIn ω s Z}}

/-- `T` is a stopping time of the natural filtration with values in `ℝ₊ = ]0, +∞[` ((8), p. 5). -/
def IsStopTime (T : Traj X → ℝ) : Prop :=
  (∀ ω, 0 < T ω) ∧ ∀ t : ℝ, MeasurableSet[natFilt t] {ω | T ω ≤ t}

/-- (7) at a random time `T`: `𝔼 µ([0, T], Z) = 𝔼 Σ_{n ≥ 1} I{t_n ≤ T} I{x_n ∈ Z}`. -/
def EmuAt (P : Measure (Traj X)) (T : Traj X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' n, {ω : Traj X | tn ω (n + 1) ≤ ENNReal.ofReal (T ω) ∧ xn ω (n + 1) ∈ Z}.indicator
    (fun _ => (1 : ℝ≥0∞)) ω ∂P

/-- (7): `𝔼 µ([0, t], Z) = 𝔼 Σ_{n ≥ 1} I{t_n ≤ t} I{x_n ∈ Z}`. -/
def Emu (P : Measure (Traj X)) (t : ℝ) (Z : Set X) : ℝ≥0∞ :=
  EmuAt P (fun _ => t) Z

/-- (36) at a random time `T`: `𝔼 µ̃([0, T], Z) = 𝔼 Σ_{n ≥ 1} I{t_n ≤ T} I{x_{n−1} ∈ Z}`. -/
def EmuTildeAt (P : Measure (Traj X)) (T : Traj X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' n, {ω : Traj X | tn ω (n + 1) ≤ ENNReal.ofReal (T ω) ∧ xn ω n ∈ Z}.indicator
    (fun _ => (1 : ℝ≥0∞)) ω ∂P

/-- (36): `𝔼 µ̃([0, t], Z) = 𝔼 Σ_{n ≥ 1} I{t_n ≤ t} I{x_{n−1} ∈ Z}`. -/
def EmuTilde (P : Measure (Traj X)) (t : ℝ) (Z : Set X) : ℝ≥0∞ :=
  EmuTildeAt P (fun _ => t) Z

/-- (9) at a random time `T`: `𝔼 ν^π([0, T], Z) = 𝔼 ∫_0^T q̃(ξ_s, π_s, Z \ {ξ_s}) I{ξ_s ∈ X} ds`. -/
def EnuPiAt (M : Model X A) (P : Measure (Traj X)) (π : Policy X A) (T : Traj X → ℝ)
    (Z : Set X) : ℝ≥0∞ :=
  expPathAt P π T (fun z p => jumpP M z p (Z \ {z}))

/-- (9): `𝔼 ν^π([0, t], Z) = 𝔼 ∫_0^t q̃(ξ_s, π_s, Z \ {ξ_s}) I{ξ_s ∈ X} ds`. -/
def EnuPi (M : Model X A) (P : Measure (Traj X)) (π : Policy X A) (t : ℝ) (Z : Set X) : ℝ≥0∞ :=
  EnuPiAt M P π (fun _ => t) Z

/-- (35) at a random time `T`: `𝔼 ν̃^π([0, T], Z) = 𝔼 ∫_0^T q̃(ξ_s, π_s) I{ξ_s ∈ Z} ds`. -/
def EnuTildeAt (M : Model X A) (P : Measure (Traj X)) (π : Policy X A) (T : Traj X → ℝ)
    (Z : Set X) : ℝ≥0∞ :=
  expPathAt P π T (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * rateP M z p)

/-- (35): `𝔼 ν̃^π([0, t], Z) = 𝔼 ∫_0^t q̃(ξ_s, π_s) I{ξ_s ∈ Z} ds`. -/
def EnuTilde (M : Model X A) (P : Measure (Traj X)) (π : Policy X A) (t : ℝ) (Z : Set X) : ℝ≥0∞ :=
  EnuTildeAt M P π (fun _ => t) Z

/-- `𝔼 q̃(ξ_t, π_t) I{ξ_t ∈ Z}`. -/
def outRate (M : Model X A) (P : Measure (Traj X)) (π : Policy X A) (t : ℝ) (Z : Set X) : ℝ≥0∞ :=
  expAt P π t (fun z p => Z.indicator (fun _ => (1 : ℝ≥0∞)) z * rateP M z p)

/-- Definition 2: `Z` is `(x, π)`-bounded if `sup_{t > 0} 𝔼 q̃(ξ_t, π_t) I{ξ_t ∈ Z} < ∞`
(here for the law `P`). -/
def IsBoundedFor (M : Model X A) (P : Measure (Traj X)) (π : Policy X A) (Z : Set X) : Prop :=
  (⨆ (t : ℝ) (_ : 0 < t), outRate M P π t Z) < ⊤

/-! ### Q-functions, Kolmogorov's forward equation, Feller's series ((23)–(33), Definition 1) -/

/-- A Q-function (p. 8), given by its off-diagonal part `qQ z t = q(z, t, · \ {z})`: a finite measure
not charging `{z}` for each `t > 0`, measurable in `(z, t)`. -/
structure IsQFunction (qQ : X → ℝ → Measure X) : Prop where
  finite : ∀ z t, 0 < t → IsFiniteMeasure (qQ z t)
  no_self : ∀ z t, 0 < t → qQ z t {z} = 0
  measurable : ∀ Z : Set X, MeasurableSet Z → Measurable (fun p : X × Ioi (0 : ℝ) => qQ p.1 p.2 Z)

/-- (29): the `q`-bounded sets `𝒴 = {Z : sup_{z ∈ Z, t > 0} q(z, t) < ∞}`, `q(z, t) = q(z, t, X \ {z})`. -/
def YsetQ (qQ : X → ℝ → Measure X) : Set (Set X) :=
  {Z | MeasurableSet Z ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ Z, ∀ t : ℝ, 0 < t → qQ z t {z}ᶜ ≤ C}

/-- Definition 1: `Q` solves Kolmogorov's forward equation (30) from `x`: (i) each `Q t` (`t > 0`) is a
finite measure, (ii) `t ↦ Q(t, Z)` is measurable, (iii) for `t > 0` and `Z ∈ 𝒴`,
`Q(t, Z) = δ_x(Z) + ∫_0^t ∫_X q(z, s, Z \ {z}) Q(s, dz) ds − ∫_0^t ∫_Z q(z, s) Q(s, dz) ds`,
written additively with the subtracted term finite. -/
structure IsFwdSolQ (qQ : X → ℝ → Measure X) (x : X) (Q : ℝ → Measure X) : Prop where
  finite : ∀ t : ℝ, 0 < t → Q t univ < ⊤
  measurable : ∀ Z : Set X, MeasurableSet Z → Measurable (fun t : Ioi (0 : ℝ) => Q t Z)
  eqn : ∀ t : ℝ, 0 < t → ∀ Z ∈ YsetQ qQ,
    Q t Z < ⊤ ∧
    (∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z in Z, qQ z s {z}ᶜ ∂(Q s)) < ⊤ ∧
    Q t Z + ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z in Z, qQ z s {z}ᶜ ∂(Q s) =
      Measure.dirac x Z + ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ z, qQ z s (Z \ {z}) ∂(Q s)

/-- (25): `P̄^{(0)}(u, x; t, Z) = δ_x(Z) e^{−∫_u^t q(x, s) ds}`. -/
def feller0 (qQ : X → ℝ → Measure X) (u : ℝ) (x : X) (t : ℝ) (Z : Set X) : ℝ≥0∞ :=
  Measure.dirac x Z * surv (∫⁻ s in Ioc u t, qQ x s {x}ᶜ)

/-- (25)–(26): `P̄^{(n)}(u, x; t, Z)`. -/
def fellerN (qQ : X → ℝ → Measure X) : ℕ → ℝ → X → ℝ → Set X → ℝ≥0∞
  | 0, u, x, t, Z => feller0 qQ u x t Z
  | n + 1, u, x, t, Z =>
      ∫⁻ w in Ioc u t, surv (∫⁻ θ in Ioc u w, qQ x θ {x}ᶜ) *
        ∫⁻ y, fellerN qQ n w y t Z ∂((qQ x w).restrict {x}ᶜ)

/-- (27): Feller's minimal transition function `P̄(u, x; t, Z) = Σ_n P̄^{(n)}(u, x; t, Z)`. -/
def fellerSeries (qQ : X → ℝ → Measure X) (u : ℝ) (x : X) (t : ℝ) (Z : Set X) : ℝ≥0∞ :=
  ∑' n, fellerN qQ n u x t Z

/-- The Q-function of a Markov policy: `q(z, t, Z \ {z}) = q̃(z, ϕ_t, Z \ {z})`. -/
def qOf (M : Model X A) (phi : X → ℝ → Measure A) (z : X) (t : ℝ) : Measure X :=
  jumpP M z (phi z t)

/-- (33): `𝒴^ϕ`. -/
def Yset (M : Model X A) (phi : X → ℝ → Measure A) : Set (Set X) :=
  YsetQ (qOf M phi)

/-- `Q` solves Kolmogorov's forward equation (32) for the Markov policy `ϕ` from `x`. -/
def IsFwdSol (M : Model X A) (phi : X → ℝ → Measure A) (x : X) (Q : ℝ → Measure X) : Prop :=
  IsFwdSolQ (qOf M phi) x Q

end

end CTJMDP.MarkovSuff


