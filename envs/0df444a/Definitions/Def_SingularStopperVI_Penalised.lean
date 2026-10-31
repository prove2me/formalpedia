-- Prove2me | Definitions.Def_SingularStopperVI_Penalised
-- name    : SingularStopperVI_Penalised
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:44.303811+00:00
-- url     : https://prove2.me/theorems/e565beb7-4679-4410-be61-6ca888bea81d
-- title:
--   The penalised objects: $\xi_m$, $\psi_\varepsilon$, $g_m$, $h_m$, $f_m$, Problems B and C, $\mathcal A^\circ_t$, $\mathcal T^\delta_t$, Hamiltonians, penalised payoffs
-- statement:
--   The penalised objects of §§4–5. **Cut-offs** $\xi_m\in C_c^\infty(\mathbb R^d)$ have $0\le\xi_m\le1$, $\xi_m=1$ on $B_m$, $\xi_m=0$ off $B_{m+1}$ and $|\nabla\xi_m|_d^2\le C_0\xi_m$. **Penalties** $\psi_\varepsilon\in C^2(\mathbb R)$ are non-negative, convex and non-decreasing, vanish on $(-\infty,0]$, are positive on $(0,\infty)$, and equal $(y-\varepsilon)/\varepsilon$ for $y\ge2\varepsilon$.
--
--   Set $g_m=\xi_{m-1}g$, $h_m=\xi_{m-1}h$ and
--
--   $$
--   f_m=\big(f^2+\|g\|^2_{C^0(\bar{\mathcal O}_m)}|\nabla\xi_{m-1}|_d^2+2g\xi_{m-1}\langle\nabla\xi_{m-1},\nabla g\rangle\big)^{1/2}.
--   $$
--
--   **Problem B.** Find $u\in C^{1,2,\alpha}(\bar{\mathcal O}_m)$ with $\partial_tu+\mathcal Lu-ru=-h_m-\frac1\delta(g_m-u)^++\psi_\varepsilon(|\nabla u|_d^2-f_m^2)$ on $\mathcal O_m=[0,T)\times B_m$, and $u=g_m$ on $\partial_P\mathcal O_m$.
--
--   **Problem C.** Find $u\in(C^{1,2,\alpha}_{Loc}\cap W^{1,2,p}_{\ell oc})(\mathbb R^{d+1}_{0,T})$, for every $p\in(1,\infty)$, with $\partial_tu+\mathcal Lu-ru=-h-\frac1\delta(g-u)^++\psi_\varepsilon(|\nabla u|_d^2-f^2)$ on $[0,T)\times\mathbb R^d$, and $u(T,\cdot)=g(T,\cdot)$.
--
--   The associated games use absolutely continuous controls $\mathcal A^\circ_t$ with rate $\dot\nu$, intensities $w\in\mathcal T^\delta_t$ with $0\le w\le1/\delta$, the discount $R^w_s=\exp(-\int_0^s(r+w_\lambda)\,d\lambda)$, the Hamiltonians $H(t,x,y)=\sup_p\{\langle y,p\rangle-\psi_\varepsilon(|p|_d^2-\phi^2(t,x))\}$ for $\phi=f_m$ and $\phi=f$, the exit time $\rho_m$, and the payoffs $\mathcal J^{\varepsilon,\delta,m}$, $\mathcal J^{\varepsilon,\delta}$. The feedback form (5.23) is also here.
--
--   **Formalization Note** Indices follow the page, with $m\ge1$ in every statement. Problem B's derivatives are named by a `Jet`; for Problem C, `K.Du` is the continuous gradient on $[0,T]\times\mathbb R^d$ given by (2.2). Controls of $\mathcal A^\circ_t$ are given by the rate. Payoffs lie in $[0,\infty]$, and the Hamiltonian is a $[0,\infty]$-valued supremum, which equals the real one since that is non-negative.
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, (4.1), Problem B, (4.3), pp.8–9, (4.4), (4.6), (4.7), p.9; Problem C, (5.14), p.22; (5.16), p.23; (5.23), p.24; Proposition 5.5, p.25

import Mathlib
import Definitions.Def_SingularStopperVI_Assumptions

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d d' : ℕ}

open scoped ContDiff in
/-- The cut-off functions (4.1), p.8: `ξ_m ∈ C_c^∞(ℝ^d)`, `0 ≤ ξ_m ≤ 1`, `ξ_m = 1` on `B_m`,
`ξ_m = 0` off `B_{m+1}`, and `|∇ξ_m|_d² ≤ C₀ ξ_m` with `C₀` independent of `m`. -/
structure IsCutoff (ξ : ℕ → Euc d → ℝ) (C0 : ℝ) : Prop where
  C0_pos : 0 < C0
  smooth : ∀ m, ContDiff ℝ ∞ (ξ m)
  compact : ∀ m, HasCompactSupport (ξ m)
  mem : ∀ m x, 0 ≤ ξ m x ∧ ξ m x ≤ 1
  eq_one : ∀ m : ℕ, ∀ x ∈ Metric.ball (0 : Euc d) m, ξ m x = 1
  eq_zero : ∀ m : ℕ, ∀ x, x ∉ Metric.ball (0 : Euc d) (m + 1) → ξ m x = 0
  grad : ∀ m x, ‖gradient (ξ m) x‖ ^ 2 ≤ C0 * ξ m x

/-- The penalty functions of p.8: for `ε ∈ (0,1)`, `ψ_ε ∈ C²(ℝ)` is non-negative and convex, `ψ_ε = 0`
on `(−∞,0]`, `ψ_ε > 0` on `(0,∞)`, `ψ_ε' ≥ 0`, and `ψ_ε(y) = (y−ε)/ε` for `y ≥ 2ε`. -/
structure IsPenalty (ψ : ℝ → ℝ → ℝ) : Prop where
  smooth : ∀ ε ∈ Ioo (0 : ℝ) 1, ContDiff ℝ 2 (ψ ε)
  nonneg : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ y, 0 ≤ ψ ε y
  convex : ∀ ε ∈ Ioo (0 : ℝ) 1, ConvexOn ℝ univ (ψ ε)
  eq_zero : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ y, y ≤ 0 → ψ ε y = 0
  pos : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ y, 0 < y → 0 < ψ ε y
  deriv_nonneg : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ y, 0 ≤ deriv (ψ ε) y
  linear : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ y, 2 * ε ≤ y → ψ ε y = (y - ε) / ε

/-- `g_m := ξ_{m−1} g`, p.8. -/
def gm (D : Data d d') (ξ : ℕ → Euc d → ℝ) (m : ℕ) (t : ℝ) (x : Euc d) : ℝ :=
  ξ (m - 1) x * D.g t x

/-- `h_m := ξ_{m−1} h`, p.8. -/
def hm (D : Data d d') (ξ : ℕ → Euc d → ℝ) (m : ℕ) (t : ℝ) (x : Euc d) : ℝ :=
  ξ (m - 1) x * D.h t x

/-- `‖g‖_{C⁰(Ō_m)}`, a supremum over a compact non-empty set of a continuous function. -/
noncomputable def gSupNorm (D : Data d d') (m : ℕ) : ℝ :=
  sSup ((fun z : ℝ × Euc d => |D.g z.1 z.2|) '' closedCyl d D.T m)

/-- The radicand `f² + ‖g‖²_{C⁰(Ō_m)} |∇ξ_{m−1}|_d² + 2 g ξ_{m−1} ⟨∇ξ_{m−1},∇g⟩` of `f_m`, p.8. The last
term has no absolute value. -/
noncomputable def fmSq (D : Data d d') (Jg : Jet d) (ξ : ℕ → Euc d → ℝ) (m : ℕ) (t : ℝ)
    (x : Euc d) : ℝ :=
  D.f t x ^ 2 + gSupNorm D m ^ 2 * ‖gradient (ξ (m - 1)) x‖ ^ 2 +
    2 * (D.g t x * ξ (m - 1) x * inner ℝ (gradient (ξ (m - 1)) x) (Jg.Du t x))

/-- `f_m`, p.8. The radicand is non-negative on `Ō_m` by (3.9). -/
noncomputable def fm (D : Data d d') (Jg : Jet d) (ξ : ℕ → Euc d → ℝ) (m : ℕ) (t : ℝ)
    (x : Euc d) : ℝ :=
  Real.sqrt (fmSq D Jg ξ m t x)

/-- The parabolic boundary `∂_P O_m = ([0,T) × ∂B_m) ∪ ({T} × B̄_m)`, p.8. -/
def parabolicBoundary (d : ℕ) (T R : ℝ) : Set (ℝ × Euc d) :=
  (Ico 0 T ×ˢ Metric.sphere 0 R) ∪ ({T} ×ˢ Metric.closedBall 0 R)

/-- Problem B, (4.3), p.8: `u ∈ C^{1,2,α}(Ō_m)` with derivatives `K` solves
`∂_t u + Lu − ru = −h_m − (1/δ)(g_m − u)^+ + ψ_ε(|∇u|_d² − f_m²)` on `O_m`, and `u = g_m` on `∂_P O_m`. -/
structure IsProblemB (D : Data d d') (Jg : Jet d) (ξ : ℕ → Euc d → ℝ) (ψ : ℝ → ℝ → ℝ)
    (α ε δ : ℝ) (m : ℕ) (u : ℝ → Euc d → ℝ) (K : Jet d) : Prop where
  reg : IsC12AlphaOn D.T α (openCyl d D.T m) (closedCyl d D.T m) u K
  pde : ∀ z ∈ openCyl d D.T m, pdeOperator D u K z.1 z.2 =
    -hm D ξ m z.1 z.2 - (1 / δ) * max (gm D ξ m z.1 z.2 - u z.1 z.2) 0 +
      ψ ε (‖K.Du z.1 z.2‖ ^ 2 - fm D Jg ξ m z.1 z.2 ^ 2)
  boundary : ∀ z ∈ parabolicBoundary d D.T m, u z.1 z.2 = gm D ξ m z.1 z.2

/-- Problem C, (5.14), p.22: `u ∈ (C^{1,2,α}_{Loc} ∩ W^{1,2,p}_{ℓoc})(ℝ^{d+1}_{0,T})` for every
`p ∈ (1,∞)` solves `∂_t u + Lu − ru = −h − (1/δ)(g − u)^+ + ψ_ε(|∇u|_d² − f²)` on `[0,T) × ℝ^d`, and
`u(T,·) = g(T,·)`.

**Formalization Note** `C^{1,2,α}_{Loc}` gives no gradient at `t = T`. The gradient of `W^{1,2,p}_{ℓoc}`
has a continuous representative on `[0,T] × ℝ^d` by (2.2), and `K.Du` is that representative. -/
structure IsProblemC (D : Data d d') (ψ : ℝ → ℝ → ℝ) (α ε δ : ℝ) (u : ℝ → Euc d → ℝ)
    (K : Jet d) : Prop where
  reg : IsC12AlphaCapLoc D.T α u K
  sobolev : ∀ p : ℝ, 1 < p → IsW12pLoc D.T p u K
  cont_Du : ContinuousOn (fun z : ℝ × Euc d => K.Du z.1 z.2) (stateDomain d D.T)
  pde : ∀ t ∈ Ico 0 D.T, ∀ x, pdeOperator D u K t x =
    -D.h t x - (1 / δ) * max (D.g t x - u t x) 0 + ψ ε (‖K.Du t x‖ ^ 2 - D.f t x ^ 2)
  terminal : ∀ x, u D.T x = D.g D.T x

/-- The class `𝒜°_t` of p.8, with `S = T − t`: `n` as in `𝒜_t`, and `ν` absolutely continuous, given by
its rate `q = ν̇`, with `E[(∫_0^S q_s ds)²] < ∞`.

**Formalization Note** Only `ν̇` enters the dynamics and the payoffs of pp.8–9, so the control is
parametrised by the rate, a progressive non-negative locally integrable process. -/
structure IsRateControl (B : Basis d' Ω) (S : ℝ≥0) (n : ℝ≥0 → Ω → Euc d) (q : ℝ≥0 → Ω → ℝ) :
    Prop where
  prog_n : IsProgressive B.F n
  unit : ∀ᵐ ω ∂B.P, ∀ s, ‖n s ω‖ = 1
  prog_q : IsProgressive B.F q
  path : ∀ᵐ ω ∂B.P, (∀ s, 0 ≤ q s ω) ∧
    ∀ s : ℝ, IntegrableOn (fun z : ℝ => q z.toNNReal ω) (Icc 0 s)
  square : ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) S, ENNReal.ofReal (q s.toNNReal ω)) ^ 2 ∂B.P < ⊤

/-- The controlled dynamics of p.9, on `[0,S]`:
`X_s = x + ∫_0^s (b(X_u) + n_u ν̇_u) du + ∫_0^s σ(X_u) dW_u`. -/
structure IsRateStateSol (B : Basis d' Ω) (D : Data d d') (S : ℝ≥0) (x : Euc d)
    (n : ℝ≥0 → Ω → Euc d) (q : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) : Prop where
  adapted : ∀ s ≤ S, Measurable[B.F s] (X s)
  continuous : ∀ᵐ ω ∂B.P, ContinuousOn (fun s => X s ω) (Icc 0 S)
  equation : ∃ M : Fin d → Fin d' → ℝ≥0 → Ω → ℝ,
    (∀ i j, IsItoIntegral B.P B.F (fun s ω => B.W s ω j) S
      (fun s ω => D.σ (X s ω) i j) (M i j)) ∧
    ∀ᵐ ω ∂B.P, ∀ s ≤ S,
      X s ω = x + (∫ u in Icc (0 : ℝ) s,
        (D.b (X u.toNNReal ω) + q u.toNNReal ω • n u.toNNReal ω)) + itoVector M s ω

/-- A pair of `𝒜°_t` given by its rate, with a solution of the dynamics from `x`. -/
abbrev RateState (B : Basis d' Ω) (D : Data d d') (t : ℝ) (x : Euc d) :=
  {c : (ℝ≥0 → Ω → Euc d) × (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → Euc d) //
    IsRateControl B (horizon D t) c.1 c.2.1 ∧ IsRateStateSol B D (horizon D t) x c.1 c.2.1 c.2.2}

/-- `w ∈ 𝒯^δ_t`, p.9, with `S = T − t`: `w` is progressive with, almost surely, `0 ≤ w_s ≤ 1/δ` for
all `s ∈ [0,S]`. -/
structure IsIntensity (B : Basis d' Ω) (δ : ℝ) (S : ℝ≥0) (w : ℝ≥0 → Ω → ℝ) : Prop where
  prog : IsProgressive B.F w
  bound : ∀ᵐ ω ∂B.P, ∀ s ≤ S, 0 ≤ w s ω ∧ w s ω ≤ 1 / δ

/-- The class `𝒯^δ_t`. -/
abbrev Intensity (B : Basis d' Ω) (D : Data d d') (δ t : ℝ) :=
  {w : ℝ≥0 → Ω → ℝ // IsIntensity B δ (horizon D t) w}

/-- The controlled discount factor `R^w_s = exp(−∫_0^s (r + w_λ) dλ)`, p.9. -/
noncomputable def discountFactor (D : Data d d') (w : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-∫ l in Icc (0 : ℝ) s, (D.r + w l.toNNReal ω))

/-- The Hamiltonians `H^ε_m` of (4.4) and `H^ε` of (5.16):
`sup_{p ∈ ℝ^d} {⟨y,p⟩ − ψ_ε(|p|_d² − φ²(t,x))}`, for `φ = f_m` and `φ = f`.

**Formalization Note** The supremum is taken in `[0,∞]`. The real supremum is non-negative (pick
`p = 0`), so truncating at `0` changes nothing and the junk value of an unbounded real `⨆` is
avoided. -/
noncomputable def hamiltonian (ψ : ℝ → ℝ → ℝ) (ε : ℝ) (φ : ℝ → Euc d → ℝ) (t : ℝ) (x y : Euc d) :
    ℝ≥0∞ :=
  ⨆ p : Euc d, ENNReal.ofReal (inner ℝ y p - ψ ε (‖p‖ ^ 2 - φ t x ^ 2))

/-- The exit time `ρ_m = inf{s ≥ 0 | X_s ∉ B_m} ∧ (T−t)`, (4.6), p.9. As in `tauStar`, the set is
restricted to `[0,T−t]` and contains `T−t`. -/
noncomputable def exitTime (D : Data d d') (m : ℕ) (t : ℝ) (X : ℝ≥0 → Ω → Euc d) (ω : Ω) : ℝ≥0 :=
  sInf ({s : ℝ≥0 | s ≤ horizon D t ∧ X s ω ∉ Metric.ball (0 : Euc d) m} ∪ {horizon D t})

/-- The expected payoff shape of (4.7), p.9, in `[0,∞]`, for an end time `ρ`, a running payoff `h'`, a
stopping payoff `g'` and a Hamiltonian `H`:
`E[∫_0^ρ R^w_s [h' + w_s g' + H(·, n_s ν̇_s)](t+s,X_s) ds + R^w_ρ g'(t+ρ,X_ρ)]`. -/
noncomputable def penalisedExpectation (B : Basis d' Ω) (D : Data d d') (t : ℝ)
    (h' g' : ℝ → Euc d → ℝ) (H : ℝ → Euc d → Euc d → ℝ≥0∞) (ρ : Ω → ℝ≥0)
    (n : ℝ≥0 → Ω → Euc d) (q : ℝ≥0 → Ω → ℝ) (w : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) : ℝ≥0∞ :=
  ∫⁻ ω,
    ((∫⁻ s in Icc (0 : ℝ) (ρ ω),
        ENNReal.ofReal (discountFactor D w s.toNNReal ω) *
          (ENNReal.ofReal (h' (t + s) (X s.toNNReal ω) +
              w s.toNNReal ω * g' (t + s) (X s.toNNReal ω)) +
            H (t + s) (X s.toNNReal ω) (q s.toNNReal ω • n s.toNNReal ω))) +
      ENNReal.ofReal (discountFactor D w (ρ ω) ω * g' (t + ρ ω) (X (ρ ω) ω))) ∂B.P

/-- The payoff `J^{ε,δ,m}_{t,x}(n,ν,w)` of (4.7), p.9. -/
noncomputable def payoffM (B : Basis d' Ω) (D : Data d d') (Jg : Jet d) (ξ : ℕ → Euc d → ℝ)
    (ψ : ℝ → ℝ → ℝ) (ε : ℝ) (m : ℕ) (t : ℝ) (n : ℝ≥0 → Ω → Euc d) (q : ℝ≥0 → Ω → ℝ)
    (w : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) : ℝ≥0∞ :=
  penalisedExpectation B D t (hm D ξ m) (gm D ξ m) (hamiltonian ψ ε (fm D Jg ξ m))
    (exitTime D m t X) n q w X

/-- The payoff `J^{ε,δ}_{t,x}(n,ν,w)` of p.23: as (4.7), with `ρ_m`, `g_m`, `h_m`, `H^ε_m` replaced by
`T−t`, `g`, `h`, `H^ε`. -/
noncomputable def payoffC (B : Basis d' Ω) (D : Data d d') (ψ : ℝ → ℝ → ℝ) (ε : ℝ) (t : ℝ)
    (n : ℝ≥0 → Ω → Euc d) (q : ℝ≥0 → Ω → ℝ) (w : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) : ℝ≥0∞ :=
  penalisedExpectation B D t D.h D.g (hamiltonian ψ ε D.f) (fun _ => horizon D t) n q w X

/-- The upper value `inf_{(n,ν) ∈ 𝒜°_t} sup_{w ∈ 𝒯^δ_t} J^{ε,δ,m}`, p.9. -/
noncomputable def upperValueM (B : Basis d' Ω) (D : Data d d') (Jg : Jet d) (ξ : ℕ → Euc d → ℝ)
    (ψ : ℝ → ℝ → ℝ) (ε δ : ℝ) (m : ℕ) (t : ℝ) (x : Euc d) : ℝ≥0∞ :=
  ⨅ c : RateState B D t x, ⨆ w : Intensity B D δ t,
    payoffM B D Jg ξ ψ ε m t c.1.1 c.1.2.1 w.1 c.1.2.2

/-- The lower value `sup_{w ∈ 𝒯^δ_t} inf_{(n,ν) ∈ 𝒜°_t} J^{ε,δ,m}`, p.9. -/
noncomputable def lowerValueM (B : Basis d' Ω) (D : Data d d') (Jg : Jet d) (ξ : ℕ → Euc d → ℝ)
    (ψ : ℝ → ℝ → ℝ) (ε δ : ℝ) (m : ℕ) (t : ℝ) (x : Euc d) : ℝ≥0∞ :=
  ⨆ w : Intensity B D δ t, ⨅ c : RateState B D t x,
    payoffM B D Jg ξ ψ ε m t c.1.1 c.1.2.1 w.1 c.1.2.2

/-- The upper value `inf_{(n,ν) ∈ 𝒜°_t} sup_{w ∈ 𝒯^δ_t} J^{ε,δ}` of (5.19), p.23. -/
noncomputable def upperValueC (B : Basis d' Ω) (D : Data d d') (ψ : ℝ → ℝ → ℝ) (ε δ t : ℝ)
    (x : Euc d) : ℝ≥0∞ :=
  ⨅ c : RateState B D t x, ⨆ w : Intensity B D δ t, payoffC B D ψ ε t c.1.1 c.1.2.1 w.1 c.1.2.2

/-- The lower value `sup_{w ∈ 𝒯^δ_t} inf_{(n,ν) ∈ 𝒜°_t} J^{ε,δ}` of (5.19), p.23. -/
noncomputable def lowerValueC (B : Basis d' Ω) (D : Data d d') (ψ : ℝ → ℝ → ℝ) (ε δ t : ℝ)
    (x : Euc d) : ℝ≥0∞ :=
  ⨆ w : Intensity B D δ t, ⨅ c : RateState B D t x, payoffC B D ψ ε t c.1.1 c.1.2.1 w.1 c.1.2.2

/-- The payoff in the display of Proposition 5.5, p.25, in `[0,∞]`:
`E[e^{−(r+δ⁻¹)(T−t)} g(T,X_{T−t}) + ∫_0^{T−t} e^{−(r+δ⁻¹)s} [h + (1/δ) g ∨ u + H^ε(·,n_s ν̇_s)](t+s,X_s) ds]`. -/
noncomputable def controlledPayoffC (B : Basis d' Ω) (D : Data d d') (ψ : ℝ → ℝ → ℝ)
    (ε δ : ℝ) (u : ℝ → Euc d → ℝ) (t : ℝ) (n : ℝ≥0 → Ω → Euc d) (q : ℝ≥0 → Ω → ℝ)
    (X : ℝ≥0 → Ω → Euc d) : ℝ≥0∞ :=
  ∫⁻ ω,
    (ENNReal.ofReal (Real.exp (-(D.r + δ⁻¹) * horizon D t) * D.g D.T (X (horizon D t) ω)) +
      ∫⁻ s in Icc (0 : ℝ) (horizon D t),
        ENNReal.ofReal (Real.exp (-(D.r + δ⁻¹) * s)) *
          (ENNReal.ofReal (D.h (t + s) (X s.toNNReal ω) +
              (1 / δ) * max (D.g (t + s) (X s.toNNReal ω)) (u (t + s) (X s.toNNReal ω))) +
            hamiltonian ψ ε D.f (t + s) (X s.toNNReal ω) (q s.toNNReal ω • n s.toNNReal ω)))
    ∂B.P

/-- The feedback form (5.23), p.24, on `[0,T−t]`, with `ψ_ε' = deriv (ψ ε)`:
`n_s = −∇u/|∇u|_d` where `∇u ≠ 0` (any unit vector where `∇u = 0`, which `IsRateControl` supplies) and
`ν̇_s = 2ψ_ε'(|∇u|_d² − f²)|∇u|_d`, all at `(t+s, X_s)`. -/
def IsFeedback (B : Basis d' Ω) (D : Data d d') (ψ : ℝ → ℝ → ℝ) (ε : ℝ) (K : Jet d) (t : ℝ)
    (n : ℝ≥0 → Ω → Euc d) (q : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Euc d) : Prop :=
  ∀ᵐ ω ∂B.P, ∀ s ≤ horizon D t,
    (K.Du (t + s) (X s ω) ≠ 0 → n s ω = -(‖K.Du (t + s) (X s ω)‖⁻¹ • K.Du (t + s) (X s ω))) ∧
    q s ω = 2 * deriv (ψ ε) (‖K.Du (t + s) (X s ω)‖ ^ 2 - D.f (t + s) (X s ω) ^ 2) *
      ‖K.Du (t + s) (X s ω)‖

end SingularStopperVI


