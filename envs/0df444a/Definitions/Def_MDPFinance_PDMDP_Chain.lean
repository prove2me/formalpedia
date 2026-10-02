-- Prove2me | Definitions.Def_MDPFinance_PDMDP_Chain
-- name    : MDPFinance_PDMDP_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:08.364034+00:00
-- url     : https://prove2.me/theorems/e770e143-bf69-41de-a1f5-7174608241a1
-- title:
--   The continuous-time Markov Decision Chain, infinite and finite horizon (§8.3)
-- statement:
--   Section 8.3 studies a genuinely different, simpler model: a **continuous-time Markov Decision Chain** on a *countable* state space $E$, with conservative, bounded transition rates $q_{xy}(u)$ in place of a general kernel $Q$, and an uncontrolled (trivial) flow. `MDChain` bundles this infinite-horizon, discounted ($\beta$) model; `MDChainFinite` bundles the finite-horizon variant (no discount, but a terminal reward $g$ and horizon $Th$, matching the book's own presentation, which drops $\beta$ entirely for the finite-horizon case). Both share the uniformized transition probability $Q(\{y\}\mid x,u) := \frac1\lambda q_{xy}(u)$ ($y \ne x$), $1+\frac1\lambda q_{xx}(u)$ ($y=x$) (`Qy`), and each has its own embedded discrete-time reward/kernel ($r'$, and $Q'$ folded directly into the value recursions `Jn`/`Jinf`/`Vinf` as sums rather than a separate bundled measure, since $E$ countable makes this direct), plus a bounding-function class appropriate to each case (`IsUpperBoundingFunctionChain`, `IsUpperBoundingFunctionChainFinite`) and, for the finite-horizon case, the explicit maximal-reward operator `T` used by Theorem 8.3.3's own fixed-point equation.
--
--   **Formalization Note.** A self-contained pair of structures, *not* built from `PDMDPModel`, per this chunk's own pitfall note that §8.3's chain is a different object from §8.1-8.2's general model (sums over $E$ replace integrals, and there is no flow/ODE data at all).
--
--   **Moderation note.** The draft's `MDChain` had unconstrained rates (no `q(x,y,u) ≥ 0` off the diagonal, no conservativeness `∑_y q(x,y,u) = 0`, no summability), its transition probabilities were real `tsum`s (junk `0` when the series diverges), the embedded kernel was an unconstrained map and the value functions were real Bochner integrals/suprema over arbitrary maps. Now the generator is conservative with summable off-diagonal rates, `λ(x,u) := −q(x,x,u)`, `Q(y|x,u) := q(x,y,u)/λ(x,u)` for `y ≠ x`, the embedded kernel is the measure `Q'(·|x,u) = λ/(β+λ) ∑_y Q(y|x,u) δ_y`, `r'(x,u) = r(x,u)/(β+λ(x,u))`, stationary policies are decision rules into `U`, and `J_n`, `J_∞`, `V_∞` are `[-∞,∞]`-valued. The finite-horizon chain (§8.3.2) has the same data plus a terminal reward `g`, its policies are jointly measurable in `(t,x)`, and its integrability assumption and operator `T` are stated with `[-∞,∞]` values.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 256-260, PDF 267-271, §8.3's opening construction, Theorem 8.3.1's own hypothesis (upper bounding function for the chain), Eq. (8.11)-(8.14), and the unnumbered bounding-function condition and operator display preceding Theorem 8.3.3

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model

open MeasureTheory Filter
open scoped Classical ENNReal

namespace MDPFinance.PDMDP

/-- A **continuous-time Markov Decision Chain** (Bäuerle–Rieder, §8.3, p. 256-257, PDF 267-268):
countable state space `E`, controllable transition rates `q_{xy}(u)` that are conservative
(`q_{xy}(u) ≥ 0` for `y ≠ x`, `Σ_y q_{xy}(u) = 0`, absolutely summable) and bounded
(`-q_{xx}(u) ≤ λ`), reward rate `r`, discount rate `β ≥ 0`. A self-contained model, not built
from `PDMDPModel`. -/
structure MDChain (E U : Type*) [MeasurableSpace E] [Countable E] [MeasurableSpace U] where
  q : E → E → U → ℝ
  hq_meas : ∀ x y, Measurable (q x y)
  hq_offdiag : ∀ x y u, y ≠ x → 0 ≤ q x y u
  hq_summable : ∀ x u, Summable fun y => q x y u
  hq_conservative : ∀ x u, ∑' y, q x y u = 0
  lam : ℝ
  hlam : 0 < lam
  hq_bounded : ∀ x u, -q x x u ≤ lam
  r : E × U → ℝ
  hr_meas : Measurable r
  β : ℝ
  hβ : 0 ≤ β

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSpace U]

/-- `Q({y}|x,u)`, the uniformized transition probability (Bäuerle–Rieder, p. 257, PDF 268):
`q_{xy}(u)/λ` for `y ≠ x`, `1 + q_{xx}(u)/λ` for `y = x`. -/
noncomputable def MDChain.Qy (Ch : MDChain E U) (x y : E) (u : U) : ℝ :=
  if y = x then 1 + Ch.q x x u / Ch.lam else Ch.q x y u / Ch.lam

/-- The uniformized transition law `Q(·|x,u)` as a measure on `E`. -/
noncomputable def MDChain.Qmeas (Ch : MDChain E U) (x : E) (u : U) : Measure E :=
  Measure.sum fun y => ENNReal.ofReal (Ch.Qy x y u) • Measure.dirac y

/-- `Q'(·|x,u) := (λ/(β+λ)) Q(·|x,u)` (Bäuerle–Rieder, p. 257, PDF 268), the embedded
(substochastic) transition law. -/
noncomputable def MDChain.Qprime (Ch : MDChain E U) (x : E) (u : U) : Measure E :=
  ENNReal.ofReal (Ch.lam / (Ch.β + Ch.lam)) • Ch.Qmeas x u

/-- `r'(x,u) := r(x,u)/(β+λ)` (Bäuerle–Rieder, p. 257, PDF 268). -/
noncomputable def MDChain.rprime (Ch : MDChain E U) (xu : E × U) : ℝ :=
  Ch.r xu / (Ch.β + Ch.lam)

/-- A Markov policy `(f_n)` of the chain: measurable decision rules `E → U` (constant control
functions suffice, p. 257). -/
def IsChainPolicy (f : ℕ → E → U) : Prop := ∀ n, Measurable (f n)

/-- `J_n(f)(x)` of the embedded discrete-time model under a reward rate `rew`, in `[-∞,∞]`. -/
noncomputable def MDChain.JnWith (Ch : MDChain E U) (rew : E × U → ℝ) (f : ℕ → E → U) :
    ℕ → E → EReal
  | 0, _ => 0
  | (n + 1), x =>
      ((rew (x, f 0 x) / (Ch.β + Ch.lam) : ℝ) : EReal) +
        erealIntegral (Ch.Qprime x (f 0 x)) (Ch.JnWith rew (fun k => f (k + 1)) n)

/-- `J_n(f)(x)` for the reward `r`. -/
noncomputable def MDChain.Jn (Ch : MDChain E U) (f : ℕ → E → U) : ℕ → E → EReal :=
  Ch.JnWith Ch.r f

/-- `J_∞(f)(x)`, as a `limsup` of the finite-stage rewards-to-go. -/
noncomputable def MDChain.Jinf (Ch : MDChain E U) (f : ℕ → E → U) (x : E) : EReal :=
  atTop.limsup fun n => Ch.Jn f n x

/-- `V_∞(x) := sup_{(f_n)} J_∞(f_n)(x)` (Bäuerle–Rieder, p. 248/257), over Markov policies. -/
noncomputable def MDChain.Vinf (Ch : MDChain E U) (x : E) : EReal :=
  ⨆ f ∈ {f : ℕ → E → U | IsChainPolicy f}, Ch.Jinf f x

/-- The upper bounding function condition for a chain (Definition 8.2.4 applied to the chain's
uniformized `Q`, for which (iii) holds with `c_φ = λ/(λ+β)`): `r⁺(x,u) ≤ c_r b(x)` and
`Σ_y b(y) Q({y}|x,u) ≤ c_Q b(x)`; then `α_b ≤ c_Q λ/(β+λ)` (p. 257). -/
def IsUpperBoundingFunctionChain (Ch : MDChain E U) (b : E → ℝ) (cr cQ : ℝ) : Prop :=
  Measurable b ∧ (∀ x, 0 ≤ b x) ∧ 0 ≤ cr ∧ 0 ≤ cQ ∧
    (∀ x u, max (Ch.r (x, u)) 0 ≤ cr * b x) ∧
    ∀ x u, (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)) ≤ ENNReal.ofReal (cQ * b x)

/-- A continuous-time Markov Decision Chain **with finite time horizon** `T` (Bäuerle–Rieder,
§8.3, p. 258-259, PDF 269-270): the rate data of `MDChain` (no discount), a measurable terminal
reward `g` and a horizon `Th > 0`. -/
structure MDChainFinite (E U : Type*) [MeasurableSpace E] [Countable E] [MeasurableSpace U] where
  q : E → E → U → ℝ
  hq_meas : ∀ x y, Measurable (q x y)
  hq_offdiag : ∀ x y u, y ≠ x → 0 ≤ q x y u
  hq_summable : ∀ x u, Summable fun y => q x y u
  hq_conservative : ∀ x u, ∑' y, q x y u = 0
  lam : ℝ
  hlam : 0 < lam
  hq_bounded : ∀ x u, -q x x u ≤ lam
  r : E × U → ℝ
  hr_meas : Measurable r
  g : E → ℝ
  hg_meas : Measurable g
  Th : ℝ
  hTh : 0 < Th

/-- `Q({y}|x,u)` for the finite-horizon chain (the same uniformization). -/
noncomputable def MDChainFinite.Qy (Ch : MDChainFinite E U) (x y : E) (u : U) : ℝ :=
  if y = x then 1 + Ch.q x x u / Ch.lam else Ch.q x y u / Ch.lam

/-- The uniformized transition law as a measure on `E`. -/
noncomputable def MDChainFinite.Qmeas (Ch : MDChainFinite E U) (x : E) (u : U) : Measure E :=
  Measure.sum fun y => ENNReal.ofReal (Ch.Qy x y u) • Measure.dirac y

/-- `r'_{rew,gt}(t,x,α) := ∫_0^{T-t} e^{-λs} rew(x,α_s) ds + e^{-λ(T-t)} gt(x)` (Bäuerle–Rieder,
Eq. (8.14), p. 259, PDF 270), in `[-∞,∞]`, for a reward rate `rew` and terminal reward `gt`. -/
noncomputable def MDChainFinite.rprimeWith (Ch : MDChainFinite E U) (rew : E × U → ℝ)
    (gt : E → ℝ) (t : ℝ) (x : E) (α : ControlFn U) : EReal :=
  erealIntegral (volume.restrict (Set.Ioc (0 : ℝ) (Ch.Th - t))) (fun s =>
      ((Real.exp (-Ch.lam * s) * rew (x, α.1 s) : ℝ) : EReal)) +
    ((Real.exp (-Ch.lam * (Ch.Th - t)) * gt x : ℝ) : EReal)

/-- `r'(t,x,α)` for the data `(r,g)`. -/
noncomputable def MDChainFinite.rprime (Ch : MDChainFinite E U) (t : ℝ) (x : E)
    (α : ControlFn U) : EReal :=
  Ch.rprimeWith Ch.r Ch.g t x α

/-- A Markov policy `(f_n)` of the finite-horizon chain: measurable `f_n : [0,T] × E → A`
(Bäuerle–Rieder, p. 258, PDF 269). -/
def IsChainPolicyFinite (f : ℕ → ℝ → E → ControlFn U) : Prop :=
  ∀ n, Measurable fun p : ℝ × E => f n p.1 p.2

/-- `J_n(f)(t,x)` of the embedded model `(E',A,Q',r')` (Bäuerle–Rieder, Eq. (8.13)-(8.14)) under
data `(rew,gt)`: the step integrates over the time `s` to the next jump and averages over the
next state `y`, in `[-∞,∞]`. -/
noncomputable def MDChainFinite.JnWith (Ch : MDChainFinite E U) (rew : E × U → ℝ) (gt : E → ℝ)
    (f : ℕ → ℝ → E → ControlFn U) : ℕ → ℝ → E → EReal
  | 0, _, _ => 0
  | (n + 1), t, x =>
      Ch.rprimeWith rew gt t x (f 0 t x) +
        (Ch.lam : EReal) * erealIntegral (volume.restrict (Set.Ioc (0 : ℝ) (Ch.Th - t)))
          (fun s => ((Real.exp (-Ch.lam * s) : ℝ) : EReal) *
            erealIntegral (Ch.Qmeas x ((f 0 t x).1 s))
              (fun y => MDChainFinite.JnWith Ch rew gt (fun k => f (k + 1)) n (t + s) y))

/-- `J_n(f)(t,x)` for the data `(r,g)`. -/
noncomputable def MDChainFinite.Jn (Ch : MDChainFinite E U) (f : ℕ → ℝ → E → ControlFn U) :
    ℕ → ℝ → E → EReal :=
  Ch.JnWith Ch.r Ch.g f

/-- `J_∞(f)(t,x) = lim_n J_n(f)(t,x)`, as a `limsup`. -/
noncomputable def MDChainFinite.Jinf (Ch : MDChainFinite E U) (f : ℕ → ℝ → E → ControlFn U)
    (t : ℝ) (x : E) : EReal :=
  atTop.limsup fun n => Ch.Jn f n t x

/-- `V(t,x) := sup_{(f_n)} J_∞(f_n)(t,x)` (Bäuerle–Rieder, Eq. (8.12) via Theorem 8.3.2), over
Markov policies. -/
noncomputable def MDChainFinite.Vinf (Ch : MDChainFinite E U) (t : ℝ) (x : E) : EReal :=
  ⨆ f ∈ {f : ℕ → ℝ → E → ControlFn U | IsChainPolicyFinite f}, Ch.Jinf f t x

/-- The Integrability Assumption (A) of the finite-horizon chain (Bäuerle–Rieder, p. 258, PDF
269), through the embedding: `sup_π 𝔼^π_{tx}[∫_t^T r⁺(X_s,π_s) ds + g⁺(X_T)] < ∞`. -/
def IntegrabilityAssumptionChainFinite (Ch : MDChainFinite E U) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x : E,
    (⨆ f ∈ {f : ℕ → ℝ → E → ControlFn U | IsChainPolicyFinite f},
      atTop.limsup fun n =>
        Ch.JnWith (fun p => max (Ch.r p) 0) (fun y => max (Ch.g y) 0) f n t x) < ⊤

/-- The maximal reward operator `T` (Bäuerle–Rieder, p. 259-260, PDF 270-271): `(Tv)(t,x) =
e^{-λ(T-t)} g(x) + ∫_0^{T-t} e^{-λs} sup_{u∈U} [r(x,u) + λ Σ_y v(t+s,y) Q({y}|x,u)] ds`. -/
noncomputable def MDChainFinite.T (Ch : MDChainFinite E U) (v : ℝ → E → EReal) (t : ℝ) (x : E) :
    EReal :=
  ((Real.exp (-Ch.lam * (Ch.Th - t)) * Ch.g x : ℝ) : EReal) +
    erealIntegral (volume.restrict (Set.Ioc (0 : ℝ) (Ch.Th - t))) fun s =>
      ((Real.exp (-Ch.lam * s) : ℝ) : EReal) *
        ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
          (Ch.lam : EReal) * erealIntegral (Ch.Qmeas x u) (fun y => v (t + s) y))

/-- An upper bounding function for the finite-horizon chain (Bäuerle–Rieder, p. 260, PDF 271):
`r⁺(x,u) ≤ c_r b(x)`, `g⁺(x) ≤ c_g b(x)`, `Σ_y b(y) Q({y}|x,u) ≤ c_Q b(x)`. -/
def IsUpperBoundingFunctionChainFinite (Ch : MDChainFinite E U) (b : E → ℝ) (cr cg cQ : ℝ) :
    Prop :=
  Measurable b ∧ (∀ x, 0 ≤ b x) ∧ 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ cQ ∧
    (∀ x u, max (Ch.r (x, u)) 0 ≤ cr * b x) ∧
    (∀ x, max (Ch.g x) 0 ≤ cg * b x) ∧
    ∀ x u, (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)) ≤ ENNReal.ofReal (cQ * b x)

end MDPFinance.PDMDP


