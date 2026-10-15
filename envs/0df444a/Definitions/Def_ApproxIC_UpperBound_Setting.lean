-- Prove2me | Definitions.Def_ApproxIC_UpperBound_Setting
-- name    : ApproxIC_UpperBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:06.23624+00:00
-- url     : https://prove2.me/theorems/20a77e86-bf43-40ad-8ef7-9a292498a45d
-- title:
--   §2, Assumption 1, Definition 1 — single-buyer ε-IC mechanism design: density on [0, v̄], R, Ṙ, M(ε), Π, Π⋆, local α-power envelopes
-- statement:
--   This file sets up the single-buyer mechanism design model of Balseiro, Besbes and Castro with an approximately optimizing buyer.
--
--   **Values.** A seller sells one item to one buyer whose value $v$ is drawn from a distribution $F$ with density $f$ on $S=[0,\bar v]$. The standing assumptions (the density half of Assumption 1) are: $\bar v>0$, $f\ge 0$, $f=0$ off $S$, $f$ is integrable on $S$ and $\int_0^{\bar v} f(v)\,dv=1$. **Assumption 1** adds that $f$ has bounded variation on $S$. Write
--   $$F(v)=\int_0^v f(u)\,du,\qquad \bar F(v)=1-F(v),\qquad R(v)=v\,\bar F(v),\qquad \dot R(v)=\bar F(v)-v f(v).$$
--   $R(v)$ is the revenue of a posted price $v$, and $\dot R$ is its derivative wherever $f$ is continuous.
--
--   **Mechanisms.** A direct mechanism $m=(x,t)$ assigns to every report $v$ an allocation probability $x(v)\in[0,1]$ and a payment $t(v)$. It is feasible for problem $(P_\varepsilon)$ when
--   1. (IR) $v\,x(v)-t(v)\ge 0$ for all $v\in S$;
--   2. (IC$_\varepsilon$) $v\,x(v)-t(v)\ge v\,x(v')-t(v')-\varepsilon$ for all $v,v'\in S$.
--
--   $\mathcal M(\varepsilon)$ is the set of feasible mechanisms, $\Pi(m)=\mathbb E_v[t(v)]=\int_0^{\bar v}t(v)f(v)\,dv$ is the revenue, and $\Pi^\star(\mathcal M(\varepsilon))=\sup_{m\in\mathcal M(\varepsilon)}\Pi(m)$.
--
--   **Definition 1 (local $\alpha$-power envelopes).** $R$ admits local $\alpha$-power envelopes at $p^\star$ with constants $\alpha>1$, $\kappa_L,\kappa_U>0$ and radius $\ell>0$ if $p^\star\in(0,\bar v)$ is the unique maximizer of $R$ on $[0,\bar v]$, $\mathcal N_\ell=(p^\star-\ell,p^\star+\ell)\subset(0,\bar v)$, and
--   $$\kappa_L\alpha\,|v-p^\star|^\alpha\le (p^\star-v)\,\dot R(v)\le \kappa_U\alpha\,|v-p^\star|^\alpha\qquad\forall v\in\mathcal N_\ell .$$
--
--   These objects are the vocabulary of Theorem 1 and of every milestone of the mission.
--
--   **Formalization Note** Every function of the value is a total function $\mathbb R\to\mathbb R$; all conditions quantify over $S$ only. $\bar v>0$ is implied by the page ("$0\le\bar v<\infty$" with a density on $[0,\bar v]$). $\dot R$ is defined as $\bar F(v)-vf(v)$ rather than as a derivative of $R$, which a bounded-variation density does not guarantee everywhere; the paper itself uses $-\dot R(v)=vf(v)-\bar F(v)$ (p. 23). Mechanisms are required to be measurable (disclosed: $\mathbb E_v[t(v)]$ presumes it). $\Pi^\star$ is an `sSup`; its revenue image is nonempty and bounded above by $\bar v$. The existential constants of Definition 1 are parameters of the predicate.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), pp. 10–13, §2, (P_ε), M(ε), (1), Assumption 1, eq. (2), Definition 1

import Mathlib

/-!
# Single-buyer ε-IC mechanism design (Balseiro, Besbes, Castro, arXiv:2103.03403v2, §2, pp. 9–13)

A seller sells one item to one buyer whose value `v` has density `f` on `S = [0, v̄]`. Every function
of the value is a total function `ℝ → ℝ`; only its values on `S = Set.Icc 0 vbar` matter.
-/

namespace ApproxIC.UpperBound

open MeasureTheory

/-- The primitives of the model (§2, Assumption 1): the upper end `vbar` (the paper's `v̄`) of the
support `S = [0, v̄]` and the density `f` of the buyer's value distribution `F`. -/
structure Model where
  /-- The upper end `v̄` of the support `S = [0, v̄]`. -/
  vbar : ℝ
  /-- The density `f` of the value distribution. -/
  f : ℝ → ℝ

/-- The density half of Assumption 1 (p. 11): `0 < v̄`, `f ≥ 0`, `f` vanishes off `S = [0, v̄]`,
`f` is integrable on `S`, and `∫_0^{v̄} f = 1`. -/
def Model.Standing (M : Model) : Prop :=
  0 < M.vbar ∧ (∀ v, 0 ≤ M.f v) ∧ (∀ v ∉ Set.Icc 0 M.vbar, M.f v = 0) ∧
    IntegrableOn M.f (Set.Icc 0 M.vbar) ∧ ∫ v in (0)..M.vbar, M.f v = 1

/-- Assumption 1 (p. 11): the standing density assumptions, and `f` has bounded variation on `S`. -/
def Model.Assumption1 (M : Model) : Prop :=
  M.Standing ∧ BoundedVariationOn M.f (Set.Icc 0 M.vbar)

/-- The cumulative distribution function `F(v) = ∫_0^v f`. -/
noncomputable def cdf (M : Model) (v : ℝ) : ℝ := ∫ u in (0)..v, M.f u

/-- The survival function `F̄(v) = 1 − F(v)` (p. 12). -/
noncomputable def cdfBar (M : Model) (v : ℝ) : ℝ := 1 - cdf M v

/-- The revenue function `R(v) = v · F̄(v)` of a posted price `v` (p. 12). -/
noncomputable def R (M : Model) (v : ℝ) : ℝ := v * cdfBar M v

/-- `Ṙ(v) := F̄(v) − v · f(v)`, the derivative of `R` wherever `f` is continuous (p. 23 uses
`−Ṙ(v) = v f(v) − F̄(v)`). Deliberately not `deriv (R M)`. -/
noncomputable def Rdot (M : Model) (v : ℝ) : ℝ := cdfBar M v - v * M.f v

/-- A direct mechanism `(x, t)`: allocation probability `x(v)` and payment `t(v)` of a report `v`. -/
structure Mech where
  /-- The allocation probability `x`. -/
  x : ℝ → ℝ
  /-- The payment `t`. -/
  t : ℝ → ℝ

/-- `x` and `t` are measurable and `x : S → [0, 1]` ((P_ε), p. 10). -/
def IsMech (M : Model) (m : Mech) : Prop :=
  Measurable m.x ∧ Measurable m.t ∧ ∀ v ∈ Set.Icc 0 M.vbar, m.x v ∈ Set.Icc (0 : ℝ) 1

/-- (IR), p. 10: `v · x(v) − t(v) ≥ 0` for all `v ∈ S`. -/
def IR (M : Model) (m : Mech) : Prop :=
  ∀ v ∈ Set.Icc 0 M.vbar, 0 ≤ v * m.x v - m.t v

/-- (IC_ε), p. 10: `v · x(v) − t(v) ≥ v · x(v') − t(v') − ε` for all `v, v' ∈ S`. -/
def IC (M : Model) (ε : ℝ) (m : Mech) : Prop :=
  ∀ v ∈ Set.Icc 0 M.vbar, ∀ v' ∈ Set.Icc 0 M.vbar,
    v * m.x v' - m.t v' - ε ≤ v * m.x v - m.t v

/-- `M(ε)`, the feasible set of problem (P_ε) (p. 11). -/
def Mset (M : Model) (ε : ℝ) : Set Mech := {m | IsMech M m ∧ IR M m ∧ IC M ε m}

/-- The revenue `Π(m) = E_v[t(v)] = ∫_0^{v̄} t(v) f(v) dv`. -/
noncomputable def revenue (M : Model) (m : Mech) : ℝ := ∫ v in (0)..M.vbar, m.t v * M.f v

/-- `Π⋆(M(ε)) = sup_{m ∈ M(ε)} Π(m)` (p. 11). -/
noncomputable def optRev (M : Model) (ε : ℝ) : ℝ := sSup (revenue M '' Mset M ε)

/-- Definition 1 (p. 12), with its constants as parameters: `p⋆` is the unique maximizer of `R` on
`S` and interior, `α > 1`, `κ_L, κ_U, ℓ > 0`, `N_ℓ = (p⋆ − ℓ, p⋆ + ℓ) ⊆ (0, v̄)`, and
`κ_L α |v − p⋆|^α ≤ (p⋆ − v) Ṙ(v) ≤ κ_U α |v − p⋆|^α` on `N_ℓ`. -/
def LocalPowerEnvelope (M : Model) (pstar α κL κU ℓ : ℝ) : Prop :=
  pstar ∈ Set.Ioo 0 M.vbar ∧
  IsMaxOn (R M) (Set.Icc 0 M.vbar) pstar ∧
  (∀ p ∈ Set.Icc 0 M.vbar, R M p = R M pstar → p = pstar) ∧
  1 < α ∧ 0 < κL ∧ 0 < κU ∧ 0 < ℓ ∧
  Set.Ioo (pstar - ℓ) (pstar + ℓ) ⊆ Set.Ioo 0 M.vbar ∧
  ∀ v ∈ Set.Ioo (pstar - ℓ) (pstar + ℓ),
    κL * α * |v - pstar| ^ α ≤ (pstar - v) * Rdot M v ∧
    (pstar - v) * Rdot M v ≤ κU * α * |v - pstar| ^ α

end ApproxIC.UpperBound


