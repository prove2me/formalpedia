-- Prove2me | Definitions.Def_DisclosureStatics_Aggregation_Model
-- name    : DisclosureStatics_Aggregation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:44.405028+00:00
-- url     : https://prove2.me/theorems/13e51fd3-3ecb-4e55-95ac-e1687e1877d3
-- title:
--   §2, pp. 9–16 and Assumptions 1–2, p. 17 — PDS, SASEU utility, budget, insurer loss, one-step aggregation, (DP-π), (DP-B), FOCs
-- statement:
--   This file sets up the insurance model of Burkovskaya and Li.
--
--   **Market.** There are finitely many states of the world $\Omega=\{s_1,\dots,s_n\}$; $s_1$ is the default state in which no accident occurs. Each state $s_i$ has a probability $P(s_i)$, an Arrow price $p_i$, and a loss $l_i$; the consumer has income $I$. The *standing assumptions* are $P(s_i)>0$, $\sum_i P(s_i)=1$, $p_i>0$ and $\sum_i p_i=1$; the last one is the paper's normalization $p_1=1-\sum_{i\ge 2}p_i$, with $p_1>0$. For an event $S\subseteq\Omega$ write $P(S)=\sum_{s_i\in S}P(s_i)$, $p_S=\sum_{s_i\in S}p_i$ and $r_S=p_S/P(S)$ (the probability-adjusted price); for a single state $r_i=p_i/P(s_i)$, in particular $r_1=r_{\{s_1\}}$.
--
--   **Utility.** The vNM index of Assumption 1 is the CARA function
--   $$u(x)=\frac{1-e^{-\gamma x}}{\gamma},\qquad \gamma>0,$$
--   whose range is $(-\infty,1/\gamma)$. The aggregation function $\varphi$ is *regular* on a set $D$ if it is $C^3$ on $D$ with $\varphi'>0$ there; it is *aggregation averse in the sense of Assumption 2* on $D$ if moreover $\varphi''<0$ on $D$ and the absolute aggregation aversion $A_\varphi=-\varphi''/\varphi'$ is non-increasing on $D$ ("CARA or DARA").
--
--   **Disclosure statements.** A product disclosure statement (PDS) $\pi$ is a partition of $\Omega$ into nonempty events in which $\{s_1\}$ is a block. For a consumption bundle $c=(c_i)_{s_i\in\Omega}$ — with $s=c(s_1)$ the consumption in the default state and $d_i=s-c_i$ the deductible in state $s_i$ — the value of event $S$ is $V_S(c)=\sum_{s_i\in S}P(s_i\mid S)\,u(c_i)$ and the SASEU utility is
--   $$U(c;\pi)=\sum_{S\in\pi}P(S)\,\varphi\bigl(V_S(c)\bigr).$$
--
--   **Budget and loss.** The budget constraint is $s+\sum_{i\ge2}(l_i-d_i)p_i=I$, and the insurer's expected loss is $L=\sum_{i\ge 2}d_i\,(p_i-P(s_i))$.
--
--   **Problems.** $c$ solves (DP-$\pi$) if it satisfies the budget and maximizes $U(\cdot;\pi)$ over all bundles satisfying the budget. Given such a $c$ and an event $B$, $c^*$ solves the intermediate problem (DP-B) if $c^*=c$ off $B$, $\sum_{s_i\in B}p_ic^*_i=\sum_{s_i\in B}p_ic_i$, and $c^*$ maximizes $P(B)\varphi(V_B(\cdot))$ among all bundles with these two properties. The first-order conditions (1)/(2) with multiplier $\lambda$ read $\varphi'(V_S(c))\,u'(c_i)=\lambda r_i$ for all $S\in\pi$ and $s_i\in S$; condition (3) reads $\varphi'(V_B(c^*))\,u'(c^*_i)=\lambda r_i$ for $s_i\in B$.
--
--   **One-step aggregation.** $B$ is a *merged event* of $\pi$ if it is the union of a family $\mathcal S$ of at least two events of $\pi$, none of which is $\{s_1\}$; $\rho$ is the *one-step aggregation* of $\pi$ along $\mathcal S$ if its events are $B$ together with the events of $\pi$ not in $\mathcal S$.
--
--   These are the objects of every result in the mission.
--
--   **Formalization Note** States are a `Fintype`; a PDS is a `Finpartition` of `univ` (whose parts are nonempty by construction). The paper's choice variables $(s,d_2,\dots,d_n)$ are encoded by the consumption bundle $c$ through $s=c(s_1)$, $d_i=s-c_i$, as the paper itself does on p. 13; the budget and the loss are written in the paper's $(s,d)$ form through this substitution, not simplified. $u$ is a parameter of the model (Assumption 1 is imposed in the theorems as $u=$ `cara γ`); $\varphi$ is a function $\mathbb R\to\mathbb R$ and every hypothesis on it is imposed on the open set $(-\infty,1/\gamma)=u(\mathbb R)$, the only place where $U$ evaluates it. Derivatives are Mathlib's `deriv`. The p. 17 phrase "non-decreasing absolute aggregation aversion" is read as non-increasing $A_\varphi$, which is what "CARA or DARA" means. Solutions and multipliers are predicates (`IsDemand`, `IsIntermediate`, `IsFOC`, `IsFOCB`), not constructed objects.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), pp. 9–17, §2.1–§2.5, eqs. (1)–(3), Assumptions 1–2

import Mathlib

namespace DisclosureStatics.Aggregation

open Finset

noncomputable section

/-- The primitives of the insurance market (Burkovskaya–Li, §2.1–2.4, pp. 9–13): the default
state `s₁` (no accident), the state probabilities `P i = P(sᵢ)`, the Arrow prices `p i = pᵢ`
(with `p s₁ = p₁ := 1 - ∑_{i ≥ 2} pᵢ`, p. 13), the losses `l i = lᵢ`, and income `I`. -/
structure Market (Ω : Type*) where
  s₁ : Ω
  P : Ω → ℝ
  p : Ω → ℝ
  l : Ω → ℝ
  I : ℝ

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Standing assumptions of §2: every state has positive probability and the probabilities sum
to one; every Arrow price is positive and the prices sum to one (this is p. 13's normalization
`p₁ = 1 - ∑_{i=2}^n pᵢ`, with `p₁ > 0`). -/
def Market.Standing (M : Market Ω) : Prop :=
  (∀ i, 0 < M.P i) ∧ ∑ i, M.P i = 1 ∧ (∀ i, 0 < M.p i) ∧ ∑ i, M.p i = 1

/-- Probability of an event, `P(S) = ∑_{sᵢ ∈ S} P(sᵢ)`. -/
def probE (M : Market Ω) (S : Finset Ω) : ℝ := ∑ i ∈ S, M.P i

/-- Price of the security paying `$1` in every state of `S`, `p_S = ∑_{sᵢ ∈ S} pᵢ` (p. 17). -/
def priceE (M : Market Ω) (S : Finset Ω) : ℝ := ∑ i ∈ S, M.p i

/-- Probability-adjusted price of event `S`, `r_S = p_S / P(S)` (p. 17); for a single state
`rE M {sᵢ} = rᵢ = pᵢ / P(sᵢ)` (p. 13), in particular `r₁ = rE M {M.s₁}`. -/
def rE (M : Market Ω) (S : Finset Ω) : ℝ := priceE M S / probE M S

/-- The CARA vNM utility index of Assumption 1 (p. 17): `u(x) = (1 - e^{-γx}) / γ`. -/
def cara (γ x : ℝ) : ℝ := (1 - Real.exp (-γ * x)) / γ

/-- Standing regularity of the aggregation function `φ` on a set `D` (p. 10: `φ` increasing and
three times differentiable): `φ` is `C³` on `D` with `φ' > 0` on `D`. -/
def Regular (φ : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ContDiffOn ℝ 3 φ D ∧ ∀ v ∈ D, 0 < deriv φ v

/-- Assumption 2 for an aggregation-averse consumer (pp. 11–12, 17, and the proof of Lemma 1,
p. 40): `φ` is regular on `D`, strictly concave there (`φ'' < 0`), and its absolute aggregation
aversion `A_φ = -φ''/φ'` is non-increasing on `D` ("CARA or DARA"). -/
def AggregationAverse (φ : ℝ → ℝ) (D : Set ℝ) : Prop :=
  Regular φ D ∧ (∀ v ∈ D, deriv (deriv φ) v < 0) ∧
    AntitoneOn (fun v => -deriv (deriv φ) v / deriv φ v) D

/-- A product disclosure statement (PDS): a partition of the state space into events. -/
abbrev PDS (Ω : Type*) [Fintype Ω] [DecidableEq Ω] := Finpartition (univ : Finset Ω)

/-- `π` is a PDS of the market: the default state `s₁` forms a block of its own (p. 9, p. 13). -/
def IsPDS (M : Market Ω) (π : PDS Ω) : Prop := {M.s₁} ∈ π.parts

/-- The value of event `S` at consumption bundle `c`,
`V_S(c) = ∑_{sᵢ ∈ S} P(sᵢ | S) u(cᵢ)` (p. 14). -/
def V (M : Market Ω) (u : ℝ → ℝ) (S : Finset Ω) (c : Ω → ℝ) : ℝ :=
  ∑ i ∈ S, (M.P i / probE M S) * u (c i)

/-- The SASEU utility of consumption bundle `c` under PDS `π` (p. 10):
`U(c; π) = ∑_{S ∈ π} P(S) φ(V_S(c))`; the block `{s₁}` contributes `P(s₁) φ(u(s))`. -/
def U (M : Market Ω) (u φ : ℝ → ℝ) (π : PDS Ω) (c : Ω → ℝ) : ℝ :=
  ∑ S ∈ π.parts, probE M S * φ (V M u S c)

/-- The budget constraint `s + ∑_{i=2}^n (lᵢ - dᵢ) pᵢ = I` (p. 10), written for the consumption
bundle `c` with `s = c s₁` and deductibles `dᵢ = s - cᵢ` (p. 13). -/
def Budget (M : Market Ω) (c : Ω → ℝ) : Prop :=
  c M.s₁ + ∑ i ∈ univ.erase M.s₁, (M.l i - (c M.s₁ - c i)) * M.p i = M.I

/-- The insurer's expected loss `L = ∑_{i=2}^n dᵢ (pᵢ - P(sᵢ))` (p. 12, p. 13), with
`dᵢ = c s₁ - cᵢ`. -/
def Loss (M : Market Ω) (c : Ω → ℝ) : ℝ :=
  ∑ i ∈ univ.erase M.s₁, (c M.s₁ - c i) * (M.p i - M.P i)

/-- `c` solves the insurance demand problem (DP-π) (p. 11): it satisfies the budget and
maximizes `U(·; π)` over the budget set. -/
def IsDemand (M : Market Ω) (u φ : ℝ → ℝ) (π : PDS Ω) (c : Ω → ℝ) : Prop :=
  Budget M c ∧ ∀ c', Budget M c' → U M u φ π c' ≤ U M u φ π c

/-- `cs` (the paper's `c*`) solves the intermediate problem (DP-B) (p. 16) given the (DP-π)
solution `c`: consumption off `B` (including `s* = s`) is kept, the expenditure on `B` is kept,
`∑_{sᵢ ∈ B} pᵢ (s - d*ᵢ) = ∑_{sᵢ ∈ B} pᵢ (s - dᵢ)`, and `P(B) φ(V_B(·))` is maximized. -/
def IsIntermediate (M : Market Ω) (u φ : ℝ → ℝ) (B : Finset Ω) (c cs : Ω → ℝ) : Prop :=
  (∀ i ∉ B, cs i = c i) ∧ ∑ i ∈ B, M.p i * cs i = ∑ i ∈ B, M.p i * c i ∧
    ∀ c' : Ω → ℝ, (∀ i ∉ B, c' i = c i) → ∑ i ∈ B, M.p i * c' i = ∑ i ∈ B, M.p i * c i →
      probE M B * φ (V M u B c') ≤ probE M B * φ (V M u B cs)

/-- The first-order conditions (1) (p. 13) — and, for `π := ρ`, (2) (p. 14) — with multiplier
`lam`: `φ'(V_{S}(c)) u'(cᵢ) = lam · rᵢ` for every event `S ∈ π` and `sᵢ ∈ S`. -/
def IsFOC (M : Market Ω) (u φ : ℝ → ℝ) (π : PDS Ω) (c : Ω → ℝ) (lam : ℝ) : Prop :=
  ∀ S ∈ π.parts, ∀ i ∈ S, deriv φ (V M u S c) * deriv u (c i) = lam * (M.p i / M.P i)

/-- The first-order conditions (3) (p. 16) of (DP-B) with multiplier `lam`:
`φ'(V_B(c*)) u'(c*ᵢ) = lam · rᵢ` for every `sᵢ ∈ B`. -/
def IsFOCB (M : Market Ω) (u φ : ℝ → ℝ) (B : Finset Ω) (cs : Ω → ℝ) (lam : ℝ) : Prop :=
  ∀ i ∈ B, deriv φ (V M u B cs) * deriv u (cs i) = lam * (M.p i / M.P i)

/-- `B` is the union of a family `𝒮` of at least two events of `π`, none of them the default
block `{s₁}` (p. 13: "event `B` is the union of `S_k, …, S_t` (`k < t`)", "`s₁` cannot be
aggregated with any other states"). -/
def IsMergedEvent (M : Market Ω) (π : PDS Ω) (𝒮 : Finset (Finset Ω)) (B : Finset Ω) : Prop :=
  𝒮 ⊆ π.parts ∧ 2 ≤ 𝒮.card ∧ {M.s₁} ∉ 𝒮 ∧ B = 𝒮.sup id

/-- One-step aggregation (p. 13): `ρ` is obtained from `π` by merging the events of `𝒮` into the
single event `B`, `ρ = (π \ 𝒮) ∪ {B}`. -/
def IsOneStepAggregation (M : Market Ω) (π ρ : PDS Ω) (𝒮 : Finset (Finset Ω))
    (B : Finset Ω) : Prop :=
  IsMergedEvent M π 𝒮 B ∧ ρ.parts = insert B (π.parts \ 𝒮)

end

end DisclosureStatics.Aggregation


