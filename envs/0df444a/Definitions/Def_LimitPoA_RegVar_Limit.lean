-- Prove2me | Definitions.Def_LimitPoA_RegVar_Limit
-- name    : LimitPoA_RegVar_Limit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:57.641783+00:00
-- url     : https://prove2.me/theorems/0d0351f6-da1d-4876-a666-36d8c91041f2
-- title:
--   §3.1, pp. 11–14 — scaled games (Definition 3.1), domains I_a, regular sequences, limit games (Definition 3.2), scalable sequences (Definition 3.3)
-- statement:
--   This file defines the scaling and limit machinery of §3.1 for a game $\Gamma$ and for its subgames $\Gamma_{|\mathcal K'}$, $\mathcal K' \subseteq \mathcal K$ (Definition 3.4).
--
--   **Subgames.** The demand vector $d_{|\mathcal K'}$ of the subgame is represented by the demand vector of $\Gamma$ that agrees with $d$ on $\mathcal K'$ and vanishes outside $\mathcal K'$ (as in Appendix A.6). A resource is *relevant* for $\Gamma_{|\mathcal K'}$ if it lies in a strategy of some group of $\mathcal K'$.
--
--   **Scaled game (Definition 3.1, p. 11).** For a demand $d$ and a constant $g > 0$ the scaled cost functions are $\tau^{[g]}_a(x) = \tau_a(T(d)\cdot x)/g$, and the scaled game has demand $d/T(d)$.
--
--   **Domains (p. 12).** The consumption domain $I_a$ of resource $a$ is the set of all consumption rates $f_a/T(d)$ over all demand vectors $d$ of the (sub)game with $T(d) > 0$ and all profiles $f$ for $d$.
--
--   **Regular sequences (pp. 12–13).** An unbounded sequence $(d^{(n)})$ is regular if $\lim_n d^{(n)}_k \in [0,\infty]$ exists for each $k$ and the limit distribution $d^{(\infty)}_k = \lim_n d^{(n)}_k/T(d^{(n)}) \in [0,1]$ exists for each $k$.
--
--   **Limit game (Definition 3.2, p. 13).** Given a regular sequence with limit distribution $d^{(\infty)}$ and scaling constants $g_n > 0$, the functions $\tau^{(\infty)}_a : I_a \to [0,\infty]$ define the limit game $\Gamma^{(\infty)} = \lim_{d^{(n)}\to\infty}\Gamma^{[g_n]}$ if:
--
--   1. (L1) $\tau^{(\infty)}_a(x) = \lim_n \tau_a(T(d^{(n)})\cdot x)/g_n \in [0,\infty]$ for each $x \in I_a\setminus\{0\}$, and $\tau^{(\infty)}_a(0) = \lim_{x\to 0^+}\tau^{(\infty)}_a(x)$ if $0 \in I_a$;
--   2. (L2) each $\tau^{(\infty)}_a$ is either the constant $\infty$ or finite and continuous on $I_a$;
--   3. (L3) each group has a *tight* strategy, all of whose resources have finite continuous limit costs on their domains;
--   4. (L4) NE profiles of $\Gamma^{(\infty)}$ have positive cost, and $\mathrm{PoA}(d^{(\infty)}) = 1$ in $\Gamma^{(\infty)}$.
--
--   In $\Gamma^{(\infty)}$ the strategy cost is $\tau^{(\infty)}_s(f) = \sum_{a\in s}\tau^{(\infty)}_a(f_a)$ and the cost is $C_{\Gamma^{(\infty)}}(f) = \sum_a f_a\,\tau^{(\infty)}_a(f_a)$, with the convention $0\cdot\infty = 0$ (p. 14).
--
--   **Scalable sequences (Definition 3.3, p. 14).** A regular sequence is scalable if there is a scaling sequence $(g_n)$ and a limit game $\Gamma^{(\infty)} = \lim_{d^{(n)}\to\infty}\Gamma^{[g_n]}$.
--
--   **Formalization Note** Every notion takes the group set $\mathcal K'$ of the subgame as a parameter ($\mathcal K' = \mathcal K$ for $\Gamma$ itself); conditions (L1)–(L3) range over the relevant resources and the groups of $\mathcal K'$, and the domains use demand vectors supported on $\mathcal K'$. Demand vectors in the domain may have zero entries ($d \ge 0$, $T(d) > 0$); with this reading $I_a$ is the closed interval the paper asserts in (3.1). Limit costs take values in $[0,\infty]$ (`ℝ≥0∞`), where $0\cdot\infty = 0$ is built in; real ratios enter through `ENNReal.ofReal`. Condition (L4) is encoded as: an NE profile of $\Gamma^{(\infty)}$ exists, and every NE profile has cost in $(0,\infty)$ and is an SO profile of $\Gamma^{(\infty)}$ (so worst NE cost = SO cost, i.e. $\mathrm{PoA}(d^{(\infty)}) = 1$). The limit $x\to 0^+$ is the right-neighbourhood filter at $0$; for a relevant resource $I_a$ is an interval containing $1$, so $0 \in I_a$ forces $[0,1] \subseteq I_a$ and this is the paper's one-sided limit within $I_a$. Scaled costs are functions on $\mathbb R$; only arguments in $[0,1]$ (consumption rates) enter.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, pp. 11–14, Definition 3.1, domain I_a and (3.1) (p. 12), regular sequences (pp. 12–13), Definition 3.2 (L1)–(L4), Definition 3.3; subgames, Definition 3.4 and p. 19

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model

namespace LimitPoA.RegVar

open Filter Topology KellyStochasticNetworks ENNReal

variable (Γ : Game)

/-- The demand vector `d|K′` of the subgame `Γ|K′` (Definition 3.4), padded with zeros outside `K′`:
the demand vector of `Γ` that coincides with the subgame (Appendix A.6). -/
def restrict (K' : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ) : Fin Γ.Sd → ℝ :=
  fun k => if k ∈ K' then d k else 0

/-- p. 19: a resource is relevant for the subgame `Γ|K′` if it lies in a strategy of a group of `K′`. -/
def IsRelevant (K' : Finset (Fin Γ.Sd)) (a : Fin Γ.J) : Prop :=
  ∃ s, Γ.grp s ∈ K' ∧ Γ.inc a s = 1

/-- p. 12: the consumption domain `I_a` of resource `a` in the subgame `Γ|K′`: all consumption rates
`f_a / T(d)` of profiles `f` for demand vectors `d ≥ 0` of the subgame with `T(d) > 0`. -/
def domain (K' : Finset (Fin Γ.Sd)) (a : Fin Γ.J) : Set ℝ :=
  {x | ∃ (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ), (∀ k, 0 ≤ d k) ∧ (∀ k, k ∉ K' → d k = 0) ∧
    0 < totalDemand Γ d ∧ IsProfile Γ d f ∧ x = load Γ f a / totalDemand Γ d}

/-- Definition 3.1, p. 11: the scaled cost functions `τ_a^[g](x) = τ_a(T(d)·x)/g`, for the total
demand `T = T(d)` and the scaling factor `g`. -/
noncomputable def scaled (τ : Fin Γ.J → ℝ → ℝ) (T g : ℝ) : Fin Γ.J → ℝ → ℝ :=
  fun a x => τ a (T * x) / g

/-- pp. 12–13: a regular sequence with limit distribution `dInf`: unbounded, every `d_k^(n)` has a
limit in `[0, ∞]`, and `d_k^(n)/T(d^(n)) → dInf k`. -/
def IsRegular (d : ℕ → Fin Γ.Sd → ℝ) (dInf : Fin Γ.Sd → ℝ) : Prop :=
  IsUnbounded Γ d ∧
    (∀ k, Tendsto (fun n => d n k) atTop atTop ∨ ∃ L : ℝ, Tendsto (fun n => d n k) atTop (𝓝 L)) ∧
    ∀ k, Tendsto (fun n => d n k / totalDemand Γ (d n)) atTop (𝓝 (dInf k))

/-- Limit strategy cost `τ_s^(∞)(f) = Σ_{a ∈ s} τ_a^(∞)(f_a)`, valued in `[0, ∞]`. -/
noncomputable def limStratCost (τInf : Fin Γ.J → ℝ → ℝ≥0∞) (f : Fin Γ.R → ℝ) (s : Fin Γ.R) : ℝ≥0∞ :=
  ∑ a, if Γ.inc a s = 1 then τInf a (load Γ f a) else 0

/-- Limit social cost `C_{Γ^(∞)}(f) = Σ_a f_a · τ_a^(∞)(f_a)` in `[0, ∞]`, with `0 · ∞ = 0` (p. 14). -/
noncomputable def limCost (τInf : Fin Γ.J → ℝ → ℝ≥0∞) (f : Fin Γ.R → ℝ) : ℝ≥0∞ :=
  ∑ a, ENNReal.ofReal (load Γ f a) * τInf a (load Γ f a)

/-- An NE profile of the limit game for the demand `dInf`. -/
def IsLimNE (τInf : Fin Γ.J → ℝ → ℝ≥0∞) (dInf : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) : Prop :=
  IsProfile Γ dInf f ∧ ∀ s s' : Fin Γ.R, Γ.grp s' = Γ.grp s → 0 < f s →
    limStratCost Γ τInf f s ≤ limStratCost Γ τInf f s'

/-- An SO profile of the limit game for the demand `dInf`. -/
def IsLimSO (τInf : Fin Γ.J → ℝ → ℝ≥0∞) (dInf : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) : Prop :=
  IsProfile Γ dInf f ∧ ∀ g, IsProfile Γ dInf g → limCost Γ τInf f ≤ limCost Γ τInf g

/-- (L2)/(L3): `τ_a^(∞)` is finite and continuous on the domain `I_a` of the subgame `Γ|K′`. -/
def IsFiniteContinuousOn (τInf : Fin Γ.J → ℝ → ℝ≥0∞) (K' : Finset (Fin Γ.Sd)) (a : Fin Γ.J) : Prop :=
  (∀ x ∈ domain Γ K' a, τInf a x ≠ ⊤) ∧ ContinuousOn (fun x => (τInf a x).toReal) (domain Γ K' a)

/-- Definition 3.2, p. 13: `τInf` with limit distribution `dInf` is the limit game of the subgame
`Γ|K′` for the regular sequence `d` (vanishing outside `K′`) and the scaling sequence `g`,
i.e. `Γ^(∞) = lim_{d^(n)→∞} Γ^[g_n]`. -/
structure IsLimitGame (τ : Fin Γ.J → ℝ → ℝ) (K' : Finset (Fin Γ.Sd)) (d : ℕ → Fin Γ.Sd → ℝ)
    (g : ℕ → ℝ) (dInf : Fin Γ.Sd → ℝ) (τInf : Fin Γ.J → ℝ → ℝ≥0∞) : Prop where
  /-- a scaling sequence of constants `g_n > 0` (Definition 3.1). -/
  scaling_pos : ∀ n, 0 < g n
  /-- the sequence is a demand sequence of the subgame `Γ|K′`. -/
  support : ∀ n k, k ∉ K' → d n k = 0
  /-- the sequence is regular with limit distribution `dInf`. -/
  regular : IsRegular Γ d dInf
  /-- (L1), `x ≠ 0`: `τ_a^(∞)(x) = lim_n τ_a(T(d^(n))·x)/g_n ∈ [0, ∞]` for `x ∈ I_a ∖ {0}`. -/
  L1 : ∀ a, IsRelevant Γ K' a → ∀ x ∈ domain Γ K' a, x ≠ 0 →
    Tendsto (fun n => ENNReal.ofReal (τ a (totalDemand Γ (d n) * x) / g n)) atTop (𝓝 (τInf a x))
  /-- (L1), `x = 0`: `τ_a^(∞)(0) = lim_{x→0+} τ_a^(∞)(x)` if `0 ∈ I_a`. -/
  L1_zero : ∀ a, IsRelevant Γ K' a → (0 : ℝ) ∈ domain Γ K' a →
    Tendsto (τInf a) (𝓝[>] 0) (𝓝 (τInf a 0))
  /-- (L2): `τ_a^(∞)` is the constant `∞` on `I_a`, or finite and continuous on `I_a`. -/
  L2 : ∀ a, IsRelevant Γ K' a →
    (∀ x ∈ domain Γ K' a, τInf a x = ⊤) ∨ IsFiniteContinuousOn Γ τInf K' a
  /-- (L3): every group of `K′` has a tight strategy. -/
  L3 : ∀ k ∈ K', ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → IsFiniteContinuousOn Γ τInf K' a
  /-- (L4): an NE profile of `Γ^(∞)` exists; NE profiles have positive finite cost and are SO
  profiles of `Γ^(∞)`, i.e. `PoA(d^(∞)) = 1`. -/
  L4 : (∃ f, IsLimNE Γ τInf dInf f) ∧ ∀ f, IsLimNE Γ τInf dInf f →
    0 < limCost Γ τInf f ∧ limCost Γ τInf f < ⊤ ∧ IsLimSO Γ τInf dInf f

/-- Definition 3.3, p. 14: the regular sequence `d` of the subgame `Γ|K′` is scalable if it has a
scaling sequence and a limit game. -/
def IsScalableSeq (τ : Fin Γ.J → ℝ → ℝ) (K' : Finset (Fin Γ.Sd)) (d : ℕ → Fin Γ.Sd → ℝ) : Prop :=
  ∃ (g : ℕ → ℝ) (dInf : Fin Γ.Sd → ℝ) (τInf : Fin Γ.J → ℝ → ℝ≥0∞), IsLimitGame Γ τ K' d g dInf τInf

end LimitPoA.RegVar


