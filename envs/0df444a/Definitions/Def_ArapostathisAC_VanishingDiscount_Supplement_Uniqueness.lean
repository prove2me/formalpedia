-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Uniqueness
-- name    : ArapostathisAC_VanishingDiscount_Supplement_Uniqueness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:03:42.840715+00:00
-- url     : https://prove2.me/theorems/643279dd-2cbe-4952-b6f5-518c87cc49fa
-- title:
--   Stability under local perturbations (Assumption 5.21), the return potential (5.20) and the Lyapunov condition of Theorem 5.12
-- statement:
--   On the countable-state model of §5.3, with $\tau=\min\{t\ge1:X_t=0\}$:
--
--   1. $f\in\Pi_{SSD}$ has **finite average cost** if it is stable with $\rho(f)=\int c\,d\hat\eta(f)<\infty$. **Assumption 5.21**: if $f\in\Pi_{SSD}$ has $\rho(f)<\infty$, every $f'\in\Pi_{SD}$ obtained by changing $f$ at finitely many states is stable with $\rho(f')<\infty$.
--   2. The **return potential (5.20)** of $f_0\in\Pi_{SD}$ and $\rho^*$:
--   $$h(i)=E^{f_0}_i\Big[\sum_{t=0}^{\tau-1}\big(c(X_t,f_0(X_t))-\rho^*\big)\Big]=E^{f_0}_i\Big[\sum_{t<\tau}c(X_t,f_0(X_t))\Big]-\rho^*E^{f_0}_i[\tau].$$
--   3. The **Lyapunov condition** for $w:S\to\mathbb R_+$, a finite $B\subset S$ and $\varepsilon>0$: (a) $0\in B$ and $\{i\notin B:P(j\mid i,a)>0\text{ for some }j\in B,a\in A\}$ is finite; (b) $w(i)\to\infty$; (c) $\sum_jP(j\mid i,a)w(j)+\varepsilon\le w(i)$ for $i\notin B$, $a\in A$; (d) a random variable $Z$ (through its law $\zeta$) and $\lambda>0$ with $E[e^{\lambda Z}]<\infty$ and $P(\{j:|w(j)-w(i)|>b\}\mid i,a)\le P(Z>b)$ for all $i$, $a$ and $b\ge0$.
--
--   **Formalization Note** The two expectations in (5.20) are computed in $[0,\infty]$ and converted to reals; the theorem using $h$ assumes both are finite. Conditions (c) and (d) are printed as conditional statements under every policy $\pi$, initial law $\mu$ and time $t$; since the conditioning includes $(X_t,A_t)$ and every pair $(i,a)$ can occur, they are equivalent to the one-step forms stated here.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 314, (5.20), Assumption 5.21 and Theorem 5.12 (a)–(d)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

open ArapostathisAC.VanishingDiscount

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- `f ∈ Π_SSD` has finite average cost `ρ(f) = ∫ c dη̂(f) < ∞` (p. 312): its chain is stable and
has an invariant probability vector `η` with `∫ c dη̂(f) < ∞`. -/
def HasFiniteRho (M : CMP A) (g : StationaryPolicy M) : Prop :=
  IsStableR M (RandRule.ofDet g) ∧ ∃ η, IsInvariantProb M (RandRule.ofDet g) η ∧
    ∫⁻ p, ENNReal.ofReal (M.c p.1 p.2) ∂(occ (RandRule.ofDet g) η) < ⊤

/-- Assumption 5.21 (stability under local perturbations, p. 314): for every `f ∈ Π_SSD` with
`ρ(f) < ∞`, every `f' ∈ Π_SD` obtained from `f` by changing the actions at finitely many states is
also stable and has `ρ(f') < ∞`. -/
def Assumption521 (M : CMP A) : Prop :=
  ∀ g g' : StationaryPolicy M, HasFiniteRho M g → {i | g'.1 i ≠ g.1 i}.Finite → HasFiniteRho M g'

/-- `E^f_i[∑_{t=0}^{τ-1} c(X_t, f(X_t))]` with `τ = min {t ≥ 1 : X_t = 0}`, in `[0, ∞]`. -/
noncomputable def costToReturn (M : CMP A) (g : StationaryPolicy M) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < returnTime 0 ω then ENNReal.ofReal (M.c (ω t).1 (ω t).2) else 0)
    ∂(pathMeasure M g.toPolicy i)

/-- `E^f_i[τ]`, `τ = min {t ≥ 1 : X_t = 0}`, in `[0, ∞]`. -/
noncomputable def meanReturn0 (M : CMP A) (g : StationaryPolicy M) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ((returnTime 0 ω : ℕ∞) : ℝ≥0∞) ∂(pathMeasure M g.toPolicy i)

/-- The function (5.20) (p. 314), `h(i) = E^{f₀}_i[∑_{t=0}^{τ-1} (c(X_t, f₀(X_t)) − ρ*)]`, computed as
`E[∑_{t<τ} c] − ρ* E[τ]`; it is the paper's `h` when both expectations are finite. -/
noncomputable def returnPotential (M : CMP A) (g : StationaryPolicy M) (ρs : ℝ) (i : ℕ) : ℝ :=
  (costToReturn M g i).toReal - ρs * (meanReturn0 M g i).toReal

/-- The Lyapunov condition of Theorem 5.12 (p. 314), for `w : S → ℝ₊`, a finite `B ⊂ S` and
`ε > 0`:
(a) `0 ∈ B` and `{i ∉ B : P(j | i, a) > 0 for some j ∈ B, a ∈ A}` is finite;
(b) `w(i) → ∞` as `i → ∞`;
(c) `E^π_μ[(w(X_{t+1}) − w(X_t) + ε) I{X_t ∉ B} | 𝔉_t] ≤ 0` for every `π`, `μ`, `t`, stated in
the equivalent one-step form `∑_j P(j | i, a) w(j) + ε ≤ w(i)` for all `i ∉ B`, `a ∈ A`;
(d) there are a random variable `Z` (here: its law `ζ` on `ℝ`) and `λ > 0` with
`E[exp(λZ)] < ∞` and `𝒫^π_μ(|w(X_{t+1}) − w(X_t)| > b | 𝔉_t) ≤ P(Z > b)` for all `b ≥ 0`, stated in
the equivalent one-step form `P({j : |w(j) − w(i)| > b} | i, a) ≤ ζ((b, ∞))` for all `i`, `a`. -/
def Lyapunov512 (M : CMP A) (w : ℕ → ℝ) (B : Set ℕ) (ε : ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ B.Finite ∧ 0 < ε ∧
  (0 ∈ B ∧ {i | i ∉ B ∧ ∃ j ∈ B, ∃ a : A, 0 < prob M i a j}.Finite) ∧
  Tendsto w atTop atTop ∧
  (∀ i, i ∉ B → ∀ a : A,
    ∑' j, M.P (i, a) {j} * ENNReal.ofReal (w j) + ENNReal.ofReal ε ≤ ENNReal.ofReal (w i)) ∧
  ∃ ζ : Measure ℝ, IsProbabilityMeasure ζ ∧ ∃ lam : ℝ, 0 < lam ∧
    ∫⁻ z, ENNReal.ofReal (Real.exp (lam * z)) ∂ζ < ⊤ ∧
    ∀ (i : ℕ) (a : A) (b : ℝ), 0 ≤ b → M.P (i, a) {j | b < |w j - w i|} ≤ ζ (Set.Ioi b)

end ArapostathisAC.VanishingDiscount.Supplement


