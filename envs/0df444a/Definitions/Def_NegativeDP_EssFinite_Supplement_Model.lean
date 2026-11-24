-- Prove2me | Definitions.Def_NegativeDP_EssFinite_Supplement_Model
-- name    : NegativeDP_EssFinite_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:50:46.694091+00:00
-- url     : https://prove2.me/theorems/65fda94a-566b-43ee-b46f-95dac91d258b
-- title:
--   §1(b), §3, §5, §6, §9 — positive bounded problem; D/P terminal returns, strong (p,ε)-optimality, conservation, excessive functions, N-stationarity, discounted switching policy
-- statement:
--   This file adds to Blackwell's published discounted model the objects that Strauch's discounted (D) and positive bounded (P) cases need and that no published definition provides.
--
--   **Common.** A Markov policy $\pi=(f_1,f_2,\dots)$ is **$N$-stationary** if $f_n=f$ for some measurable $f:S\to A$ and every $n\le N$; nothing is required of $f_n$ for $n>N$.
--
--   **Discounted case D.** The problem is Blackwell's: non-empty standard Borel spaces $S$, $A$, a probability kernel $q(\cdot\mid s,a)$, a bounded Borel return $r(s,a,t)$ and $0\le\beta<1$. Here $M(S)$ is the set of bounded Borel functions. For $v\in M(S)$ the $n$-stage return with terminal reward $v$ is
--
--   $$
--   I_n(\pi,v)(s_1)=e_\pi\Big[\sum_{j=1}^n\beta^{j-1}r(s_j,a_j,s_{j+1})+\beta^n v(s_{n+1})\Big].
--   $$
--
--   A policy $\pi$ is **$(p,\varepsilon)$-optimal** if $p\{I(\pi)\ge v^*-\varepsilon\}=1$, where $v^*=\sup_\sigma I(\sigma)$ is the supremum over all randomized history-dependent policies; the event is read in the completion of $p$. The operator $U$ of a Markov policy **conserves** $v\in M(S)$ if $Uv\ge v$, and $u$ is **excessive** for $U$ if $Uu\le u$. For the switching theorem, the **continuation return** of a policy $\sigma$ at a history $(s_1,a_1,\dots,s_n)$ is
--
--   $$
--   u_n(s_1,a_1,\dots,s_n)=\sum_{j=n}^\infty\beta^{j-1}\sigma_nq\cdots\sigma_jqr,
--   $$
--
--   and a policy $\pi$ **switches** between $\sigma$ and $\tau$ if at every stage it uses $\sigma_n$ on $B_n=\{u_n>v_n\}$ ($v_n$ the continuation return of $\tau$) and $\tau_n$ on the complement.
--
--   **Positive bounded case P.** The data are the same spaces and law of motion, a bounded Borel return $r\ge0$, and $\beta=1$; in addition the expected return of every policy at every state is at most $R$, a positive number independent of the policy. The objects are the total return $I(\pi)=\sum_n\pi_1q\cdots\pi_nqr$, the $n$-stage return $I_n(\pi,v)$ with terminal reward $v\in M(S)$, the optimal return $v^*=\sup_\pi I(\pi)$, the operators
--
--   $$
--   Tu(s)=\int r(s,f(s),t)+u(t)\,dq(t\mid s,f(s)),\qquad T_au(s)=\int r(s,a,t)+u(t)\,dq(t\mid s,a),\qquad Uu=\sup_n T_nu,
--   $$
--
--   excessive functions and $(p,\varepsilon)$-optimality, all as in the discounted case with $\beta=1$.
--
--   These definitions are the substrate of the discounted and positive bounded cases of Theorems 4.1–9.3 of the paper; the negative case uses the published `NegativeDP` definitions.
--
--   **Formalization Note** Stages are numbered from $0$ in Lean: Blackwell's `Hist S A n` is the paper's $H_{n+1}$ and Lean stage $j$ is the paper's stage $j+1$, so $\beta^{j-1}$ becomes `P.β ^ j` and the $k$-th term of $u_n$ at Lean decision $n$ carries `P.β ^ (n + k)`. In case P the return is first computed in $[0,\infty]$ (a sum of lower Lebesgue integrals of $r\ge0$), the uniform bound $R$ is imposed on that value, and `Pos.I` is its real value, which is exact because of the bound. In both cases the history and stage laws are Blackwell's (`historyLaw`, `stageLaw`); for case P they are taken from the same data viewed as a Blackwell problem with $\beta=0$, which changes nothing because these laws depend only on $q$ and the policy. The continuation kernels of the switching policy are those of the published switching model, applied to the law of motion with the zero return (`Disc.lawOnly`); again only $q$ enters. $(p,\varepsilon)$-optimality is the almost-everywhere statement `∀ᵐ s ∂p`, which is the completion reading of the paper. Bochner integrals are used only for bounded functions that are measurable for the measure in question.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 872 (§1(b)), pp. 874–875 (§3), pp. 878–879 (§5), pp. 881–883 (§6), p. 888 (Theorem 9.3)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_Switching_Model

namespace NegativeDP.EssFinite.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- `N`-stationarity (p. 883): the Markov plan `π = (f₁, f₂, …)` has `fₙ = f` for some `f` and
all `n ≤ N`. Lean rules are numbered from `0`, so the condition is on `π 0, …, π (N - 1)`;
nothing is required of the tail. -/
def IsNStationary (π : MarkovPlan S A) (N : ℕ) : Prop :=
  ∃ f : {g : S → A // Measurable g}, ∀ k < N, π k = f

/-! ### The discounted case D: additions to Blackwell's published model -/

namespace Disc

open DiscountedDP.Stationary (Problem I historyLaw stageReward U optReturn IsBM)

/-- `Iₙ(π, v)(s) = e_π[Σ_{j=1}^n β^{j−1} r(sⱼ, aⱼ, sⱼ₊₁) + βⁿ v(sₙ₊₁)]` (p. 875), discounted
case, for a bounded Borel terminal reward `v`. Lean stage `j` is the paper's stage `j + 1`. -/
noncomputable def In (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (v : S → ℝ)
    (s : S) : ℝ :=
  (∑ j ∈ Finset.range n, P.β ^ j * stageReward P π s j) +
    P.β ^ n * ∫ h, v h.2 ∂historyLaw P π s n

/-- Strauch's `(p, ε)`-optimality (p. 875): `p{I(π) ≥ sup_σ I(σ) − ε} = 1`, the set read in the
completion of `p` (an almost-everywhere statement). This is one comparison with the optimal
return, stronger than Blackwell's `IsPOptimal`. -/
def IsStrongPEOptimal (P : Problem S A) (p : Measure S) (ε : ℝ) (π : Plan (S := S) (A := A)) :
    Prop :=
  ∀ᵐ s ∂p, optReturn P s - ε ≤ I P π s

/-- `U` conserves `v ∈ M(S)` (p. 881): `v` is bounded Borel and `Uv ≥ v`. -/
def Conserves (P : Problem S A) (π : MarkovPlan S A) (v : S → ℝ) : Prop :=
  IsBM v ∧ ∀ s, v s ≤ U P π v s

/-- `u` is excessive for `U` (p. 883): `Uu ≤ u`. -/
def IsExcessive (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ) : Prop :=
  ∀ s, U P π u s ≤ u s

/-- The law of motion of `P` with the zero return, as a negative problem: used only for the
reward-independent continuation kernels of the published switching model. -/
noncomputable def lawOnly (P : Problem S A) : NegativeDP.Switching.Problem S A where
  q := P.q
  q_markov := P.q_markov
  r := fun _ => 0
  r_measurable := measurable_const
  r_nonpos := fun _ => le_rfl
  qr_finite := fun _ _ => integrable_zero _ _ _

/-- Expected one-stage reward `σₙqr` at a history `h ∈ Hist S A n`: the expectation of
`r(sₙ, a, t)` under `a ~ σ.κ n h`, `t ~ q(· | sₙ, a)`. -/
noncomputable def stepReward (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : ℝ :=
  ∫ a, ∫ t, P.r (h.2, a, t) ∂P.q (h.2, a) ∂σ.κ n h

/-- Continuation return of Theorem 9.3 (p. 888), discounted case:
`uₙ(s₁, a₁, …, sₙ) = Σ_{j=n}^∞ β^{j−1} σₙq ⋯ σⱼqr`, with the factor `β^{j−1}` as printed.
At Lean decision `n` (the paper's stage `n + 1`) the `k`-th term is the paper's `j = n + 1 + k`,
so its factor is `β^{n+k}`. -/
noncomputable def contReturn (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : ℝ :=
  ∑' k : ℕ, P.β ^ (n + k) *
    ∫ h', stepReward P σ (n + k) h' ∂NegativeDP.Switching.contKernel (lawOnly P) σ n k h

/-- The switching policy of Theorem 9.3 (p. 888), discounted case: at each decision `π` uses
`σ`'s kernel on `Bₙ = {uₙ > vₙ}` and `τ`'s kernel on the complement. -/
def IsSwitch (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) : Prop :=
  ∀ n (h : Hist S A n),
    π.κ n h = if contReturn P τ n h < contReturn P σ n h then σ.κ n h else τ.κ n h

end Disc

/-! ### The positive bounded case P -/

namespace Pos

/-- The data of a positive problem (§3, p. 874): non-empty Borel `S`, `A`, a law of motion
`q ∈ Q(S | SA)`, a bounded non-negative Borel return `r`; `β = 1`. The uniform bound on the
expected return is added in `Problem`. -/
structure Data (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] where
  q : Kernel (S × A) S
  q_markov : IsMarkovKernel q
  r : S × A × S → ℝ
  r_measurable : Measurable r
  r_nonneg : ∀ x, 0 ≤ r x
  r_bounded : ∃ C : ℝ, ∀ x, r x ≤ C

/-- The same law of motion and return viewed as Blackwell's problem with `β = 0`; it is used only
for its history and stage laws (which depend on `q` and the policy alone) and for the
undiscounted stage expectation `stageReward`. -/
noncomputable def Data.toDisc (P : Data S A) : DiscountedDP.Stationary.Problem S A where
  q := P.q
  q_markov := P.q_markov
  r := P.r
  r_measurable := P.r_measurable
  r_bounded := by
    obtain ⟨C, hC⟩ := P.r_bounded
    exact ⟨C, fun x => by rw [abs_of_nonneg (P.r_nonneg x)]; exact hC x⟩
  β := 0
  β_nonneg := le_rfl
  β_lt_one := zero_lt_one

/-- Expected return at Lean stage `n` (the paper's stage `n + 1`), in `[0, ∞]`. -/
noncomputable def Data.stageGain (P : Data S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (P.r (x.1.1.2, x.1.2, x.2)) ∂DiscountedDP.Stationary.stageLaw P.toDisc π s n

/-- The total expected return `Σₙ π₁q ⋯ πₙqr` (p. 875) as a value in `[0, ∞]`. -/
noncomputable def Data.IE (P : Data S A) (π : Plan (S := S) (A := A)) (s : S) : ℝ≥0∞ :=
  ∑' n, P.stageGain π s n

/-- Strauch's positive bounded problem (§1 (b), p. 872, and §3, p. 874): the return is
non-negative and bounded, `β = 1`, and the expected return of every policy (every randomized
history-dependent plan) at every state is at most `R`, a positive number independent of the
policy. -/
structure Problem (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] extends Data S A where
  return_bounded : ∃ R : ℝ, 0 < R ∧
    ∀ (π : Plan (S := S) (A := A)) (s : S), toData.IE π s ≤ ENNReal.ofReal R

/-- `I(π)(s)` (p. 875), positive bounded case, as a real number; it is exact because the
extended value `IE` is bounded by `R`. -/
noncomputable def I (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : ℝ :=
  (P.IE π s).toReal

/-- `Iₙ(π, v)(s) = e_π[Σ_{j=1}^n r(sⱼ, aⱼ, sⱼ₊₁) + v(sₙ₊₁)]` (p. 875), `β = 1`, for a bounded
Borel terminal reward `v`. -/
noncomputable def In (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (v : S → ℝ)
    (s : S) : ℝ :=
  (∑ j ∈ Finset.range n, DiscountedDP.Stationary.stageReward P.toDisc π s j) +
    ∫ h, v h.2 ∂DiscountedDP.Stationary.historyLaw P.toDisc π s n

/-- `v* = sup_π I(π)` (p. 883), over every randomized history-dependent plan. -/
noncomputable def optReturn (P : Problem S A) (s : S) : ℝ :=
  ⨆ π : Plan (S := S) (A := A), I P π s

/-- The operator `T` of a measurable rule `f` (p. 878), `β = 1`:
`Tu(s) = ∫ r(s, f(s), t) + u(t) dq(t | s, f(s))`. -/
noncomputable def T (P : Problem S A) (f : {g : S → A // Measurable g}) (u : S → ℝ) (s : S) : ℝ :=
  ∫ t, P.r (s, f.1 s, t) + u t ∂P.q (s, f.1 s)

/-- `T_a`, the operator of the constant rule `f ≡ a` (p. 885). -/
noncomputable def Ta (P : Problem S A) (a : A) (u : S → ℝ) (s : S) : ℝ :=
  ∫ t, P.r (s, a, t) + u t ∂P.q (s, a)

/-- `Uu = supₙ Tₙu` (p. 879) for a Markov plan `π = (f₁, f₂, …)`. -/
noncomputable def U (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ) (s : S) : ℝ :=
  ⨆ n : ℕ, T P (π n) u s

/-- `u` is excessive for `U` (p. 883): `Uu ≤ u`. -/
def IsExcessive (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ) : Prop :=
  ∀ s, U P π u s ≤ u s

/-- Strauch's `(p, ε)`-optimality (p. 875), positive bounded case. -/
def IsStrongPEOptimal (P : Problem S A) (p : Measure S) (ε : ℝ) (π : Plan (S := S) (A := A)) :
    Prop :=
  ∀ᵐ s ∂p, optReturn P s - ε ≤ I P π s

end Pos

end NegativeDP.EssFinite.Supplement


