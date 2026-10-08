-- Prove2me | Definitions.Def_NegativeDP_Switching_Model
-- name    : NegativeDP_Switching_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:54.492145+00:00
-- url     : https://prove2.me/theorems/a4167d2e-78cc-4bb5-8389-412228fd83d8
-- title:
--   Strauch's negative dynamic programming problem (§3) with continuation returns $u_n$, history-dependent terminal rewards and the switching policy of Theorem 9.3
-- statement:
--   **The negative dynamic programming problem** (Strauch 1966, §3, p. 874). The state space $S$ and the action space $A$ are non-empty Borel sets. The law of motion $q(\cdot\mid s,a)$ is a probability kernel from $S\times A$ to $S$. The return $r(s,a,t)$ is a Borel function with $-\infty<r\le 0$, and its one-step expectation $\int r(s,a,t)\,q(dt\mid s,a)$ is finite at every $(s,a)$. There is no discounting ($\beta=1$).
--
--   A **policy** $\pi=(\pi_1,\pi_2,\dots)$ chooses the $n$-th action with a probability kernel $\pi_n(\cdot\mid h)$ depending on the whole history $h=(s_1,a_1,\dots,a_{n-1},s_n)$. The **expected return** from the initial state $s$ is the sum of the stage expectations
--   $$I(\pi)(s)=\sum_{n=1}^{\infty}\pi_1q\cdots\pi_nqr\,(s)\in[-\infty,0],$$
--   and, for a terminal reward $w$ that depends on the history $(s_1,a_1,\dots,s_{n+1})$ and is $\le 0$,
--   $$I_n(\pi,w)(s_1)=e_\pi\Big[\sum_{j=1}^{n}r(s_j,a_j,s_{j+1})+w(s_1,a_1,\dots,s_{n+1})\Big]$$
--   (p. 888, extending $I_n(\pi,v)$ of p. 875, which is also defined here for a terminal reward $v(s_{n+1})$).
--
--   **Continuation returns** (p. 888). For a policy $\sigma$ and a history $h=(s_1,a_1,\dots,s_n)$, the continuation return
--   $$u_n(h)=\sum_{j=n}^{\infty}\sigma_nq\cdots\sigma_jqr\,(h)$$
--   is the expected total return from stage $n$ on when $\sigma$'s own kernels $\sigma_n,\sigma_{n+1},\dots$, fed the full history starting with $h$, are used. It is defined from the law of the future histories started at $h$. For two policies $\sigma,\tau$ with continuation returns $u_n,v_n$, the file defines $w_n=\max(u_n,v_n)$ and the one-step operator $\pi_n(r+w_{n+1})(h)$, the expectation of $r(s_n,a,t)+w_{n+1}(h,a,t)$ when $a\sim\pi_n(\cdot\mid h)$ and $t\sim q(\cdot\mid s_n,a)$.
--
--   **The switching policy** of Theorem 9.3: $\pi$ is a switching policy for $(\sigma,\tau)$ when
--   $$\pi_n(\cdot\mid h)=\begin{cases}\sigma_n(\cdot\mid h)&\text{if }u_n(h)>v_n(h),\\ \tau_n(\cdot\mid h)&\text{otherwise,}\end{cases}$$
--   at every stage $n$ and every history $h$. The file also defines $^n\pi=(\pi_{n+1},\pi_{n+2},\dots)$ for a Markov policy and $(f,\pi)$, the policy which uses the measurable rule $f$ at the first stage and then runs $\pi$ on the history from $s_2$ on (p. 879).
--
--   These objects are the vocabulary of §9's improvement results: Theorem 9.2 (Howard's routine), Theorem 9.3 and Corollaries 9.1, 9.2.
--
--   **Formalization Note** The paper's Borel sets are non-empty standard Borel types and its policies are the plans of Blackwell's published model `DiscountedDP.Stationary` (kernels on `Hist S A n`, the history before the paper's $(n+1)$-st action: decisions are numbered from $0$ in Lean, so Lean's index $n$ is the paper's stage $n+1$). Only the negative case ($r\le 0$, $\beta=1$) is modelled. Returns live in `EReal` and are computed as minus the `lintegral` of the loss $-r$ (and of $-w$ for a terminal reward), so the value $-\infty$ is represented exactly; a Bochner integral, which returns $0$ on non-integrable functions, is never used. $I(\pi)$ is the sum of stage expectations, which equals $e_\pi\rho$ by monotone convergence. Terminal rewards are read through $(-w)^+$, so they are meaningful for $w\le 0$, the paper's class $M$. The switching policy is characterised by the predicate `IsSwitch` (its existence is part of Theorem 9.3) rather than built with `Kernel.piecewise`, because building it needs a proof that the set $B_n=\{u_n>v_n\}$ is Borel. The law of the history is built with the same one-step kernel as the continuation law.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), pp. 873–875 (§2–§3), p. 879 (Theorem 5.1(f): (f, π)), p. 888 (Theorem 9.3 and its proof)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return

namespace NegativeDP.Switching

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

/-- Strauch §3 (p. 874), negative case: non-empty Borel `S`, `A`; law of motion `q ∈ Q(S | SA)`;
return `r ∈ M(SAS)` with `r > −∞` (real-valued, non-positive) and `qr > −∞` (integrable at every
state-action pair); `β = 1`. -/
structure Problem (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] where
  q : Kernel (S × A) S
  q_markov : IsMarkovKernel q
  r : S × A × S → ℝ
  r_measurable : Measurable r
  r_nonpos : ∀ x, r x ≤ 0
  qr_finite : ∀ s a, Integrable (fun t => r (s, a, t)) (q (s, a))

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- `M(X)`, negative case (p. 873): non-positive extended-real Baire functions. -/
def IsNegM {X : Type*} [MeasurableSpace X] (u : X → EReal) : Prop :=
  Measurable u ∧ ∀ x, u x ≤ 0

/-- The empty history `(s)` at the first decision: the paper's `H_1 = S`. -/
def Hist.start (s : S) : Hist S A 0 := ((fun i : Fin 0 => Fin.elim0 i), s)

/-- Extend a history `h = (s_1, a_1, …, s_n)` by the action `a` taken at its current state and
the next state `t`: `(s_1, a_1, …, s_n, a, t)`. -/
def Hist.snoc {n : ℕ} (h : Hist S A n) (a : A) (t : S) : Hist S A (n + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A) (Fin.last n)).symm
    ((h.2, a), h.1), t)

/-- The transition kernel from a history and the chosen action to the next state. -/
noncomputable def nextKernel (P : Problem S A) (n : ℕ) : Kernel (Hist S A n × A) S :=
  P.q ∘ₖ Kernel.deterministic (fun ha : Hist S A n × A => (ha.1.2, ha.2)) (by fun_prop)

/-- One stage of the process under the plan `σ` at Lean decision `n`: from a history
`h ∈ Hist S A n`, draw `a ~ σ.κ n h`, then `t ~ q(· | h.2, a)`, and return `Hist.snoc h a t`. -/
noncomputable def stepKernel (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ) :
    Kernel (Hist S A n) (Hist S A (n + 1)) :=
  letI : IsMarkovKernel (σ.κ n) := σ.κ_markov n
  letI : IsMarkovKernel P.q := P.q_markov
  Kernel.map ((Kernel.id ×ₖ σ.κ n) ⊗ₖ (nextKernel P n).comap Prod.snd measurable_snd)
    (fun x : (Hist S A n × A) × S =>
      (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A) (Fin.last n)).symm
        ((x.1.1.2, x.1.2), x.1.1.1), x.2) : Hist S A (n + 1)))

/-- Continuation law: started from a history `h ∈ Hist S A n` (Lean decision `n`, the paper's
stage `n + 1`) and using `σ`'s own kernels `σ.κ n, σ.κ (n+1), …` fed the full history, the law of
the history `k` stages later. -/
noncomputable def contKernel (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ) :
    (k : ℕ) → Kernel (Hist S A n) (Hist S A (n + k))
  | 0 => Kernel.id
  | k + 1 => stepKernel P σ (n + k) ∘ₖ contKernel P σ n k

/-- Expected one-stage loss `−σ_n q r` at a history `h ∈ Hist S A n`: the expectation of
`−r(s_n, a, t)` under `a ~ σ.κ n h`, `t ~ q(· | s_n, a)`, a value in `[0, ∞]`. -/
noncomputable def stepLoss (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) ∂P.q (h.2, a) ∂σ.κ n h

/-- Continuation return (p. 888): `u_n(s_1, a_1, …, s_n) = Σ_{j ≥ n} σ_n q ⋯ σ_j q r` (β = 1),
the expected total return from history `h ∈ Hist S A n` on when `σ`'s kernels are used from
Lean decision `n` on. A value in `[−∞, 0]`. -/
noncomputable def contReturn (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : EReal :=
  -((∑' k : ℕ, ∫⁻ h', stepLoss P σ (n + k) h' ∂contKernel P σ n k h : ℝ≥0∞) : EReal)

/-- Law of the history before the paper's `(n+1)`st action from the initial state `s`
(Blackwell's recursion, with the negative problem's law of motion). -/
noncomputable def historyLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    (n : ℕ) → Measure (Hist S A n)
  | 0 => Measure.dirac (Hist.start s)
  | n + 1 => (historyLaw P π s n).bind (stepKernel P π n)

/-- Expected loss `−E r` at Lean stage `n` (the paper's stage `n + 1`), in `[0, ∞]`. -/
noncomputable def stageLoss (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    ℝ≥0∞ :=
  ∫⁻ h, stepLoss P π n h ∂historyLaw P π s n

/-- `I(π)(s) = Σ_n π_1 q ⋯ π_n q r` (p. 875), a value in `[−∞, 0]`. -/
noncomputable def I (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : EReal :=
  -((∑' n, stageLoss P π s n : ℝ≥0∞) : EReal)

/-- `I_n(π, v)(s)` (p. 875): `n` stages, then the terminal reward `v(s_{n+1})`, `v ∈ M(S)`. -/
noncomputable def In (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (v : S → EReal)
    (s : S) : EReal :=
  -(((∑ j ∈ Finset.range n, stageLoss P π s j) +
      ∫⁻ h, (-(v h.2)).toENNReal ∂historyLaw P π s n : ℝ≥0∞) : EReal)

/-- `I_n(π, w_{n+1})` (p. 888): `n` stages, then the history-dependent terminal reward
`w_{n+1}(s_1, a_1, …, s_{n+1})`, `w ∈ M(SA⋯AS)` with `2n + 1` factors, i.e. on `Hist S A n`. -/
noncomputable def InH (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ)
    (w : Hist S A n → EReal) (s : S) : EReal :=
  -(((∑ j ∈ Finset.range n, stageLoss P π s j) +
      ∫⁻ h, (-(w h)).toENNReal ∂historyLaw P π s n : ℝ≥0∞) : EReal)

/-- The one-step operator `π_n(r + β w)` with `β = 1` (proof of Theorem 9.3, p. 888): at a history
`h ∈ Hist S A n`, the expectation of `r(s_n, a, t) + w(h, a, t)` under `a ~ π.κ n h`,
`t ~ q(· | s_n, a)`, computed as minus the integral of the loss (`w ≤ 0` is assumed wherever this
is used). -/
noncomputable def stepOp (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ)
    (w : Hist S A (n + 1) → EReal) (h : Hist S A n) : EReal :=
  -((∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + (-(w (Hist.snoc h a t))).toENNReal
      ∂P.q (h.2, a) ∂π.κ n h : ℝ≥0∞) : EReal)

/-- The switching policy of Theorem 9.3 (p. 888): at Lean decision `n` (the paper's stage `n+1`),
`π` uses `σ`'s kernel on `B = {u > v}` (σ's continuation return strictly larger than τ's) and
`τ`'s kernel on the complement. -/
def IsSwitch (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) : Prop :=
  ∀ n (h : Hist S A n),
    π.κ n h = if contReturn P τ n h < contReturn P σ n h then σ.κ n h else τ.κ n h

/-- `w_n = max(u_n, v_n)` (proof of Theorem 9.3, p. 888), at Lean decision `n`. -/
noncomputable def wmax (P : Problem S A) (σ τ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : EReal :=
  max (contReturn P σ n h) (contReturn P τ n h)

/-- `ⁿπ` (p. 874) for a Markov plan: the plan it defines from the `(n+1)`st stage on. -/
def shift (π : MarkovPlan S A) (n : ℕ) : MarkovPlan S A := fun k => π (k + n)

/-- Drop the first state-action pair of a history. -/
def Hist.tail {n : ℕ} (h : Hist S A (n + 1)) : Hist S A n := (fun i => h.1 i.succ, h.2)

omit [StandardBorelSpace S] [Nonempty S] [StandardBorelSpace A] [Nonempty A] in
lemma Hist.measurable_tail (n : ℕ) : Measurable (Hist.tail (S := S) (A := A) (n := n)) := by
  unfold Hist.tail
  refine Measurable.prodMk ?_ measurable_snd
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_fst)

/-- `(f, π)` (p. 879): use the rule `f` at the first stage, then run `π` on the history from
the second state on. -/
noncomputable def prefixPlan (f : {g : S → A // Measurable g}) (π : Plan (S := S) (A := A)) :
    Plan (S := S) (A := A) where
  κ
    | 0 => Kernel.deterministic (fun h : Hist S A 0 => f.1 h.2) (f.2.comp measurable_snd)
    | k + 1 => (π.κ k).comap Hist.tail (Hist.measurable_tail k)
  κ_markov
    | 0 => by infer_instance
    | k + 1 => by
        have := π.κ_markov k
        infer_instance

end NegativeDP.Switching


