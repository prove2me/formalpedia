-- Prove2me | Definitions.Def_BestBothWorlds_SAO_Algorithm
-- name    : BestBothWorlds_SAO_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:17:18.650187+00:00
-- url     : https://prove2.me/theorems/d773e1b0-e38f-4285-89e0-17bee4a35033
-- title:
--   The SAO strategy with parameter β (Algorithm 1)
-- statement:
--   SAO (Stochastic and Adversarial Optimal) is Algorithm 1 of Bubeck and Slivkins. It takes a parameter $\beta>1$ and the horizon $n$. It keeps a set $A$ of *active* arms, a deactivation time $\tau_i$ (initially $n$) for each arm, and the probability $q_i$ that arm $i$ had when it was deactivated. It starts with $A=\{1,\dots,K\}$ and $p_i=1/K$. Write
--   $$w(x)=\sqrt{\frac{4K\log\beta}{x}+5\Big(\frac{K\log\beta}{x}\Big)^2}.$$
--   On round $t=1,\dots,n$ it plays $I_t\sim p$ and updates $\widetilde H_{\cdot,t}$, $\widehat H_{\cdot,t}$ and $T_\cdot(t)$ with the observed reward. Then, for $i=1,\dots,K$ in order:
--
--   1. **Test (12).** If $i\in A$ and $\max_{j\in A}\widetilde H_{j,t}-\widetilde H_{i,t}>6\,w(t)$, arm $i$ is deactivated: $A\leftarrow A\setminus\{i\}$, $\tau_i\leftarrow t$, $q_i\leftarrow p_i$.
--   2. **Tests (13)–(15).** With $t_i^*=\min(\tau_i,t)$, SAO checks the three tests below. If one of them holds, Exp3.P is started.
--      - (13): $|\widetilde H_{i,t}-\widehat H_{i,t}|>\sqrt{2\log\beta/T_i(t)}+\sqrt{4\big(\tfrac{Kt_i^*}{t^2}+\tfrac{t-t_i^*}{q_i\tau_i t}\big)\log\beta+5\big(\tfrac{K\log\beta}{t_i^*}\big)^2}$.
--      - (14): $i\notin A$ and $\max_{j\in A}\widetilde H_{j,t}-\widetilde H_{i,t}>10\,w(\tau_i-1)$.
--      - (15): $i\notin A$ and $\max_{j\in A}\widetilde H_{j,t}-\widetilde H_{i,t}\le 2\,w(\tau_i)$.
--
--   After the loop, (16) sets
--   $$p_i=\frac{q_i\tau_i}{t+1}\mathbb 1_{\{i\notin A\}}+\frac1{|A|}\Big(1-\sum_{j\notin A}\frac{q_j\tau_j}{t+1}\Big)\mathbb 1_{\{i\in A\}}.$$
--
--   If a test (13)–(15) fires on round $\tau_0$, then from round $\tau_0+1$ on SAO runs Exp3.P from scratch on the remaining $m=n-\tau_0$ rounds. It uses the parameters of Bubeck–Cesa-Bianchi Theorem 3.2 (3.10) for horizon $m$ and confidence $\delta_P=K/\beta$, so that $\ln(K\delta_P^{-1})=\ln\beta$.
--
--   **Formalization Note** The state is folded over the observed history. Within a round the estimates include round $t$ before the tests run. The arms are tested in increasing order, and the active set changes during the loop: a later arm's tests use the set from which earlier arms of the same round were already removed. Algorithm 1 leaves three boundary cases undefined; this file fixes them as follows.
--   - Test (13) is taken to be false when $T_i(t)=0$, because $\widehat H_{i,t}$ and $\sqrt{2\log\beta/T_i(t)}$ are undefined there.
--   - Test (14) is taken to be false when $\tau_i=1$, because $w(\tau_i-1)$ divides by $0$. For $\beta=10Kn^3\delta^{-1}$ no arm can be deactivated on round 1: there $\widetilde H_{j,1}\le K<6w(1)$, since $\log\beta>1$.
--   - $q_i$ is $0$ until arm $i$ is deactivated. It is then read only through $(t-t_i^*)/(q_i\tau_i t)$, which has numerator $0$ while the arm is active.
--
--   $|A|\ge1$ always holds, because an arm attaining $\max_{j\in A}\widetilde H_{j,t}$ cannot satisfy (12) when $\log\beta>0$. Hence (16) never divides by $0$, and the vector $p$ has nonnegative entries summing to $1$. Once Exp3.P has started, SAO's own state is frozen and plays no further role. The confidence parameter $\delta_P=K/\beta$ of Exp3.P is implicit in the paper; this choice makes (25) exactly Lemma 4.8.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 13, Algorithm 1, eq. (12)–(16)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P

namespace BestBothWorlds.SAO

/-- The internal state of SAO (Algorithm 1, p. 13) after `t` rounds. -/
structure SAOState (K : ℕ) where
  /-- number of rounds processed -/
  t : ℕ
  /-- the active set `A` -/
  active : Finset (Fin K)
  /-- `τ_i`, the deactivation time of arm `i` (`n` while active) -/
  tau : Fin K → ℕ
  /-- `q_i`, the probability of arm `i` when it was deactivated (`0` while active; never read) -/
  q : Fin K → ℝ
  /-- the sampling vector `p` for the next round -/
  p : Fin K → ℝ
  /-- `G̃_{i,t}` -/
  Gtil : Fin K → ℝ
  /-- `Ĝ_{i,t}` -/
  Ghat : Fin K → ℝ
  /-- `T_i(t)` -/
  T : Fin K → ℕ
  /-- `some τ₀` once one of the tests (13)–(15) has fired on round `τ₀` (Exp3.P is then started
  from round `τ₀ + 1` on) -/
  tau0 : Option ℕ

/-- The initial state (lines 1–5): `A = {1, …, K}`, `τ_i = n`, `p_i = 1/K`. -/
noncomputable def SAOState.init (K n : ℕ) : SAOState K where
  t := 0
  active := Finset.univ
  tau := fun _ => n
  q := fun _ => 0
  p := fun _ => 1 / (K : ℝ)
  Gtil := fun _ => 0
  Ghat := fun _ => 0
  T := fun _ => 0
  tau0 := none

/-- `max_{j ∈ A} f j` (`0` for empty `A`, which never occurs in a run of SAO: an arm attaining the
maximum over `A` cannot satisfy (12)). -/
noncomputable def maxOver {K : ℕ} (A : Finset (Fin K)) (f : Fin K → ℝ) : ℝ :=
  if h : A.Nonempty then A.sup' h f else 0

/-- The confidence width `√(4K log(β)/x + 5 (K log(β)/x)²)` used in tests (12), (14), (15). -/
noncomputable def width (K : ℕ) (β x : ℝ) : ℝ :=
  Real.sqrt (4 * K * Real.log β / x + 5 * (K * Real.log β / x) ^ 2)

open Classical in
/-- The body of the inner loop (lines 9–18) for arm `i` on round `t`. The carried data are the
active set `A`, the times `τ`, the probabilities `q`, and a flag recording whether one of the tests
(13)–(15) has fired on this round. `p` is the sampling vector used on round `t`, `Ht i = H̃_{i,t}`,
`Hh i = Ĥ_{i,t}`, `T i = T_i(t)`.
* (12): if `i ∈ A` and `max_{j∈A} H̃_{j,t} - H̃_{i,t} > 6 · width(t)`, then `A ← A \ {i}`,
  `τ_i ← t`, `q_i ← p_i`.
* (13) with `t*_i = min(τ_i, t)`: `|H̃_{i,t} - Ĥ_{i,t}| > √(2 log β / T_i(t)) +
  √(4 (K t*_i/t² + (t - t*_i)/(q_i τ_i t)) log β + 5 (K log β / t*_i)²)`; it is taken to be false
  when `T_i(t) = 0`, where `Ĥ_{i,t}` and the first root are undefined.
* (14): `i ∉ A` and `max_{j∈A} H̃_{j,t} - H̃_{i,t} > 10 · width(τ_i - 1)`; it is taken to be false
  when `τ_i = 1`, where `width(τ_i - 1)` divides by zero.
* (15): `i ∉ A` and `max_{j∈A} H̃_{j,t} - H̃_{i,t} ≤ 2 · width(τ_i)`.
The tests use the active set as updated by the earlier arms of the same round. -/
noncomputable def armStep (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ)
    (s : Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool) (i : Fin K) :
    Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool :=
  let A := s.1
  let deact : Prop := i ∈ A ∧ maxOver A Ht - Ht i > 6 * width K β t
  let A' := if deact then A.erase i else A
  let tau' := if deact then Function.update s.2.1 i t else s.2.1
  let q' := if deact then Function.update s.2.2.1 i (p i) else s.2.2.1
  let tstar : ℕ := min (tau' i) t
  let test13 : Prop := 1 ≤ T i ∧
    |Ht i - Hh i| > Real.sqrt (2 * Real.log β / T i) +
      Real.sqrt (4 * (K * tstar / (t : ℝ) ^ 2 + ((t : ℝ) - tstar) / (q' i * tau' i * t)) *
        Real.log β + 5 * (K * Real.log β / tstar) ^ 2)
  let test14 : Prop := i ∉ A' ∧ 2 ≤ tau' i ∧
    maxOver A' Ht - Ht i > 10 * width K β ((tau' i : ℝ) - 1)
  let test15 : Prop := i ∉ A' ∧ maxOver A' Ht - Ht i ≤ 2 * width K β (tau' i)
  (A', tau', q', s.2.2.2 || decide (test13 ∨ test14 ∨ test15))

/-- One round `t = s.t + 1` of SAO (lines 7–21) after the played arm `a = I_t` and its reward
`g = g_{I_t,t}` are observed. The estimates are updated with round `t`
(`G̃_{i,t} = G̃_{i,t-1} + g 𝟙{a = i}/p_{i,t}`, `Ĝ`, `T`), the inner loop runs over
`i = 1, …, K` in order, and (16) gives the next sampling vector
`p_i = (q_i τ_i/(t+1)) 𝟙{i ∉ A} + (1/|A|)(1 - ∑_{j ∉ A} q_j τ_j/(t+1)) 𝟙{i ∈ A}`. If one of the
tests (13)–(15) fired, `τ₀ = t` is recorded. Once `τ₀` is recorded the state is frozen (Exp3.P
takes over). -/
noncomputable def saoStep (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) : SAOState K :=
  match s.tau0 with
  | some _ => s
  | none =>
    let t := s.t + 1
    let Gtil' : Fin K → ℝ := fun i => s.Gtil i + (if o.1 = i then o.2 / s.p i else 0)
    let Ghat' : Fin K → ℝ := fun i => s.Ghat i + (if o.1 = i then o.2 else 0)
    let T' : Fin K → ℕ := fun i => s.T i + (if o.1 = i then 1 else 0)
    let Ht : Fin K → ℝ := fun i => Gtil' i / t
    let Hh : Fin K → ℝ := fun i => Ghat' i / T' i
    let r := (List.finRange K).foldl (armStep K β t s.p Ht Hh T') (s.active, s.tau, s.q, false)
    let A := r.1
    let tau := r.2.1
    let q := r.2.2.1
    { t := t
      active := A
      tau := tau
      q := q
      p := fun i => if i ∈ A then
          (1 - ∑ j ∈ Finset.univ \ A, q j * tau j / ((t : ℝ) + 1)) / A.card
        else q i * tau i / ((t : ℝ) + 1)
      Gtil := Gtil'
      Ghat := Ghat'
      T := T'
      tau0 := if r.2.2.2 then some t else none }

/-- SAO's internal state after processing the history `h`. -/
noncomputable def saoState (K n : ℕ) (β : ℝ) (h : History K) : SAOState K :=
  h.foldl (saoStep K β) (SAOState.init K n)

/-- The SAO strategy with parameter `β > 1` and horizon `n` (Algorithm 1, p. 13), as a policy.
Before any test (13)–(15) fires it plays the sampling vector of Algorithm 1. If a test fires on
round `τ₀`, then from round `τ₀ + 1` on it runs Exp3.P from scratch on the remaining
`m = n - τ₀` rounds, with the parameters of Bubeck & Cesa-Bianchi 2012, Theorem 3.2 (3.10), for
horizon `m` and confidence `δ_P = K/β` (so that `ln(K δ_P⁻¹) = ln β`). -/
noncomputable def sao (K n : ℕ) (β : ℝ) : Policy K := fun h =>
  match (saoState K n β h).tau0 with
  | none => (saoState K n β h).p
  | some τ₀ => exp3P K (exp3PTuned K (n - τ₀) (K / β)) (h.drop τ₀)

end BestBothWorlds.SAO


