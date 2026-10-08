-- Prove2me | Definitions.Def_MNLBandit_UCB_Algorithm1
-- name    : MNLBandit_UCB_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:33:48.626307+00:00
-- url     : https://prove2.me/theorems/071a5471-dec5-451c-a341-ee39dca82b3f
-- title:
--   §3.2, pp. 8–9 — Algorithm 1: epochs, estimates (3.1)–(3.3), UCB (3.4), optimistic assortment (3.6)–(3.7)
-- statement:
--   This file defines **Algorithm 1** of Agrawal, Avadhanula, Goyal and Zeevi, the epoch-based upper-confidence-bound policy for the MNL-Bandit, and the epoch quantities along a history.
--
--   The time horizon is divided into **epochs**: in epoch $\ell$ the assortment $S_\ell$ is offered repeatedly until a customer does not purchase. When epoch $\ell$ ends, the algorithm records the purchase counts
--   $$
--   \hat v_{i,\ell}=\sum_{t\in\mathcal E_\ell}\mathbb 1(c_t=i)\qquad(3.1),
--   $$
--   and computes, for every product $i$, the set $\mathcal T_i(\ell)=\{\tau\le\ell : i\in S_\tau\}$ of epochs that offered $i$ and its size $T_i(\ell)$ (3.2), the average $\bar v_{i,\ell}=\frac1{T_i(\ell)}\sum_{\tau\in\mathcal T_i(\ell)}\hat v_{i,\tau}$ (3.3), and the upper confidence bound
--   $$
--   v^{\mathrm{UCB}}_{i,\ell}=\bar v_{i,\ell}+\sqrt{\bar v_{i,\ell}\,\frac{48\log(\sqrt N\ell+1)}{T_i(\ell)}}+\frac{48\log(\sqrt N\ell+1)}{T_i(\ell)}\qquad(3.4).
--   $$
--   The next epoch offers the optimistic assortment
--   $$
--   S_{\ell+1}=\operatorname*{argmax}_{S\in\mathcal S}\tilde R_{\ell+1}(S),\qquad \tilde R_{\ell+1}(S)=\frac{\sum_{i\in S}r_iv^{\mathrm{UCB}}_{i,\ell}}{1+\sum_{j\in S}v^{\mathrm{UCB}}_{j,\ell}}\qquad(3.6)\text{–}(3.7),
--   $$
--   with the initialization $v^{\mathrm{UCB}}_{i,0}=1$.
--
--   The definitions are:
--   1. `alg1 r sel`, Algorithm 1 as a policy: a state (completed epochs with their assortments and counts, the current assortment, the current counts) is updated by each observed choice; a no-purchase closes the epoch and recomputes the UCBs and the next assortment. The argmax is taken by the selector `sel`. The policy sees only $r$, `sel` and the observed choices, never $v$.
--   2. Along a history $h$: `epochsDone h` (the number of completed epochs), `Tcount h i ℓ` $=T_i(\ell)$, `vbar h i ℓ` $=\bar v_{i,\ell}$, `vUCB h i ℓ` $=v^{\mathrm{UCB}}_{i,\ell}$, and `nextSet h ℓ` $=S_{\ell+1}$, all after the first $\ell$ completed epochs ($\ell\le$ `epochsDone h`).
--   3. `epochsStarted h` $=L$, the number of epochs that have at least one of the $T$ customers.
--
--   **Formalization Note.** (3.4) divides by $T_i(\ell)$, which is $0$ until product $i$ is first offered; the algorithm then keeps the initial value, $v^{\mathrm{UCB}}_{i,\ell}=1$ while $T_i(\ell)=0$. Line 3 of Algorithm 1 ("while $t<T$") is not modelled: the policy is defined for every customer and the horizon enters only the regret. Line 8 prints $i\in S_\ell$ inside $\mathcal T_i(\ell)$; (3.2)'s $i\in S_\tau$ is used.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, pp. 8–9, (3.1)–(3.7), Algorithm 1

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

/-- The record of one completed epoch `τ` of Algorithm 1: its assortment `S_τ` and the purchase
counts `v̂_{i,τ}` (3.1) of every product in that epoch. -/
abbrev EpochRecord (N : ℕ) := Finset (Fin N) × (Fin N → ℕ)

/-- `T_i(ℓ) = |{τ ≤ ℓ : i ∈ S_τ}|` (3.2), for the list `past` of the `ℓ = past.length` completed
epochs. -/
def TcountL {N : ℕ} (past : List (EpochRecord N)) (i : Fin N) : ℕ :=
  (past.filter (fun e => decide (i ∈ e.1))).length

/-- `v̄_{i,ℓ} = (1 / T_i(ℓ)) ∑_{τ ∈ 𝒯_i(ℓ)} v̂_{i,τ}` (3.3) for the list `past` of completed epochs.
Only used when `T_i(ℓ) ≥ 1`. -/
noncomputable def vbarL {N : ℕ} (past : List (EpochRecord N)) (i : Fin N) : ℝ :=
  ((past.filter (fun e => decide (i ∈ e.1))).map (fun e => (e.2 i : ℝ))).sum / (TcountL past i : ℝ)

/-- The upper confidence bound (3.4) after the `ℓ = past.length` completed epochs `past`:
`v^UCB_{i,ℓ} = v̄_{i,ℓ} + √(v̄_{i,ℓ} · 48 log(√N ℓ + 1) / T_i(ℓ)) + 48 log(√N ℓ + 1) / T_i(ℓ)`.
While product `i` has never been offered (`T_i(ℓ) = 0`) the value is `1`, the initialization
`v^UCB_{i,0} = 1` of Algorithm 1, line 1. -/
noncomputable def vUCBL {N : ℕ} (past : List (EpochRecord N)) (i : Fin N) : ℝ :=
  if TcountL past i = 0 then 1 else
    vbarL past i
      + Real.sqrt (vbarL past i * (48 * Real.log (Real.sqrt N * (past.length : ℝ) + 1))
          / (TcountL past i : ℝ))
      + 48 * Real.log (Real.sqrt N * (past.length : ℝ) + 1) / (TcountL past i : ℝ)

/-- The optimistic assortment (3.6)–(3.7): the selector's maximizer over `𝒮` of
`R̃(S) = ∑_{i ∈ S} r_i v^UCB_i / (1 + ∑_{j ∈ S} v^UCB_j)` computed from the completed epochs
`past`. -/
noncomputable def optimisticSet {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (past : List (EpochRecord N)) :
    Finset (Fin N) :=
  sel (fun S => mnlObjective (fun i => vUCBL past i) r 1 S)

/-- The internal state of Algorithm 1: the completed epochs, the assortment of the current epoch,
and the purchase counts of the current epoch so far. -/
structure AlgState (N : ℕ) where
  past : List (EpochRecord N)
  cur : Finset (Fin N)
  counts : Fin N → ℕ

/-- Initial state (lines 1–2): no completed epoch, the first assortment is the argmax of `R̃`
with `v^UCB_{i,0} = 1`, no purchases yet. -/
noncomputable def initState {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) : AlgState N :=
  ⟨[], optimisticSet r sel [], fun _ => 0⟩

/-- One customer's outcome updates the state (lines 5–14). A no-purchase closes the current epoch:
its assortment and counts are appended to the completed epochs, the UCBs are recomputed, and the next
epoch's assortment is the new optimistic assortment. A purchase of `i` increments `i`'s count. -/
noncomputable def step {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (s : AlgState N) :
    Option (Fin N) → AlgState N
  | none =>
      ⟨s.past ++ [(s.cur, s.counts)], optimisticSet r sel (s.past ++ [(s.cur, s.counts)]),
        fun _ => 0⟩
  | some i => ⟨s.past, s.cur, Function.update s.counts i (s.counts i + 1)⟩

/-- The state of Algorithm 1 after the outcomes `cs`, in order. -/
noncomputable def runAlg {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (cs : List (Option (Fin N))) : AlgState N :=
  cs.foldl (step r sel) (initState r sel)

/-- Algorithm 1 (p. 9) as a policy: customer `t` is offered the assortment of the current epoch
after the choices of customers `0, …, t - 1`. It uses only the revenues `r`, the selector `sel`
(which encodes `𝒮` and the tie-breaking rule) and the observed choices, never `v`. -/
noncomputable def alg1 {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) : Policy N :=
  fun _ pre => (runAlg r sel (List.ofFn pre)).cur

/-- The state of Algorithm 1 after the whole history `h`. -/
noncomputable def finalState {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) : AlgState N :=
  runAlg r sel (List.ofFn h)

/-- The number of epochs completed within the history `h` (the number of no-purchases). -/
noncomputable def epochsDone {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) : ℕ :=
  (finalState r sel h).past.length

/-- The first `ℓ` completed epochs of `h` (epochs `1, …, ℓ`), for `ℓ ≤ epochsDone h`. -/
noncomputable def pastUpTo {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (ℓ : ℕ) :
    List (EpochRecord N) :=
  (finalState r sel h).past.take ℓ

/-- `T_i(ℓ)` (3.2) along `h`, after `ℓ` completed epochs. -/
noncomputable def Tcount {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (i : Fin N) (ℓ : ℕ) : ℕ :=
  TcountL (pastUpTo r sel h ℓ) i

/-- `v̄_{i,ℓ}` (3.3) along `h`, after `ℓ` completed epochs. -/
noncomputable def vbar {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (i : Fin N) (ℓ : ℕ) : ℝ :=
  vbarL (pastUpTo r sel h ℓ) i

/-- `v^UCB_{i,ℓ}` (3.4) along `h`, after `ℓ` completed epochs. -/
noncomputable def vUCB {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (i : Fin N) (ℓ : ℕ) : ℝ :=
  vUCBL (pastUpTo r sel h ℓ) i

/-- `S_{ℓ+1}`, the assortment Algorithm 1 offers in epoch `ℓ + 1`, computed at the end of epoch `ℓ`
from `v^UCB_{·,ℓ}` (3.6); `nextSet r sel h 0 = S_1`. -/
noncomputable def nextSet {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (ℓ : ℕ) : Finset (Fin N) :=
  optimisticSet r sel (pastUpTo r sel h ℓ)

/-- `L`, the number of epochs started within the first `T` customers of `h`: `0` if `T = 0`, and
otherwise one plus the number of no-purchases among customers `0, …, T - 2`. -/
def epochsStarted {N T : ℕ} (h : History N T) : ℕ :=
  if T = 0 then 0 else
    (Finset.univ.filter (fun t : Fin T => t.val + 1 < T ∧ h t = none)).card + 1

end MNLBandit.UCB


