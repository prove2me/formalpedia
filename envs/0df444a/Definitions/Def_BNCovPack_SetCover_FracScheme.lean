-- Prove2me | Definitions.Def_BNCovPack_SetCover_FracScheme
-- name    : BNCovPack_SetCover_FracScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:05:55.268289+00:00
-- url     : https://prove2.me/theorems/8d9eadfd-dc5f-4df2-bbdd-c06c0aa526ea
-- title:
--   The Section 3 fractional scheme with $\{0,1\}$ coefficients and $n$ replaced by $\ell$, run on a set-cover instance
-- statement:
--   This file defines the online fractional covering scheme of Section 3 of Buchbinder and Naor (2009) in the special case where every coefficient is $0$ or $1$, run on a set-cover instance.
--
--   Fix a finite ground set $X$ of elements and a finite family $\mathcal S$ of sets, each set $s$ with a positive cost $c(s)$; for an element $e$ let $\mathcal S_e$ be the collection of sets containing $e$. In the covering-packing framework of the paper (Figure 1) the primal variables are the sets, $x(s)=w(s)\ge 0$, and every arriving element $e$ is a covering constraint $\sum_{s\in\mathcal S_e} w(s)\ge 1$ whose dual variable is $y(e)\ge 0$. Elements arrive one by one in a list $\sigma=(e_1,e_2,\dots)$, possibly with repetitions. Fix the parameter $B>0$ and an integer $\ell\ge 1$.
--
--   1. **State.** The current weights $w(s)$, the loads $L(s)=\sum_{k:\ s\ni e_k} y(e_k)$ accumulated over the elements that have arrived so far, and the dual value $Y=\sum_k y(e_k)$. Initially everything is $0$.
--   2. **Weights as a function of the new dual variable.** When element $e$ arrives and its dual variable has the value $t\ge 0$, every set $s\ni e$ has weight
--   $$w_s(t)=\max\Big\{w(s),\ \frac1\ell\Big(\exp\Big(\frac{B}{2c(s)}\big(L(s)+t\big)\Big)-1\Big)\Big\},$$
--   and every other set keeps its weight.
--   3. **One round.** If $\sum_{s\in\mathcal S_e}w(s)\ge 1$ nothing changes. Otherwise $y(e)$ is the least $t\ge 0$ with $\sum_{s\in\mathcal S_e} w_s(t)\ge 1$; the weights become $w_s(y(e))$, the loads of the sets containing $e$ grow by $y(e)$, and $Y$ grows by $y(e)$.
--   4. **Run.** The state after the list $\sigma$ is obtained by applying the rounds in order from the all-zero state.
--
--   This is the paper's Line (ii)b with $a(i,j)\in\{0,1\}$, $a_i(\max)=1$, and the number $n$ of primal variables replaced by $\ell$, the bound on the number of non-zero coefficients of a constraint (p. 5). The paper describes the increase of $y(e)$ continuously and notes that a discrete implementation finds the minimal $y(e)$ satisfying the new constraint; the round above is that discrete implementation, and its outcome is the endpoint of the continuous process.
--
--   **Formalization Note** The instance is the published `SetCoverInstance` (elements `E`, set indices `T`, incidence `elemSets`, positive costs `c`) and `elementWeight inst w e` is $\sum_{s\in\mathcal S_e}w(s)$. The least $t$ is `sInf` of the set of admissible $t$; when no set contains $e$ that set is empty and `sInf` returns $0$, a case the theorems exclude by hypothesis. $\ell$ is a natural number cast to $\mathbb R$; the exponential is `Real.exp`.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, pp. 4-5, Section 3, scheme lines (i)-(ii) and the paragraph before Theorem 3.2 (a(i,j) in {0,1}, n replaced by ℓ); p. 12, Section 5.1 (the scheme applied to set cover)

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- State of the Section 3 scheme with `{0,1}` coefficients, run on a set-cover instance
(Buchbinder–Naor 2009, p. 5 and p. 12). The primal variables are the sets, the covering
constraints are the arriving elements.
* `w s` is the primal variable `x(s)` (the fractional weight `w(s)` of §5.1);
* `load s` is `∑_{k : s ∋ e_k} y(k)`, the sum of the dual variables of the elements that have
  arrived so far and lie in `s` (the exponent's sum `∑_k a(s,k) y(k)` of Line (ii)b);
* `dual` is the dual value `Y = ∑_k y(k)`. -/
structure FracState (T : Type*) where
  w : T → ℝ
  load : T → ℝ
  dual : ℝ

/-- Initially every primal and dual variable is zero (p. 4: "Initially, each variable `x(i)` is
initialized to zero"). -/
def FracState.init (T : Type*) : FracState T where
  w := fun _ => 0
  load := fun _ => 0
  dual := 0

/-- Line (ii)b with `a ∈ {0,1}`, `a_i(max) = 1` and `n` replaced by `ℓ` (p. 5): when the arriving
element `e` has its dual variable at value `t`, every set `s ∋ e` has primal value
`max (w s, (1/ℓ)(exp((B/(2 c(s)))·(load s + t)) − 1))`; sets not containing `e` are unchanged. -/
noncomputable def augWeight {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) (t : ℝ) :
    T → ℝ :=
  fun s => if s ∈ inst.elemSets e then
      max (st.w s) ((1 / (ℓ : ℝ)) * (Real.exp (B / (2 * inst.c s) * (st.load s + t)) - 1))
    else st.w s

/-- The value the dual variable `y(e)` reaches in the round of `e` (p. 4–5: "find the minimal
`y(j)` such that the new primal constraint is satisfied"): the least `t ≥ 0` with
`∑_{s ∋ e} w_s(t) ≥ 1`. (When no set contains `e` the set is empty and `sInf` returns `0`; the
theorems exclude this case by hypothesis.) -/
noncomputable def dualStep {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ elementWeight inst (augWeight inst B ℓ st e t) e}

open Classical in
/-- One round of the scheme (p. 5, lines (i)–(ii)) on arrival of element `e`: if the constraint
`∑_{s ∋ e} x(s) ≥ 1` already holds nothing changes (`y(e) = 0`); otherwise `y(e)` is raised to
`dualStep`, the primal variables follow `augWeight`, and the loads and the dual value are
updated. -/
noncomputable def fracStep {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) : FracState T :=
  if 1 ≤ elementWeight inst st.w e then st
  else
    let y := dualStep inst B ℓ st e
    { w := augWeight inst B ℓ st e y
      load := fun s => if s ∈ inst.elemSets e then st.load s + y else st.load s
      dual := st.dual + y }

/-- The state of the scheme after the elements of the arrival list `σ` have been given, in order,
starting from the all-zero state. Elements may repeat. -/
noncomputable def fracRun {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (σ : List E) : FracState T :=
  σ.foldl (fracStep inst B ℓ) (FracState.init T)

end BNCovPack.SetCover


