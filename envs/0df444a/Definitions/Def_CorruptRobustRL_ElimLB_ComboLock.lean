-- Prove2me | Definitions.Def_CorruptRobustRL_ElimLB_ComboLock
-- name    : CorruptRobustRL_ElimLB_ComboLock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:06.488998+00:00
-- url     : https://prove2.me/theorems/e8fd3f35-3bbf-4169-8d4f-40aba8b1bac4
-- title:
--   App. A, p. 38 — the combination-lock instances ℳ and ℳ₀ on {x^{(0)},…,x^{(H)}} × [A] and the events ℰ^combi_k, ℰ^{no elim}_k, ℰ^adm_k
-- statement:
--   Fix $H\ge1$ and $A\ge2$. The environment has states $x^{(0)},\dots,x^{(H)}$ and actions $[A]=\{1,\dots,A\}$. The two **combination-lock** instances $\mathcal M$ and $\mathcal M_0$ share their transitions: for $h\in[H-1]$, action $a=1$ at $x^{(h)}$ moves deterministically to $x^{(h+1)}$; any action $a>1$ moves to the sink $x^{(0)}$; every action at the sink stays at the sink. Both start at $x^{(1)}$. Under $\mathcal M_0$ every reward is $0$; under $\mathcal M$ action $1$ at $x^{(H)}$ yields reward $1$ and every other pair yields reward $0$.
--
--   On the history of a uniformly action-eliminating algorithm, for an episode $k$:
--
--   1. $\mathcal E^{\mathrm{combi}}_k$: the learner plays $(a_{k;1},\dots,a_{k;H})=(1,\dots,1)$;
--   2. $\mathcal E^{\mathrm{no\,elim}}_k$: the Q-supervisor $\mathcal T_k$ eliminates no action, i.e.
--
--   $$
--   \mathcal E^{\mathrm{no\,elim}}_k=\{\mathscr A_{k;h}(x)=\mathcal A\ \forall x,h\}\cap\{\bar Q_{k;h}(x,a)\ge\max_{a'\in\mathcal A}\underline Q_{k;h}(x,a')\ \forall x,h,a\};
--   $$
--
--   3. $\mathcal E^{\mathrm{adm}}_k$: $\mathcal T_k$ is confidence-admissible with respect to the optimal actions and Q-functions of $\mathcal M_0$.
--
--   These instances and events carry the whole proof of the lower bound for action-eliminating algorithms.
--
--   **Formalization Note** States are `Fin (H+1)` with $x^{(j)}$ = `j` and the sink `0`; actions are `Fin A` and the paper's action $1$ is `0 : Fin A`. The paper does not state the initial distribution or the moves out of $x^{(H)}$; here the start is $x^{(1)}$ and every action at $x^{(H)}$ moves to the sink ($x^{(H)}$ is reachable only at the last stage, so the latter never matters). Episodes are 0-based.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 38, App. A (instances M, M_0; events ℰ^combi_k, ℰ^no elim_k, ℰ^adm_k)

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_Setting

namespace CorruptRobustRL.ElimLB

/-- Transitions of the combination lock (arXiv:1911.08689v4, App. A, p. 38) on the states
`x^{(0)}, …, x^{(H)}` (`Fin (H + 1)`, `x^{(0)}` the sink) and actions `Fin A`, where the paper's
action `1` is `0 : Fin A`: at `x^{(h)}`, `1 ≤ h ≤ H - 1`, action `1` moves to `x^{(h+1)}`;
every other move goes to the sink `x^{(0)}` (including all actions at `x^{(H)}`). -/
noncomputable def comboTrans (H A : ℕ) [NeZero A] (s : Fin (H + 1)) (a : Fin A) :
    PMF (Fin (H + 1)) :=
  if h : 1 ≤ s.val ∧ s.val < H ∧ a = 0 then PMF.pure ⟨s.val + 1, by omega⟩ else PMF.pure 0

/-- The combination lock `ℳ`: start at `x^{(1)}`; reward `1` for action `1` at `x^{(H)}`,
reward `0` otherwise. -/
noncomputable def comboLock (H A : ℕ) [NeZero A] : Instance (Fin (H + 1)) (Fin A) where
  p0 := PMF.pure 1
  p := comboTrans H A
  R := fun s a => if s.val = H ∧ a = 0 then PMF.pure 1 else PMF.pure 0
  hR := by
    intro s a r hr
    split_ifs at hr <;> simp_all

/-- The instance `ℳ₀`: same start and transitions as `ℳ`, all rewards `0`. -/
noncomputable def comboLock0 (H A : ℕ) [NeZero A] : Instance (Fin (H + 1)) (Fin A) where
  p0 := PMF.pure 1
  p := comboTrans H A
  R := fun _ _ => PMF.pure 0
  hR := by
    intro s a r hr
    simp_all

/-- `ℰ^combi_k`: the actions of episode `k` (0-based) are all the paper's action `1`. -/
def combi {H A : ℕ} [NeZero A] (k : ℕ)
    (run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A))) : Prop :=
  ∃ e, run[k]? = some e ∧ ∀ s ∈ e.2, s.2.1 = 0

/-- `ℰ^{no elim}_k`: the Q-supervisor of episode `k` eliminates no action. -/
def noElimEv {H A : ℕ} [NeZero A] (k : ℕ)
    (run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A))) : Prop :=
  ∃ e, run[k]? = some e ∧ NoElim e.1

/-- `ℰ^adm_k`: the Q-supervisor of episode `k` is confidence-admissible for `ℳ₀`. -/
def admEv {H A : ℕ} [NeZero A] (k : ℕ)
    (run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A))) : Prop :=
  admEvent (comboLock0 H A) k run

end CorruptRobustRL.ElimLB


