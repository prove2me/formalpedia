-- Prove2me | Definitions.Def_IIDMultiItem_TwoPoint_Flow
-- name    : IIDMultiItem_TwoPoint_Flow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:56:29.881654+00:00
-- url     : https://prove2.me/theorems/ba7f5452-658e-4ae0-84b8-fbe4d3d09729
-- title:
--   Flows on the IC and IR constraints of one buyer and their virtual values (§2.2, (2.4), (2.6))
-- statement:
--   Fix a buyer $i$ and the reports $v_{-i}$ of the others. A **flow** for a type space $(T,f)$ consists of nonnegative weights $\lambda(t',t)$ on the IC constraints (type $t'$ does not gain by reporting $t$), for all $t',t\in T$, and $\lambda(t,\bot)$ on the IR constraints, satisfying flow conservation
--   $$\sum_{t''}\lambda(t,t'')+\lambda(t,\bot)\;=\;f(t)+\sum_{t'}\lambda(t',t)\qquad(t\in T).\tag{2.4}$$
--   The **virtual value** of item $j$ at type $t$ under the flow is
--   $$\Phi_j(t)\;=\;t_j-\frac1{f(t)}\sum_{t'}\lambda(t',t)\,(t'_j-t_j)\qquad(t\in T,\ j\in[m]).\tag{2.6}$$
--   For a mechanism $M$, a buyer $i$ and reports $v_{-i}$, a constraint is **tight** when it holds with equality: the IC constraint of $(t',t)$ when $u_i(t';v_{-i})=t'\cdot x_i(t,v_{-i})-s_i(t,v_{-i})$, the IR constraint of $t$ when $u_i(t;v_{-i})=0$. `TightOn` says that every constraint of positive weight in a given flow is tight.
--
--   **Formalization Note.** `Flow T` has fields `ic t' t` $=\lambda(t',t)$ and `ir t` $=\lambda(t,\bot)$; `IsFlow Ts lam` is nonnegativity plus (2.4); `virtualValue Ts lam t j` is (2.6), with $1/f(t)$ as written (every type has $f(t)>0$ in a prior).
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 11 (PDF 13), §2.2, (2.4), (2.6); p. 12 (PDF 14), Lemma 2.2 ('tight')

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Model

open scoped BigOperators

/-!
# Flows and virtual values (Cai–Devanur–Weinberg), for one buyer

Liu, Liu, Wang, *Optimal Multi-Item Auctions with I.I.D. Values*, arXiv:2610.11051 (held version,
PDF of 2026-11-03, sha256 983080a4…), §2.2, p. 11, (2.4) and (2.6).

Weights `ic t' t = λ(t', t)` on the IC constraints (type `t'` does not gain by reporting `t`) and
`ir t = λ(t, ⊥)` on the IR constraints. A flow is a nonnegative weighting satisfying flow
conservation (2.4); the virtual value (2.6) of item `j` at type `t` is
`Φ_j(t) = t_j − (1/f(t)) ∑_{t'} λ(t', t)(t'_j − t_j)`.
-/

namespace IIDMultiItem.TwoPoint

/-- Weights on the IC constraints (`ic t' t = λ(t', t)`) and on the IR constraints
(`ir t = λ(t, ⊥)`) of one buyer. -/
structure Flow (T : Type) where
  ic : T → T → ℝ
  ir : T → ℝ

namespace Flow

variable {T : Type} [Fintype T] {m : ℕ}

/-- `λ` is a flow for the type space `Ts`: all weights are nonnegative and (2.4)
`∑_{t''} λ(t, t'') + λ(t, ⊥) = f(t) + ∑_{t'} λ(t', t)` holds for every type `t`. -/
def IsFlow (Ts : TypeSpace T m) (lam : Flow T) : Prop :=
  (∀ t' t, 0 ≤ lam.ic t' t) ∧ (∀ t, 0 ≤ lam.ir t) ∧
    ∀ t, (∑ t'', lam.ic t t'') + lam.ir t = Ts.pmf t + ∑ t', lam.ic t' t

/-- The virtual value (2.6): `Φ_j(t) = t_j − (1/f(t)) ∑_{t'} λ(t', t)(t'_j − t_j)`. -/
noncomputable def virtualValue (Ts : TypeSpace T m) (lam : Flow T) (t : T) (j : Fin m) : ℝ :=
  Ts.val t j - (1 / Ts.pmf t) * ∑ t', lam.ic t' t * (Ts.val t' j - Ts.val t j)

end Flow

namespace Mechanism

variable {T : Type} {n m : ℕ}

/-- For buyer `i` and the others' reports `v_{-i}` (the other coordinates of `v`): every
constraint of positive weight in `lam` is tight, i.e. `u(t') = t' · x(t) − s(t)` whenever
`λ(t', t) > 0` and `u(t) = 0` whenever `λ(t, ⊥) > 0`. -/
def TightOn (M : Mechanism T n m) (Ts : TypeSpace T m) (i : Fin n) (v : Fin n → T)
    (lam : Flow T) : Prop :=
  (∀ t' t, 0 < lam.ic t' t → M.util Ts i v t' = M.payoff Ts i v t' t) ∧
    ∀ t, 0 < lam.ir t → M.util Ts i v t = 0

end Mechanism

end IIDMultiItem.TwoPoint


