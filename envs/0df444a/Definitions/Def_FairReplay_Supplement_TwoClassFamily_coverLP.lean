-- Prove2me | Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP
-- name    : FairReplay_Supplement_TwoClassFamily_coverLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:48:09.7612+00:00
-- url     : https://prove2.me/theorems/13f020ff-1c6c-4d53-85dc-aa9da57dd6ce
-- title:
--   Control matrix $C$, control-cover program $C_{\mathrm{ctrl}}$, unmatched candidates $U$, $\bar c_x$
-- statement:
--   For a declared two-class family:
--
--   1. $C_{x,i}=1$ if group $S_i$ contains the candidate $x$ and another high vertex (a **same-background control** for $x$), and $0$ otherwise.
--   2. The **control-cover program** on a set of rows $B\subseteq A$ is
--   $$C^{B}_{\mathrm{ctrl}}=\min_{q\ge 0}\Big\{c^\top q:\ \sum_i C_{x,i}q_i\ge 1\ \ \forall x\in B\Big\},$$
--   with $C_{\mathrm{ctrl}}=C^{A}_{\mathrm{ctrl}}$ (value $\infty$ if infeasible, $0$ if $B=\varnothing$).
--   3. The **unmatched candidates** are $U=\{x\in A: C_{x,i}=0\ \forall i\}$; a candidate is **observable** if some group contains it, and then $\bar c_x=\min\{c_i:x\in S_i\}$.
--   4. For a vector $q$, $\sum_{i:q_i>0}c_i$ is the rounding overhead of a schedule built from $q$.
--
--   **Formalization Note** $C$ is read from the proof of Theorem 10.9(i) (p.21). The program's value is an infimum in $[0,\infty]$; $\bar c_x$ is a real infimum, used only for observable $x$.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9, eqs. (66), (69), (70), p.19 and proof of (i), p.21 (PDF pp.21, 23)

import Mathlib
import Definitions.Def_FairReplay_Supplement_TwoClassFamily

namespace FairReplay.Supplement.TwoClassFamily

/-- `C_{x,i} = 1`: group `i` is a **same-background control** for the candidate `x` — it contains `x`
and another high vertex (Theorem 10.9, proof of (i), p.21: "If a queried group contains x and another
high vertex"). -/
def IsControl (F : TwoClassFamily) (x : Fin F.n) (i : Fin F.k) : Prop :=
  x ∈ F.S i ∧ ∃ y ∈ F.S i, y ≠ x ∧ F.high y = true

/-- The control matrix `C` as a `0/1` real matrix. -/
noncomputable def ctrl (F : TwoClassFamily) (x : Fin F.n) (i : Fin F.k) : ℝ := by
  classical exact if F.IsControl x i then 1 else 0

/-- A candidate `x` is **observable** if some legal group contains it. -/
def Observable (F : TwoClassFamily) (x : Fin F.n) : Prop :=
  ∃ i, x ∈ F.S i

/-- **The fractional control-cover program** (Sah, Zhang, Lian, *Testing Fairness of Evolving
Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…,
Theorem 10.9, eqs. (66) and (70), p.19 (PDF p.21)): `C_ctrl = min_{q ≥ 0} { c⊤q : C q ≥ 1 }` and
`C^{A∖U}_ctrl = min_{q ≥ 0} { c⊤q : C_{A∖U} q ≥ 1 }`, "with value zero if A ∖ U is empty".

`F.coverLP rows` is the infimum of `Σ_i c_i q_i` over `q ≥ 0` with `Σ_i C_{x,i} q_i ≥ 1` for every row
`x ∈ rows`. `F.Cctrl = F.coverLP F.A` is the paper's `C_ctrl`.

**Formalization Note** The infimum is taken in `[0, ∞]`: it is `∞` exactly when some row has no
control group (the program is infeasible), which is the paper's `C_ctrl = ∞`, and it is `0` when there
are no rows. When finite it is attained (a feasible linear program bounded below). -/
noncomputable def coverLP (F : TwoClassFamily) (rows : Finset (Fin F.n)) : ENNReal :=
  ⨅ (q : Fin F.k → ℝ) (_ : ∀ i, 0 ≤ q i) (_ : ∀ x ∈ rows, 1 ≤ ∑ i, F.ctrl x i * q i),
    ENNReal.ofReal (∑ i, F.c i * q i)

/-- `C_ctrl` (Theorem 10.9, eq. (66)): the control-cover program over all candidates. -/
noncomputable def Cctrl (F : TwoClassFamily) : ENNReal :=
  F.coverLP F.A

/-- `q` is an optimizer of the control-cover program on `rows` (feasible, attaining the infimum). -/
def IsCoverOptimizer (F : TwoClassFamily) (rows : Finset (Fin F.n)) (q : Fin F.k → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∀ x ∈ rows, 1 ≤ ∑ i, F.ctrl x i * q i) ∧
    ENNReal.ofReal (∑ i, F.c i * q i) = F.coverLP rows

/-- `Σ_{i : q_i > 0} c_i`, the rounding overhead of a schedule built from `q`. -/
noncomputable def supportCost (F : TwoClassFamily) (q : Fin F.k → ℝ) : ℝ := by
  classical exact ∑ i ∈ Finset.univ.filter (fun i => 0 < q i), F.c i

/-- The **unmatched candidates** `U = {x ∈ A : C_{x,i} = 0 ∀ i}` (Theorem 10.9, eq. (69), p.19):
candidates with no control-compatible legal group. -/
noncomputable def unmatched (F : TwoClassFamily) : Finset (Fin F.n) := by
  classical exact F.A.filter (fun x => ∀ i, ¬ F.IsControl x i)

/-- `c̄_x = min{c_i : x ∈ S_i}` (Theorem 10.9(iv), p.19): the cost of a cheapest group containing `x`.

**Formalization Note** A real `sInf`; it is the minimum of a finite nonempty set when `x` is
observable, the only case in which the theorems use it. -/
noncomputable def cbar (F : TwoClassFamily) (x : Fin F.n) : ℝ :=
  sInf (F.c '' {i | x ∈ F.S i})

end FairReplay.Supplement.TwoClassFamily


