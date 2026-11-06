-- Prove2me | Definitions.Def_DecodablePOMDP_Controller
-- name    : DecodablePOMDP_Controller
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:46.956212+00:00
-- url     : https://prove2.me/theorems/8eba9f7d-9434-4c0c-b34d-e9264ff22994
-- title:
--   Deterministic finite-state controllers, their policies and codes
-- statement:
--   A **deterministic finite-state controller** for horizon $H$, $A$ actions and $O$ observations has, for each stage $h\in[1:H-1]$, a number $k_h+1\ge1$ of memory states, an action table $\mathrm{act}_h:[k_h+1]\to[A]$ and an update table $\mathrm{upd}_h:[k_h+1]\times[O]\to\mathbb N$. Its run starts in memory $m_1=0$ and sets $m_{h+1}=\mathrm{upd}_h(m_h,y_{h+1})$; its policy is the deterministic history policy
--
--   $$\pi_h(a_{1:h-1},y_{2:h})=\mathrm{act}_h(m_h).$$
--
--   Its **code** lists, stage by stage, $\langle k_h\rangle$, the action table and the update table in binary.
--
--   This is the output format of Theorem 1: the algorithm of App. A.10 outputs such a controller.
--
--   **Formalization Note** A memory index is read modulo the memory size of its stage, so every table is a valid controller. The policy is returned as point masses.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 1, p.4; App. A.10, p.20

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_DecodablePOMDP_Value
import Definitions.Def_DecodablePOMDP_Code

namespace DecodablePOMDP

open ExponomialAssortment.FPTAS

/-- **Deterministic finite-state controller** (the output of Theorem 1; A.10, p.20). For each stage
`h ∈ [1 : H−1]` (index `h − 1`): `k + 1` memory states (`k = Controller.k i`), an action table
`act_h : [k_h + 1] → A` and an update table `upd_h : [k_h + 1] × O → ℕ` giving the memory at
stage `h + 1` after observing `y_{h+1}`. The run starts in memory `0`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Theorem 1, p.4 ("produces a deterministic
policy") and App. A.10, p.20 ("the resulting controller π̂ is deterministic"; "obtaining the action
and next memory by table lookup").

**Formalization Note.** Memory sizes are stored as `k + 1 ≥ 1`. An updated memory index is read
modulo the next stage's memory size, so every table is a valid finite-state controller. -/
structure Controller (H A O : ℕ) where
  k : Fin (H - 1) → ℕ
  act : (i : Fin (H - 1)) → Fin (k i + 1) → Fin A
  upd : (i : Fin (H - 1)) → Fin (k i + 1) → Fin O → ℕ

/-- **Memory of a controller** after a `t`-step history (newest first) of the original POMDP:
`m₁ = 0` and `m_{h+1} = upd_h(m_h, y_{h+1})` (indices read modulo the memory sizes). -/
def Controller.memAt {H A O : ℕ} (c : Controller H A O) :
    (t : ℕ) → Hist (Fin A) (Fin O) t → ℕ
  | 0, _ => 0
  | t + 1, hist =>
      if ht : t < H - 1 then
        c.upd ⟨t, ht⟩ ⟨c.memAt t (Fin.tail hist) % (c.k ⟨t, ht⟩ + 1), Nat.mod_lt _ (by omega)⟩
          (hist 0).2
      else 0

/-- **Policy of a controller** (R3 of the plan): at stage `h = t + 1 ≤ H − 1` it plays
`act_h(m_h)` with probability one, `m_h` the memory after the history; it is a deterministic
history policy `π_h(a_{1:h−1}, y_{2:h}) = act_h(m_h)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.10, p.20.

**Formalization Note.** Returned as point masses; at stages `≥ H` (never read) the vector is `0`. -/
def Controller.policy {H A O : ℕ} (c : Controller H A O) : PolicyFn (Fin A) (Fin O) :=
  fun t hist a =>
    if ht : t < H - 1 then
      (if a = c.act ⟨t, ht⟩ ⟨c.memAt t hist % (c.k ⟨t, ht⟩ + 1), Nat.mod_lt _ (by omega)⟩
        then 1 else 0)
    else 0

/-- **Binary code of a controller**: for each stage in order, `encodeNat k`, then the action table
and the update table entries (`encodeNat`), in index order. -/
def encodeController {H A O : ℕ} (c : Controller H A O) : List Bool :=
  encVec (fun i => encodeNat (c.k i) ++
    encVec (fun m => encodeNat (c.act i m).val) ++
    encVec (fun m => encVec (fun y => encodeNat (c.upd i m y))))

end DecodablePOMDP


