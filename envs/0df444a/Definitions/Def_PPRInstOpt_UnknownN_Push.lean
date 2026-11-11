-- Prove2me | Definitions.Def_PPRInstOpt_UnknownN_Push
-- name    : PPRInstOpt_UnknownN_Push
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:11:48.498356+00:00
-- url     : https://prove2.me/theorems/991e1ab2-1653-40d3-a485-f336f90d3384
-- title:
--   ForwardPush and BackwardPush (Algorithms 1 and 2), atomic and synchronous
-- statement:
--   **Forward push** at $u$ (Algorithm 1) acts on reserves and residues $(p_f,r_f)$: with $a=r_f(u)$, set $r_f(u)\leftarrow 0$, $p_f(u)\leftarrow p_f(u)+\alpha a$, and $r_f(v)\leftarrow r_f(v)+(1-\alpha)a/d_{\mathrm{out}}(u)$ for every out-neighbour $v$ of $u$. **Backward push** at $v$ (Algorithm 2) acts on $(p_b,r_b)$: with $a=r_b(v)$, set $r_b(v)\leftarrow 0$, $p_b(v)\leftarrow p_b(v)+\alpha a$, and
--   $$r_b(u)\leftarrow r_b(u)+\frac{(1-\alpha)\,a}{d_{\mathrm{out}}(u)}\quad\text{for every in-neighbour }u\text{ of }v.$$
--   A **synchronous** push on a set $C$ first records $a(u)=r(u)$ for all $u\in C$ and zeroes them, then distributes each $a(u)$; residue received during the step waits for the next one. The initial states are $(p_f,r_f)=(0,\mathbf 1_s)$ and $(p_b,r_b)=(0,\mathbf 1_t)$. All operations read the graph through the oracle only.
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 13, §2.1–2.2, Algorithms 1 and 2

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Graph

namespace PPRInstOpt.UnknownN

variable {V : Type} [DecidableEq V]

/-- Distribute an amount `a` forward from `u` (lines 3–5 of Algorithm 1, p. 13):
`p_f(u) += α a` and `r_f(v) += (1 - α) a / dout(u)` for every out-neighbour `v` of `u`.
The pair is `(p_f, r_f)`. -/
noncomputable def fwdPushAmt (o : Oracle V) (α : ℝ) (pr : (V → ℝ) × (V → ℝ)) (u : V) (a : ℝ) :
    (V → ℝ) × (V → ℝ) :=
  (Function.update pr.1 u (pr.1 u + α * a),
    (o.outs u).foldl
      (fun r v => Function.update r v (r v + (1 - α) * a / (o.outdeg u : ℝ))) pr.2)

/-- `ForwardPush(u)` (Algorithm 1, p. 13): `r ← r_f(u)`, `r_f(u) ← 0`, `p_f(u) ← p_f(u) + α r`,
and `r_f(v) ← r_f(v) + (1 - α) r / dout(u)` for each `v ∈ N_out(u)`. -/
noncomputable def fwdPush (o : Oracle V) (α : ℝ) (pr : (V → ℝ) × (V → ℝ)) (u : V) :
    (V → ℝ) × (V → ℝ) :=
  fwdPushAmt o α (pr.1, Function.update pr.2 u 0) u (pr.2 u)

/-- Distribute an amount `a` backward from `v` (lines 3–5 of Algorithm 2, p. 13):
`p_b(v) += α a` and `r_b(u) += (1 - α) a / dout(u)` for every in-neighbour `u` of `v`.
The pair is `(p_b, r_b)`. -/
noncomputable def bwdPushAmt (o : Oracle V) (α : ℝ) (pr : (V → ℝ) × (V → ℝ)) (v : V) (a : ℝ) :
    (V → ℝ) × (V → ℝ) :=
  (Function.update pr.1 v (pr.1 v + α * a),
    (o.ins v).foldl
      (fun r u => Function.update r u (r u + (1 - α) * a / (o.outdeg u : ℝ))) pr.2)

/-- `BackwardPush(v)` (Algorithm 2, p. 13): `r ← r_b(v)`, `r_b(v) ← 0`, `p_b(v) ← p_b(v) + α r`,
and `r_b(u) ← r_b(u) + (1 - α) r / dout(u)` for each `u ∈ N_in(v)`. -/
noncomputable def bwdPush (o : Oracle V) (α : ℝ) (pr : (V → ℝ) × (V → ℝ)) (v : V) :
    (V → ℝ) × (V → ℝ) :=
  bwdPushAmt o α (pr.1, Function.update pr.2 v 0) v (pr.2 v)

/-- Synchronous forward push on the (duplicate-free) list `C` (§3.1, pp. 15–16): every `u ∈ C`
pushes the residue it holds at the start; residue received during the step waits. -/
noncomputable def fwdSyncPush (o : Oracle V) (α : ℝ) (p r : V → ℝ) (C : List V) :
    (V → ℝ) × (V → ℝ) :=
  C.foldl (fun pr u => fwdPushAmt o α pr u (r u)) (p, fun x => if x ∈ C then 0 else r x)

/-- Synchronous backward push on the (duplicate-free) list `C` (§3.5, p. 22). -/
noncomputable def bwdSyncPush (o : Oracle V) (α : ℝ) (p r : V → ℝ) (C : List V) :
    (V → ℝ) × (V → ℝ) :=
  C.foldl (fun pr v => bwdPushAmt o α pr v (r v)) (p, fun x => if x ∈ C then 0 else r x)

/-- The initial forward state `(p_f, r_f) = (0, 1_s)` (§2.1, p. 12). -/
def fwdStart (s : V) : (V → ℝ) × (V → ℝ) :=
  (fun _ => 0, fun x => if x = s then 1 else 0)

/-- The initial backward state `(p_b, r_b) = (0, 1_t)` (§2.2, p. 13). -/
def bwdStart (t : V) : (V → ℝ) × (V → ℝ) :=
  (fun _ => 0, fun x => if x = t then 1 else 0)

end PPRInstOpt.UnknownN


