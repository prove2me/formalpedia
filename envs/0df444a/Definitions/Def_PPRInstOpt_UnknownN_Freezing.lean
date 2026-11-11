-- Prove2me | Definitions.Def_PPRInstOpt_UnknownN_Freezing
-- name    : PPRInstOpt_UnknownN_Freezing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:12:36.882982+00:00
-- url     : https://prove2.me/theorems/d574847b-5f6e-4055-91cc-99b936105975
-- title:
--   ForwardPushWithFreezing and BackwardPushWithFreezing (Algorithms 6 and 7) with their iterates and RAM time
-- statement:
--   Both algorithms are state machines run through the oracle from a start vertex $x$ ($s$, resp. $t$) with a budget $\kappa\ge 1$. The state holds residues $r$, reserves $p$, the frozen set $F$, the vertices reached so far, the candidate sets $C^{(k)}$ (with $C^{(0)}=\{x\}$), the number of completed iterations, the remaining budget $\kappa'$, the last computed $R_f$ (resp. $\bar r_b$), a stop flag and the RAM time. Initially $r=\mathbf 1_x$, $p=0$, $F=\emptyset$.
--
--   **Algorithm 6** (iteration $\ell$): $R_f=\sum_{u\notin F}r(u)$; $C^{(\ell)}=\{u\notin F: r(u)>0,\ r(u)/d_{\mathrm{out}}(u)\ge R_f/\kappa\}\cup(C^{(\ell-1)}\setminus F)$; stop if $C^{(\ell)}=\emptyset$, $\sum_{C^{(\ell)}}r<R_f/2$, or $\sum_{C^{(\ell)}}d_{\mathrm{out}}>\kappa'$; otherwise push synchronously on $C^{(\ell)}$, decrease $\kappa'$ by $\sum_{C^{(\ell)}}d_{\mathrm{out}}$, and if $\ell\ge L_f$ freeze $C^{(\ell-L_f)}$, where
--   $$L_f=\Big\lceil\log_{1-\alpha/2}\frac{\varepsilon_r}{8\kappa^2}\Big\rceil,\qquad L_b=\Big\lceil\log_{1-\alpha/2}\frac{\varepsilon_r\alpha^2}{32\kappa}\Big\rceil.$$
--   **Algorithm 7** is the backward analogue: $\bar r_b=\max_{v\notin F}r(v)$, activation $r(v)>0,\ r(v)\ge\alpha\bar r_b/2$, stop if $C^{(\ell)}=\emptyset$ or $\sum_{C^{(\ell)}}d_{\mathrm{in}}>\kappa'$, budget decrease $\sum_{C^{(\ell)}}d_{\mathrm{in}}$, freezing with $L_b$.
--
--   `fwdIter`/`bwdIter` give the state after $\ell$ steps (the superscript $(\ell)$ of §3.2 and §3.5: $\ell$ completed iterations); `fwdFinal`/`bwdFinal` the state at the first stop, whose fields are the outputs $r_f,p_f,F_f,R_f$ (resp. $r_b,p_b,F_b,\bar r_b$). `liveMass` is $\sum_{u\notin F}r(u)$ and `liveMax` is $\max_{v\notin F}r(v)$ ($0$ if all vertices are frozen).
--
--   **RAM time.** Each iteration is charged the cost of the §3.3 implementation: one unit per iteration, per candidate, per pushed or scanned edge (the out-neighbours of $C^{(\ell-1)}$), per frozen vertex, and $2(\lfloor\log_2(H+2)\rfloor+1)$ per binary-heap insertion (with its later deletion), $H$ the insertions so far; the heap receives the out-neighbours (Algorithm 7: in-neighbours) of every newly frozen vertex. Algorithm 7 is charged $1+d_{\mathrm{in}}(v)$ per candidate $v$ with positive residue, one unit per newly activated or frozen vertex, and its heap insertions.
--
--   **Formalization Note** Activation is restricted to vertices with positive residue (finding I1: with threshold $0$ the printed set contains vertices never reached). The bookkeeping that finds the candidate set is computed abstractly over the reached vertices and charged its RAM cost; arithmetic is exact.
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 16, 19-22, §3.1–3.3, §3.5, Algorithms 6 and 7

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Push

/-!
# ForwardPushWithFreezing and BackwardPushWithFreezing (Algorithms 6 and 7)

Each algorithm is a state machine driven through the adjacency-list `Oracle` only; it never sees
`V` as a whole (no `Fintype V` is available to it). The state after `ℓ` calls of the step function
is the state after `ℓ` completed iterations (the superscript `(ℓ)` of §3.2 and §3.5, which count
iterations from `0`); the step that breaks sets `done` and changes nothing else but `R`/`rbar` and
`cost`.

Conventions.
* Activation only among vertices with positive residue (reading of finding I1): the candidate set
  of iteration `ℓ` is `{u ∉ F : r(u) > 0, threshold} ∪ (C^(ℓ-1) \ F)`. Vertices with positive
  residue are exactly ones the algorithm has reached (`seen`), so the set is computed over `seen`.
* `cand k` is `C^(k)` with `cand 0 = [s]` (resp. `[t]`); freezing at the end of iteration `ℓ ≥ L`
  adds `C^(ℓ-L)` (line 13 of Algorithm 6, line 12 of Algorithm 7).
* `cost` is the RAM time: every primitive operation costs one unit. The bookkeeping of §3.3
  (finding newly activated vertices with a binary-heap priority queue plus a scan of the
  out-neighbours of `C^(ℓ-1)`; for Algorithm 7 its backward analogue) is computed abstractly and
  charged per iteration the cost of that implementation: one unit per iteration, per candidate,
  per scanned or pushed edge, per frozen vertex, and `2(⌊log₂(H+2)⌋+1)` per priority-queue
  insertion (an insertion and its later deletion in a binary heap holding at most `H + 1` entries,
  `H` the insertions so far). Algorithm 7 pushes only candidates with positive residue (a
  zero-residue push changes nothing), maintains `Σ_{C} din` incrementally, and charges its pushes
  `1 + din(v)` each.
-/

namespace PPRInstOpt.UnknownN

/-- `L_f = ⌈log_{1-α/2}(εr / (8 κ_f²))⌉` (line 2 of Algorithm 6, p. 16). -/
noncomputable def Lf (α εr : ℝ) (κ : ℕ) : ℕ :=
  ⌈Real.logb (1 - α / 2) (εr / (8 * (κ : ℝ) ^ 2))⌉₊

/-- `L_b = ⌈log_{1-α/2}(εr α² / (32 κ_b))⌉` (line 2 of Algorithm 7, p. 21). -/
noncomputable def Lb (α εr : ℝ) (κ : ℕ) : ℕ :=
  ⌈Real.logb (1 - α / 2) (εr * α ^ 2 / (32 * (κ : ℝ)))⌉₊

/-- Charge for `k` priority-queue insertions (and their later deletions) when `H` insertions have
been made in total. -/
def heapCharge (k H : ℕ) : ℕ := 2 * k * (Nat.log 2 (H + 2) + 1)

/-- The state of Algorithm 6 (or 7): residues `r`, reserves `p`, the frozen set, the vertices
reached so far, the candidate sets `C^(k)`, the number of completed iterations, the remaining
budget, the last computed `R_f` (resp. `\bar r_b`), the stop flag, the number of priority-queue
insertions, and the RAM time spent. -/
structure PushState (V : Type) where
  r : V → ℝ
  p : V → ℝ
  frozen : V → Bool
  seen : List V
  cand : ℕ → List V
  iter : ℕ
  budget : ℕ
  R : ℝ
  done : Bool
  heapIns : ℕ
  cost : ℕ

variable {V : Type} [DecidableEq V]

/-- Lines 1–6 of Algorithm 6 (resp. 1–5 of Algorithm 7) from the start vertex `x` with budget
`κ`: `r = 1_x`, `p = 0`, nothing frozen, `C^(0) = {x}`; `R` is `1` (the value of `R_f` and of
`\bar r_b` before the first iteration). -/
def pushInit (x : V) (κ : ℕ) : PushState V where
  r := fun y => if y = x then 1 else 0
  p := fun _ => 0
  frozen := fun _ => false
  seen := [x]
  cand := fun k => if k = 0 then [x] else []
  iter := 0
  budget := κ
  R := 1
  done := false
  heapIns := 0
  cost := 1

/-- One iteration of Algorithm 6, `ForwardPushWithFreezing(s, κ_f)` (p. 16), lines 8–13:
`R_f ← Σ_{u ∉ F_f} r_f(u)`; `C^(ℓ) ← {u ∉ F_f : r_f(u) > 0, r_f(u)/dout(u) ≥ R_f/κ_f} ∪
(C^(ℓ-1) \ F_f)`; break if `C^(ℓ)` is empty, `Σ_{C^(ℓ)} r_f < R_f/2`, or
`Σ_{C^(ℓ)} dout > κ'_f`; else push synchronously on `C^(ℓ)`, `κ'_f ← κ'_f - Σ_{C^(ℓ)} dout`, and if
`ℓ ≥ L_f` freeze `C^(ℓ-L_f)`. -/
noncomputable def fwdStep (o : Oracle V) (α εr : ℝ) (κ : ℕ) (st : PushState V) : PushState V :=
  if st.done then st else
  let ℓ := st.iter + 1
  let live := st.seen.filter (fun u => !st.frozen u)
  let R := (live.map st.r).sum
  let prev := (st.cand st.iter).filter (fun u => !st.frozen u)
  let new := live.filter (fun u => decide (u ∉ prev) && decide (0 < st.r u) &&
    decide (R / (κ : ℝ) ≤ st.r u / (o.outdeg u : ℝ)))
  let C := prev ++ new
  let mass := (C.map st.r).sum
  let work := (C.map o.outdeg).sum
  let scan := if st.iter = 0 then 0 else ((st.cand st.iter).map o.outdeg).sum
  let base := st.cost + 1 + C.length + scan
  if C = [] ∨ mass < R / 2 ∨ st.budget < work then
    { st with done := true, R := R, cost := base }
  else
    let pr := fwdSyncPush o α st.p st.r C
    let cand' := Function.update st.cand ℓ C
    let newFrozen :=
      if Lf α εr κ ≤ ℓ then (cand' (ℓ - Lf α εr κ)).filter (fun u => !st.frozen u) else []
    let ins := (newFrozen.map o.outdeg).sum
    { r := pr.2
      p := pr.1
      frozen := fun u => st.frozen u || decide (u ∈ newFrozen)
      seen := st.seen ++ ((C.flatMap o.outs).dedup.filter (fun v => v ∉ st.seen))
      cand := cand'
      iter := ℓ
      budget := st.budget - work
      R := R
      done := false
      heapIns := st.heapIns + ins
      cost := base + work + newFrozen.length + heapCharge ins (st.heapIns + ins) }

/-- One iteration of Algorithm 7, `BackwardPushWithFreezing(t, κ_b)` (p. 21), lines 7–12:
`\bar r_b ← max_{v ∉ F_b} r_b(v)`; `C^(ℓ) ← {v ∉ F_b : r_b(v) > 0, r_b(v) ≥ α \bar r_b / 2} ∪
(C^(ℓ-1) \ F_b)`; break if `C^(ℓ)` is empty or `Σ_{C^(ℓ)} din > κ_b` (remaining budget); else
push synchronously on `C^(ℓ)`, `κ_b ← κ_b - Σ_{C^(ℓ)} din`, and if `ℓ ≥ L_b` freeze
`C^(ℓ-L_b)`. -/
noncomputable def bwdStep (o : Oracle V) (α εr : ℝ) (κ : ℕ) (st : PushState V) : PushState V :=
  if st.done then st else
  let ℓ := st.iter + 1
  let live := st.seen.filter (fun v => !st.frozen v)
  let rbar := (live.map st.r).foldr max 0
  let prev := (st.cand st.iter).filter (fun v => !st.frozen v)
  let new := live.filter (fun v => decide (v ∉ prev) && decide (0 < st.r v) &&
    decide (α * rbar / 2 ≤ st.r v))
  let C := prev ++ new
  let work := (C.map o.indeg).sum
  let base := st.cost + 1 + new.length
  if C = [] ∨ st.budget < work then
    { st with done := true, R := rbar, cost := base }
  else
    let pr := bwdSyncPush o α st.p st.r C
    let cand' := Function.update st.cand ℓ C
    let newFrozen :=
      if Lb α εr κ ≤ ℓ then (cand' (ℓ - Lb α εr κ)).filter (fun v => !st.frozen v) else []
    let ins := (newFrozen.map o.indeg).sum
    let active := C.filter (fun v => decide (0 < st.r v))
    { r := pr.2
      p := pr.1
      frozen := fun v => st.frozen v || decide (v ∈ newFrozen)
      seen := st.seen ++ ((C.flatMap o.ins).dedup.filter (fun u => u ∉ st.seen))
      cand := cand'
      iter := ℓ
      budget := st.budget - work
      R := rbar
      done := false
      heapIns := st.heapIns + ins
      cost := base + (active.map (fun v => 1 + o.indeg v)).sum + newFrozen.length +
        heapCharge ins (st.heapIns + ins) }

/-- The state of Algorithm 6 after `ℓ` calls of its step (`ℓ` completed iterations while not
`done`). -/
noncomputable def fwdIter (o : Oracle V) (α εr : ℝ) (κ : ℕ) (s : V) (ℓ : ℕ) : PushState V :=
  (fwdStep o α εr κ)^[ℓ] (pushInit s κ)

/-- The state of Algorithm 7 after `ℓ` calls of its step. -/
noncomputable def bwdIter (o : Oracle V) (α εr : ℝ) (κ : ℕ) (t : V) (ℓ : ℕ) : PushState V :=
  (bwdStep o α εr κ)^[ℓ] (pushInit t κ)

/-- The output of Algorithm 6 (line 14): the state at the first break. Its fields `r`, `p`,
`frozen`, `R` are `r_f`, `p_f`, `F_f`, `R_f`; `cost` is its RAM time. (The algorithm breaks after
at most `κ_f + 1` steps on a graph with positive out-degrees, so the infimum is attained.) -/
noncomputable def fwdFinal (o : Oracle V) (α εr : ℝ) (κ : ℕ) (s : V) : PushState V :=
  fwdIter o α εr κ s (sInf {ℓ | (fwdIter o α εr κ s ℓ).done = true})

/-- The output of Algorithm 7 (line 13): `r_b`, `p_b`, `F_b`, `\bar r_b` (field `R`) and the RAM
time. -/
noncomputable def bwdFinal (o : Oracle V) (α εr : ℝ) (κ : ℕ) (t : V) : PushState V :=
  bwdIter o α εr κ t (sInf {ℓ | (bwdIter o α εr κ t ℓ).done = true})

section Fintype

variable [Fintype V]

/-- `R^(ℓ) = Σ_{u ∈ V \ F^(ℓ)} r^(ℓ)(u)` for a state (§3.2, p. 16). -/
noncomputable def liveMass (st : PushState V) : ℝ :=
  ∑ u, if st.frozen u then 0 else st.r u

/-- `\bar r^(ℓ) = max_{v ∈ V \ F^(ℓ)} r^(ℓ)(v)` for a state (§3.5, p. 22); `0` if every vertex is
frozen (all residues are nonnegative). -/
noncomputable def liveMax (st : PushState V) : ℝ :=
  (Finset.univ.filter (fun v => st.frozen v = false)).fold max 0 st.r

end Fintype

end PPRInstOpt.UnknownN


