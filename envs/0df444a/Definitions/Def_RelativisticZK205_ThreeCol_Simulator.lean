-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Simulator
-- name    : RelativisticZK205_ThreeCol_Simulator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:04.336867+00:00
-- url     : https://prove2.me/theorems/a2b621fc-bf25-465e-a18c-610373476208
-- title:
--   The No-Signalling simulators of §5.1 as a local wiring of PR-boxes and one 3-COLZK
-- statement:
--   The simulators $S_1,S_2$ receive the graph $G$ (not the colouring) and the queries $((i,j),r)$ and $((i',j'),r')$. Let $h=\lceil\log_2|V|\rceil$ and write every vertex label as an $h$-bit string with bits $i_1,\dots,i_h$.
--
--   **Step 3.** A simulator whose query is not an edge aborts.
--
--   **Step 4 (comparator).** $S_1$ sets $x_1=\bar i_1$ and $S_2$ sets $x'_1=i'_1$. For $k=1,\dots,h-1$: a PR-box on inputs $x_k$ (from $S_1$) and $i'_{k+1}$ (from $S_2$) gives $y,y'$ with $y\oplus y'=x_k\wedge i'_{k+1}$; a PR-box on inputs $\bar i_{k+1}$ and $x'_k$ gives $z,z'$ with $z\oplus z'=x'_k\wedge\bar i_{k+1}$; then
--
--   $$
--   x_{k+1}=(x_k\wedge\bar i_{k+1})\oplus y\oplus z,\qquad x'_{k+1}=(x'_k\wedge i'_{k+1})\oplus y'\oplus z'.
--   $$
--
--   Finally $z_{00}=x_h$ and $z'_{00}=x'_h$.
--
--   **Step 5.** The same comparator on $(i,j')$, $(j,i')$ and $(j,j')$ gives $(z_{01},z'_{01})$, $(z_{10},z'_{10})$, $(z_{11},z'_{11})$.
--
--   **Steps 6–8.** One use of 3-COLZK on inputs $(z_{00},z_{01},z_{10},z_{11},r)$ and $(z'_{00},z'_{01},z'_{10},z'_{11},r')$ gives $(\ell_0,\ell_1)$ and $(\ell'_0,\ell'_1)$; $S_1$ replies $(w_i,w_j)=(\ell_0,\ell_1)$ and $S_2$ replies $(w'_{i'},w'_{j'})=(\ell'_0,\ell'_1)$.
--
--   The whole procedure is a local wiring over $\{\mathrm{PR},\text{3-COLZK}\}$: each simulator only ever uses its own query and its own box outputs. The file also defines the bare comparator as a channel on two labels, and the preprocessing phase (Steps 4–5) as a channel returning each simulator's table of $z$-bits.
--
--   **Formalization Note** $h$ is `Nat.clog 2 n` and the $k$-th bit of a label $i$ is `Nat.testBit i (k-1)` (least significant first; the source fixes no order). The comparator with $h:=k$ outputs the pair $(x_k,x'_k)$, because its first $k-1$ iterations are those of any longer run. An aborting simulator (invalid query) still takes part in every box instance, with constant inputs `false` (resp. the all-`false` table and $r=$ `false`), and replies `none`; since the boxes are No-Signalling this does not change the other simulator's law, and the source's simulator simply stops. For $h=0$ (at most one vertex, so no edge) the comparator has no first bit and its output is unused. The simulators' local computation is not given a running-time bound.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), §5.1, p.10, Simulator (S_1|{PR, 3-COLZK, V̂′}, S_2|{PR, 3-COLZK, V̂′})(G), Steps 3–8; p.11, proof of Theorem 1

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Channel
import Definitions.Def_RelativisticZK205_ThreeCol_PRBox
import Definitions.Def_RelativisticZK205_ThreeCol_ThreeColZK
import Definitions.Def_RelativisticZK205_ThreeCol_Protocol

/-!
# The No-Signalling simulators `(S₁ | {PR, 3-COLZK}, S₂ | {PR, 3-COLZK})(G)`

Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, *Relativistic Zero
Knowledge*, STOC 2027 submission #205 (October 2026), §5.1, p.10 (Steps 3–8 of the simulator) and
p.11 (proof of Theorem 1, channel count).

The simulators are a local wiring (`Wiring`, pp.4–5) over two boxes, the PR-box (Fig. 6) and
3-COLZK (Fig. 10). They take the graph `G` but **no colouring**.

Conventions.
* `h = ⌈log₂ |V|⌉ = Nat.clog 2 n`; a vertex `i : Fin n` is the integer `i ∈ {0, …, n-1}` and its
  `k`-th bit (`1 ≤ k ≤ h`) is `bit i (k - 1) = Nat.testBit i (k - 1)` (least significant bit
  first). Any injective `h`-bit encoding serves the source; this is one.
* An aborting simulator (Step 3) feeds the constant input `false` (resp. all-`false` bits and
  `r = false`) to every box it shares and outputs `none`.
-/

namespace RelativisticZK205.ThreeCol

/-- The two kinds of box available to the simulators. -/
inductive SimBox : Type
  | pr
  | colzk
  deriving DecidableEq

/-- Input alphabet (the same for both parties) of each simulator box. -/
abbrev SimBox.In : SimBox → Type
  | .pr => Bool
  | .colzk => ColzkIn

/-- Output alphabet (the same for both parties) of each simulator box. -/
abbrev SimBox.Out : SimBox → Type
  | .pr => Bool
  | .colzk => ColzkOut

/-- The channel of each simulator box: `prBox` (Fig. 6) or `threeColZK` (Fig. 10). -/
noncomputable def SimBox.channel : (k : SimBox) → Channel k.In k.In k.Out k.Out
  | .pr => prBox
  | .colzk => threeColZK

/-- The box family `{PR, 3-COLZK}`. -/
noncomputable def simFamily : BoxFamily where
  K := SimBox
  InA := SimBox.In
  InB := SimBox.In
  OutA := SimBox.Out
  OutB := SimBox.Out
  box := SimBox.channel

instance : DecidableEq simFamily.K := inferInstanceAs (DecidableEq SimBox)

/-- The bit of index `k` (0-based) of the integer label `i`; the source's `i_k` is `bit i (k - 1)`. -/
def bit (i : ℕ) (k : ℕ) : Bool := Nat.testBit i k

/-- One iteration `k` (`1 ≤ k ≤ h - 1`) of Step 4(b), p.10. A comparator party's local state is
`(context, own label, own current x)`: Alice holds `(c, i, x_k)`, Bob holds `(d, i', x'_k)`.
* First PR-box: Alice inputs `x_k`, Bob inputs `i'_{k+1}`; they obtain `y, y'` with
  `y ⊕ y' = x_k ∧ i'_{k+1}`. Alice stores `(x_k ∧ ī_{k+1}) ⊕ y`, Bob stores `y'`.
* Second PR-box: Alice inputs `ī_{k+1}`, Bob inputs `x'_k`; they obtain `z, z'` with
  `z ⊕ z' = x'_k ∧ ī_{k+1}`. Alice sets `x_{k+1} = (x_k ∧ ī_{k+1}) ⊕ y ⊕ z`, Bob sets
  `x'_{k+1} = (x'_k ∧ i'_{k+1}) ⊕ y' ⊕ z'`.
`actA`, `actB` say whether a party is active; an inactive (aborted) party inputs `false`. -/
noncomputable def cmpStep {C D : Type} (actA : C → Bool) (actB : D → Bool) (k : ℕ) :
    Wiring simFamily (C × ℕ × Bool) (D × ℕ × Bool) (C × ℕ × Bool) (D × ℕ × Bool) :=
  .call (k := SimBox.pr)
    (fun s => if actA s.1 then s.2.2 else false)
    (fun t => if actB t.1 then bit t.2.1 k else false)
    (fun s y => (s, xor (s.2.2 && !bit s.2.1 k) y))
    (fun t y' => (t, y'))
    (.call (k := SimBox.pr)
      (fun p => if actA p.1.1 then !bit p.1.2.1 k else false)
      (fun p => if actB p.1.1 then p.1.2.2 else false)
      (fun p z => (p.1.1, p.1.2.1, xor p.2 z))
      (fun p z' => (p.1.1, p.1.2.1, xor (xor (p.1.2.2 && bit p.1.2.1 k) p.2) z'))
      (.done id id))

/-- The iterations of Step 4(b) for the listed values of `k`, in order. -/
noncomputable def cmpSteps {C D : Type} (actA : C → Bool) (actB : D → Bool) : List ℕ →
    Wiring simFamily (C × ℕ × Bool) (D × ℕ × Bool) (C × ℕ × Bool) (D × ℕ × Bool)
  | [] => .done id id
  | k :: ks => (cmpStep actA actB k).comp (cmpSteps actA actB ks)

/-- Step 4, p.10: the comparator on labels of `h` bits, carrying an untouched context. Alice starts
from `(c, i)`, Bob from `(d, i')`.
(a) Alice sets `x₁ = ī₁`, Bob sets `x'₁ = i'₁`;
(b) for `k = 1, …, h - 1`, one iteration `cmpStep k`;
(c) Alice outputs `(c, z = x_h)`, Bob outputs `(d, z' = x'_h)`.
For `h = 0` there is no first bit and the output is not meaningful (no vertex pair needs it). -/
noncomputable def comparatorW {C D : Type} (actA : C → Bool) (actB : D → Bool) (h : ℕ) :
    Wiring simFamily (C × Bool) (D × Bool) (C × ℕ) (D × ℕ) :=
  ((cmpSteps actA actB (List.range' 1 (h - 1))).comp
      (.done (fun s => (s.1, s.2.2)) (fun t => (t.1, t.2.2)))).pre
    (fun s => (s.1, s.2, !bit s.2 0)) (fun t => (t.1, t.2, bit t.2 0))

/-- The bare comparator on `h`-bit labels as a channel: Alice inputs the label `i`, Bob the label
`i'`; Alice receives `x_h`, Bob receives `x'_h`. Running it with `h := k` gives the pair
`(x_k, x'_k)` reached after the first `k - 1` iterations of Step 4(b). -/
noncomputable def comparator (h : ℕ) : Channel ℕ ℕ Bool Bool := fun i i' =>
  ((comparatorW (C := Unit) (D := Unit) (fun _ => true) (fun _ => true) h).exec
      ((), i) ((), i')).map fun p => (p.1.2, p.2.2)

/-- A simulator's local state during preprocessing: its query and its table `z_uv` (`u, v : Bool`). -/
abbrev SimState (n : ℕ) : Type := Query n × (Bool → Bool → Bool)

/-- Overwrite the entry `z_uv` of a table. -/
def setZ (z : Bool → Bool → Bool) (u v b : Bool) : Bool → Bool → Bool :=
  fun a a' => if a = u ∧ a' = v then b else z a a'

/-- Steps 4–5, p.10: the comparator producing `(z_uv, z'_uv)` from the label `u` of `S₁`'s query
(`i` for `u = 0`, `j` for `u = 1`) and the label `v` of `S₂`'s query (`i'` or `j'`), with
`h = ⌈log₂ |V|⌉`. A simulator whose query is invalid is inactive (Step 3). -/
noncomputable def cmpUV {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Bool) :
    Wiring simFamily (SimState n) (SimState n) (SimState n) (SimState n) :=
  ((comparatorW (fun s : SimState n => decide (IsValid G s.1))
      (fun t : SimState n => decide (IsValid G t.1)) (Nat.clog 2 n)).comp
      (.done (fun p => (p.1.1, setZ p.1.2 u v p.2)) (fun p => (p.1.1, setZ p.1.2 u v p.2)))).pre
    (fun s => (s, ((labelOf u s.1 : Fin n) : ℕ))) (fun t => (t, ((labelOf v t.1 : Fin n) : ℕ)))

/-- Steps 4 and 5, p.10, as a wiring: the comparators for `(u, v) = (0,0), (0,1), (1,0), (1,1)`,
i.e. for `(i, i')`, `(i, j')`, `(j, i')`, `(j, j')`, in this order. Each party starts from its query
and an all-`false` table and ends with its query and its table `z_uv` (resp. `z'_uv`). -/
noncomputable def preprocessW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Wiring simFamily (SimState n) (SimState n) (Query n) (Query n) :=
  ((cmpUV G false false).comp ((cmpUV G false true).comp ((cmpUV G true false).comp
      ((cmpUV G true true).comp (.done id id))))).pre
    (fun q => (q, fun _ _ => false)) (fun q => (q, fun _ _ => false))

/-- The preprocessing phase as a channel: the simulators' queries in, their tables of `z`-bits out
(each together with its own query). -/
noncomputable def preprocess {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Channel (Query n) (Query n) (SimState n) (SimState n) :=
  (preprocessW G).exec

/-- Steps 6–8, p.10: one use of 3-COLZK. An active simulator inputs its table and its `r` and replies
`(w_i, w_j) = (ℓ₀, ℓ₁)` (resp. `(w'_{i'}, w'_{j'}) = (ℓ'₀, ℓ'₁)`); an aborted one inputs all-`false`
bits and `false`, and replies `none`. -/
noncomputable def colzkStepW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Wiring simFamily Reply Reply (SimState n) (SimState n) :=
  .call (k := SimBox.colzk)
    (fun s => if IsValid G s.1 then (s.2, s.1.2.2) else (fun _ _ => false, false))
    (fun t => if IsValid G t.1 then (t.2, t.1.2.2) else (fun _ _ => false, false))
    (fun s l => if IsValid G s.1 then some l else none)
    (fun t l => if IsValid G t.1 then some l else none)
    (.done id id)

/-- p.10: the whole simulator wiring, Steps 3–8: preprocessing (Steps 4–5) followed by one use of
3-COLZK (Steps 6–8). It depends on `G` only. -/
noncomputable def simWiring {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Wiring simFamily Reply Reply (Query n) (Query n) :=
  (preprocessW G).comp (colzkStepW G)

/-- The simulators' joint response channel: `S₁` receives `q₁`, `S₂` receives `q₂`, and they reply
to their verifiers. -/
noncomputable def simChannel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Channel (Query n) (Query n) Reply Reply :=
  (simWiring G).exec

end RelativisticZK205.ThreeCol


