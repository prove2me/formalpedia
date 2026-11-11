-- Prove2me | Definitions.Def_IncApproxVC_Oblivious_IncMaxFlow
-- name    : IncApproxVC_Oblivious_IncMaxFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:18.607208+00:00
-- url     : https://prove2.me/theorems/d71240fe-06eb-429a-baec-4600c45b7ab5
-- title:
--   The interface of $\mathrm{IncMaxFlow}(s,t,F,U)$: operations, caller requirements, internally maintained flow and its guarantees
-- statement:
--   This file fixes the operations, the caller's obligations and the guarantees of the incremental threshold max-flow data structure $\mathrm{IncMaxFlow}(s,t,F,U)$ of Theorem 5.2. The structure is initialized with a flow threshold $F$ and a capacity bound $U$, and holds a network $G'$ that starts with the two vertices $s=0$, $t=1$ and no edges. The operations are:
--   - `InsertVertex`: add a new vertex, the next unused number;
--   - `InsertEdge`$(a,b,u)$: add an edge from $a$ to $b$ with $u(e)=u$ and $l(e)=0$. Edges are numbered in order of insertion; parallel edges are allowed;
--   - `GetApproxFlow`$(e)$, `LowerBoundFlow`$(e,l)$ (set $l(e)=l$), `increaseUpperBound`$(e,u)$ (set $u(e)=u$) and `NextModifiedEdge`$()$, which returns an edge or $\bot$.
--
--   **Machine encoding.** Initialization writes the words $0,U$ and the real $F$. The operations write $[1]$, $[2,a,b,u]$, $[3,e]$, $[4,e,l]$, $[5,e,u]$ and $[6]$. Answers are read from real cell $-1$; `NextModifiedEdge` answers an edge index, or $-1$ for $\bot$, and on $\bot$ real cell $-2$ holds $1$ if $G'$ has an $s$–$t$ flow of value at least $F$ and $0$ otherwise. The **internally maintained flow** $f$ is read from the state: $f(e)$ is real cell $e$.
--
--   **Caller requirements** (`Valid`, checked against the run's own earlier answers, so the sequence may be adaptive):
--   - `InsertEdge` needs existing endpoints and an integer $u\in[1,U]$;
--   - `LowerBoundFlow`$(e,l)$ needs $e$ to be the answer of the latest `NextModifiedEdge`, with only `GetApproxFlow` calls since then, one of them on $e$. The answer $\bar f$ of the last such call must satisfy $u(e)-l\ge 1.01\,(u(e)-\bar f)+0.01$, with $l\ge 0$ an integer;
--   - `increaseUpperBound`$(e,u)$ needs an integer $u$ that is larger than the current $u(e)$ and at most $U$.
--
--   **Guarantees.** Write $a\approx_\alpha b$ for $\alpha^{-1}a\le b\le\alpha a$.
--   - `FlowFeasible`: after every operation $l\le f\le u$.
--   - `ApproxOK`: the answer $\bar f$ of `GetApproxFlow`$(e)$ satisfies $u(e)-\bar f\approx_{1.01}u(e)-f(e)$.
--   - `NMEAnswerOK`: `NextModifiedEdge` returns an existing edge or $\bot$.
--   - `ReportOK`: on $\bot$ the report is correct.
--   - `StableOK`: on $\bot$, no edge's residual capacity $u(e')-f(e')$ differs by a factor of at least $1.02$ from its value when $e'$ was last returned (or inserted, if never returned).
--   - `SaturationOK`: at every $\bot$ that reports no flow of value $F$ and comes before any $\bot$ that reported one, the following holds. For every $T\subseteq N^-[t]\setminus\{s\}$ such that $G'$ (current $u,l$) has an $s$–$T$ flow of value at least $F$, some edge $(v,t)$ with $v\in T\setminus\{t\}$ has $f((v,t))\ge u((v,t))/4$.
--
--   **Formalization Note.** The guarantee of p. 15 is printed "at any point in time before NextModifiedEdge has reported success while returning $\bot$". Taken literally it fails for every data structure: with $T=\{t\}$ it forbids an $s$–$t$ flow of value $F$ even right after an insertion that creates one and before the next `NextModifiedEdge`. It is therefore stated at the returns of $\bot$, which is where the proof of Lemma 5.5 applies it. The counters `numModifying`, `numGetApprox`, `numNext` and `numReturned` feed the time bound of Theorem 5.2.
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), pp. 14–15, Theorem 5.2 (interface of IncMaxFlow(s, t, F, U)); p. 13 (a ≈_α b)

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Flow
import Definitions.Def_IncApproxVC_Oblivious_Online

/-!
# The interface of the incremental threshold max-flow data structure `IncMaxFlow(s, t, F, U)`

Adena, Henzinger, Rutschmann, *Incremental Approximate Vertex Connectivity via Almost-Linear Time
Local Cut Algorithms*, STOC 2027 submission (manuscript sha256 d6baac6b…), pp. 14–15, Theorem 5.2.

**Operations.** The structure starts from the network `G′` with the two vertices `s = 0`, `t = 1`
and no edges. `InsertVertex` adds the next vertex (the `k`-th inserted vertex is `k + 1`, so the
caller's name for a new vertex is fixed by the order of insertion). `InsertEdge(a, b, u)` adds an
edge from `a` to `b` with `u(e) = u` and `l(e) = 0`; edges are numbered `0, 1, …` in order of
insertion, parallel edges allowed. `GetApproxFlow(e)`, `LowerBoundFlow(e, l)`,
`increaseUpperBound(e, u)` and `NextModifiedEdge()` are as on p. 15. `netAfter ops k` is the network
(vertex count, edge ends, `u`, `l`) after the first `k` operations, and `Net.toFlowNet` its flow
network on the vertex type `ℕ`.

**Machine encoding.** Initialization writes the integer words `[0, U]` and the real word `F`.
The operations write `[1]`, `[2, a, b, u]`, `[3, e]`, `[4, e, l]`, `[5, e, u]`, `[6]`
respectively (layout of `runOps`). The answer of `GetApproxFlow` is real cell `−1`. The answer of
`NextModifiedEdge` is real cell `−1`: the index of the returned edge, or `−1` for `⊥`; on `⊥`,
real cell `−2` holds the report, `1` if an `s–t` flow of value at least `F` exists in `G′` and `0`
if not. The internally maintained flow `f` is read from the state: `f(e)` is real cell `e`
(`e = 0, 1, 2, …`).

**Requirements on the caller (`Valid`).** These are the conditions of p. 15, checked against the
run's own answers, so the operation sequence may depend on earlier answers.
* `InsertEdge`: both ends exist and `u ∈ [1, U]` is an integer.
* `LowerBoundFlow(e, l)`: `e` was returned by the latest `NextModifiedEdge` and only
  `GetApproxFlow` calls came after that; among them is a call `GetApproxFlow(e)`, and the last such
  call's answer `f̄` satisfies `u(e) − l ≥ 1.01 · (u(e) − f̄) + 0.01` with `l ≥ 0` an integer.
* `increaseUpperBound(e, u)`: `u` is an integer, larger than the current `u(e)`, and at most `U`
  (`U` is the upper bound for the capacity of edges).

**Guarantees.**
* `FlowFeasible`: after every operation the internal flow respects `l ≤ f ≤ u` on every edge.
* `ApproxOK`: the answer `f̄` of `GetApproxFlow(e)` has `u(e) − f̄ ≈_{1.01} u(e) − f(e)`, where
  `a ≈_α b` means `α⁻¹ a ≤ b ≤ α a` (p. 13).
* `NMEAnswerOK`: `NextModifiedEdge` returns an existing edge or `⊥`.
* `ReportOK`: on `⊥` the report is correct.
* `StableOK`: on `⊥`, no edge's residual capacity `u(e′) − f(e′)` has changed by a factor of at least
  `1.02` since `e′` was last returned by `NextModifiedEdge` (or since its insertion, if it never
  was); `Changed a b` is `a ≠ b` together with `b ≥ 1.02 a` or `a ≥ 1.02 b`.
* `SaturationOK`: at every return of `⊥` that reports no flow of value `F`, provided no earlier `⊥`
  reported one, the following holds. For every `T ⊆ N⁻[t] \ {s}` such that `G′` (current `u`, `l`)
  admits an `s–T` flow of value at least `F`, some edge `(v, t)` with `v ∈ T \ {t}` has
  `f((v, t)) ≥ u((v, t))/4`.
* `numModifying` counts the `InsertVertex`, `InsertEdge`, `LowerBoundFlow` and
  `increaseUpperBound` calls; `numGetApprox` and `numNext` count the `GetApproxFlow` and
  `NextModifiedEdge` calls; `numReturned` counts the edges returned by `NextModifiedEdge`.
-/

namespace IncApproxVC.Oblivious

namespace IncMaxFlow

open Classical

/-- An operation of `IncMaxFlow` after its initialization. -/
inductive Op where
  /-- `InsertVertex(v)`: add the next vertex, with no incident edges. -/
  | insertVertex
  /-- `InsertEdge(e, u)`: add the edge `e = (tail, head)` with `u(e) = cap`, `l(e) = 0`. -/
  | insertEdge (tail head cap : ℕ)
  /-- `GetApproxFlow(e)`. -/
  | getApproxFlow (e : ℕ)
  /-- `LowerBoundFlow(e, l)`: set `l(e) = l`. -/
  | lowerBoundFlow (e l : ℕ)
  /-- `increaseUpperBound(e, u)`: set `u(e) = cap`. -/
  | increaseUpperBound (e cap : ℕ)
  /-- `NextModifiedEdge()`. -/
  | nextModifiedEdge
  deriving DecidableEq

/-- The integer words of an operation. -/
def Op.words : Op → List ℤ
  | .insertVertex => [1]
  | .insertEdge a b c => [2, (a : ℤ), (b : ℤ), (c : ℤ)]
  | .getApproxFlow e => [3, (e : ℤ)]
  | .lowerBoundFlow e l => [4, (e : ℤ), (l : ℤ)]
  | .increaseUpperBound e c => [5, (e : ℤ), (c : ℤ)]
  | .nextModifiedEdge => [6]

/-- The machine operations: initialization with `[0, U]` and the real word `F`, then `ops`. -/
def machineOps (U : ℕ) (F : ℝ) (ops : List Op) : List (List ℤ × List ℝ) :=
  ([0, (U : ℤ)], [F]) :: ops.map fun o => (o.words, [])

/-- The network `G′`: the number of vertices (`0 = s`, `1 = t`, then the inserted ones), the ends
of the edges in order of insertion, and the current upper and lower bounds by edge index. -/
structure Net where
  /-- The vertices are `0, …, numVertices − 1`. -/
  numVertices : ℕ
  /-- `ends[e] = (tail, head)` of edge `e`. -/
  ends : List (ℕ × ℕ)
  /-- The upper bound `u(e)`. -/
  up : ℕ → ℝ
  /-- The lower bound `l(e)`. -/
  low : ℕ → ℝ

/-- The initial network: `s`, `t`, no edges. -/
def Net.init : Net := ⟨2, [], fun _ => 0, fun _ => 0⟩

/-- The effect of an operation on the network. -/
def Net.step (G : Net) : Op → Net
  | .insertVertex => { G with numVertices := G.numVertices + 1 }
  | .insertEdge a b c =>
      { G with
        ends := G.ends ++ [(a, b)]
        up := Function.update G.up G.ends.length (c : ℝ)
        low := Function.update G.low G.ends.length 0 }
  | .lowerBoundFlow e l => { G with low := Function.update G.low e (l : ℝ) }
  | .increaseUpperBound e c => { G with up := Function.update G.up e (c : ℝ) }
  | .getApproxFlow _ => G
  | .nextModifiedEdge => G

/-- The network after the first `k` operations. -/
def netAfter (ops : List Op) (k : ℕ) : Net :=
  (ops.take k).foldl Net.step Net.init

/-- The flow network of `G′` on the vertex type `ℕ`, with edges `Fin |ends|`. -/
def Net.toFlowNet (G : Net) : FlowNet ℕ (Fin G.ends.length) where
  tail := fun e => (G.ends.get e).1
  head := fun e => (G.ends.get e).2
  up := fun e => G.up e
  low := fun e => G.low e

/-- `N⁻[t] = {t} ∪ N⁻(t)` in `G′`, with `t = 1`. -/
def Net.closedInSink (G : Net) : Finset ℕ :=
  insert 1 ((G.ends.filter fun p => p.2 = 1 ∧ p.1 ≠ 1).map Prod.fst).toFinset

section Run

variable (P : PNormReg.Program) (ω : ℕ → Bool) (fuel U : ℕ) (F : ℝ) (ops : List Op)

/-- The machine state after the initialization and the first `k` operations. -/
noncomputable def state (k : ℕ) : PNormReg.State :=
  runOps P ω fuel (machineOps U F ops) (k + 1)

/-- The answer of operation `j` (real cell `−1`). -/
noncomputable def ans (j : ℕ) : ℝ :=
  (state P ω fuel U F ops (j + 1)).core.mem (-1)

/-- The report of operation `j` (real cell `−2`). -/
noncomputable def report (j : ℕ) : ℝ :=
  (state P ω fuel U F ops (j + 1)).core.mem (-2)

/-- The internally maintained flow after the first `k` operations: `f(e)` is real cell `e`. -/
noncomputable def flow (k : ℕ) (e : ℕ) : ℝ :=
  (state P ω fuel U F ops k).core.mem (e : ℤ)

/-- The residual capacity `u(e) − f(e)` after the first `k` operations. -/
noncomputable def residual (k : ℕ) (e : ℕ) : ℝ :=
  (netAfter ops k).up e - flow P ω fuel U F ops k e

/-- Operation `j` is `NextModifiedEdge` and returned the edge `e`. -/
def Returned (j e : ℕ) : Prop :=
  ops[j]? = some .nextModifiedEdge ∧ ans P ω fuel U F ops j = (e : ℝ)

/-- Operation `j` is `NextModifiedEdge` and returned `⊥`. -/
def Bottom (j : ℕ) : Prop :=
  ops[j]? = some .nextModifiedEdge ∧ ans P ω fuel U F ops j = -1

/-- The requirements of p. 15 on every operation, checked against the run's answers. -/
def Valid : Prop :=
  ∀ j : ℕ, ∀ o : Op, ops[j]? = some o →
    match o with
    | .insertEdge a b c =>
        a < (netAfter ops j).numVertices ∧ b < (netAfter ops j).numVertices ∧ 1 ≤ c ∧ c ≤ U
    | .getApproxFlow e => e < (netAfter ops j).ends.length
    | .lowerBoundFlow e l =>
        e < (netAfter ops j).ends.length ∧
        ∃ i, i < j ∧ Returned P ω fuel U F ops i e ∧
          (∀ i', i < i' → i' < j → ∃ e', ops[i']? = some (.getApproxFlow e')) ∧
          ∃ i'', i < i'' ∧ i'' < j ∧ ops[i'']? = some (.getApproxFlow e) ∧
            (∀ i''', i'' < i''' → i''' < j → ops[i''']? ≠ some (.getApproxFlow e)) ∧
            1.01 * ((netAfter ops j).up e - ans P ω fuel U F ops i'') + 0.01 ≤
              (netAfter ops j).up e - (l : ℝ)
    | .increaseUpperBound e c =>
        e < (netAfter ops j).ends.length ∧ (netAfter ops j).up e < (c : ℝ) ∧ c ≤ U
    | .insertVertex => True
    | .nextModifiedEdge => True

/-- After the initialization and after every operation, `l ≤ f ≤ u` on every edge. -/
def FlowFeasible : Prop :=
  ∀ k, k ≤ ops.length → ∀ e, e < (netAfter ops k).ends.length →
    (netAfter ops k).low e ≤ flow P ω fuel U F ops k e ∧
      flow P ω fuel U F ops k e ≤ (netAfter ops k).up e

/-- `GetApproxFlow(e)` returns `f̄(e)` with `u(e) − f̄(e) ≈_{1.01} u(e) − f(e)`. -/
def ApproxOK : Prop :=
  ∀ j e, ops[j]? = some (.getApproxFlow e) →
    ((netAfter ops (j + 1)).up e - ans P ω fuel U F ops j) / 1.01 ≤
        residual P ω fuel U F ops (j + 1) e ∧
      residual P ω fuel U F ops (j + 1) e ≤
        1.01 * ((netAfter ops (j + 1)).up e - ans P ω fuel U F ops j)

/-- `NextModifiedEdge()` returns an existing edge or `⊥`. -/
def NMEAnswerOK : Prop :=
  ∀ j, ops[j]? = some .nextModifiedEdge →
    ans P ω fuel U F ops j = -1 ∨
      ∃ e, e < (netAfter ops (j + 1)).ends.length ∧ ans P ω fuel U F ops j = (e : ℝ)

/-- On `⊥`, the report says correctly whether `G′` has an `s–t` flow of value at least `F`. -/
def ReportOK : Prop :=
  ∀ j, Bottom P ω fuel U F ops j →
    (report P ω fuel U F ops j = 1 ∧ (netAfter ops (j + 1)).toFlowNet.MaxFlowAtLeast 0 1 F) ∨
      (report P ω fuel U F ops j = 0 ∧ ¬ (netAfter ops (j + 1)).toFlowNet.MaxFlowAtLeast 0 1 F)

/-- `τ` is the reference time of edge `e` for a call at time `j`: the last earlier call of
`NextModifiedEdge` that returned `e`, or, if there is none, the operation that inserted `e`. -/
def IsMark (j e τ : ℕ) : Prop :=
  τ < j ∧
    ((Returned P ω fuel U F ops τ e ∧
        ∀ τ', τ < τ' → τ' < j → ¬ Returned P ω fuel U F ops τ' e) ∨
      ((∃ a b c, ops[τ]? = some (.insertEdge a b c)) ∧ (netAfter ops τ).ends.length = e ∧
        ∀ τ', τ' < j → ¬ Returned P ω fuel U F ops τ' e))

/-- `a` and `b` differ by a multiplicative factor of at least `1.02`. -/
def Changed (a b : ℝ) : Prop :=
  a ≠ b ∧ (1.02 * a ≤ b ∨ 1.02 * b ≤ a)

/-- On `⊥`, no residual capacity has changed by a factor `1.02` since the edge's reference time. -/
def StableOK : Prop :=
  ∀ j, Bottom P ω fuel U F ops j → ∀ e, e < (netAfter ops (j + 1)).ends.length → ∀ τ,
    IsMark P ω fuel U F ops j e τ →
      ¬ Changed (residual P ω fuel U F ops (τ + 1) e) (residual P ω fuel U F ops (j + 1) e)

/-- The `1/4`-saturation guarantee at every `⊥` reporting no flow, before any `⊥` reported one. -/
def SaturationOK : Prop :=
  ∀ j, Bottom P ω fuel U F ops j → report P ω fuel U F ops j = 0 →
    (∀ i, i < j → Bottom P ω fuel U F ops i → report P ω fuel U F ops i ≠ 1) →
    ∀ T : Finset ℕ, T ⊆ (netAfter ops (j + 1)).closedInSink \ {0} →
      (∃ f' : Fin (netAfter ops (j + 1)).ends.length → ℝ, ∃ F' : ℝ, F ≤ F' ∧
        (netAfter ops (j + 1)).toFlowNet.IsSetFlow 0 T f' F') →
      ∃ e : Fin (netAfter ops (j + 1)).ends.length,
        (netAfter ops (j + 1)).toFlowNet.head e = 1 ∧
        (netAfter ops (j + 1)).toFlowNet.tail e ∈ T ∧
        (netAfter ops (j + 1)).toFlowNet.tail e ≠ 1 ∧
        (netAfter ops (j + 1)).up e / 4 ≤ flow P ω fuel U F ops (j + 1) e

/-- The number of edges returned by `NextModifiedEdge` (calls whose answer is not `⊥`). -/
noncomputable def numReturned : ℕ :=
  ((Finset.range ops.length).filter fun j =>
    ops[j]? = some .nextModifiedEdge ∧ ans P ω fuel U F ops j ≠ -1).card

end Run

/-- The number of `InsertVertex`, `InsertEdge`, `LowerBoundFlow` and `increaseUpperBound` calls. -/
def numModifying (ops : List Op) : ℕ :=
  (ops.filter fun o => match o with
    | .getApproxFlow _ => false
    | .nextModifiedEdge => false
    | _ => true).length

/-- The number of `GetApproxFlow` calls. -/
def numGetApprox (ops : List Op) : ℕ :=
  (ops.filter fun o => match o with
    | .getApproxFlow _ => true
    | _ => false).length

/-- The number of `NextModifiedEdge` calls. -/
def numNext (ops : List Op) : ℕ :=
  (ops.filter fun o => match o with
    | .nextModifiedEdge => true
    | _ => false).length

end IncMaxFlow

end IncApproxVC.Oblivious


