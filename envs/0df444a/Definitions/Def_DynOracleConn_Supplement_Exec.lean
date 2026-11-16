-- Prove2me | Definitions.Def_DynOracleConn_Supplement_Exec
-- name    : DynOracleConn_Supplement_Exec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:46:18.548567+00:00
-- url     : https://prove2.me/theorems/5700648d-5066-4e8f-bbdd-cad3483c5ee3
-- title:
--   Running a word-RAM program on dynamic $s$–$t$ connectivity: snapshot oracles, time, queries, space and answers
-- statement:
--   This definition runs a program $P$ of the word RAM with words of $w=a\lceil\log_2(n+1)\rceil$ bits on an instance $(n,s,t,S)$ and an update sequence $\sigma$ of an initially empty graph on $[n]$.
--
--   1. **Initialization.** The words $n,s,t,S$ are pending at the start. Update $k$ is delivered as the words $u,v,b$, where $b=1$ for an insertion and $b=0$ for a deletion. There is no free initialization phase: all work up to the end of the first update is charged to that update.
--   2. **Snapshot oracle.** The oracle instructions executed while update $k$ is processed are answered by the graph $G_k$ before the update. In the matrix model, $\mathrm{Adjacent}(u,v)$ returns $1$ if $uv$ is an edge and $0$ otherwise. In the list model, $\mathrm{Degree}$ and $\mathrm{Neighbor}$ are answered by the list oracle of $G_k$ with keys $\rho_k$, so the order of the lists may change from update to update.
--   3. **Answer.** An update ends when the machine blocks at a `read`. Its answer is correct if the words written meanwhile are exactly $[1]$ when $s$ and $t$ are connected in $G_{k+1}$, the graph after the update, and exactly $[0]$ otherwise.
--   4. **Records.** For every update the run records the number of steps, the number of oracle calls, the space reached by its end (cumulative from the start), and the output. If an update never completes, its time is $\infty$, its space and queries are suprema over the infinite run, and no later update is processed.
--
--   It also defines the comparison $x\le X$ of such a record with a real bound, and the statement that the maximum degree is at most $\Delta$ after every prefix.
--
--   This is the paper's model (§1.1): "At initialization, the algorithm is given n, s, t, and S. Each update is announced before it takes effect: while processing an insertion or deletion, the algorithm can inspect the graph as it was before the update, and it must report whether s and t are connected after the update." The update sequence and the orderings are fixed in advance (§7, p.42).
--
--   **Formalization Note** Vertices are coded $0,\dots,n-1$. An oracle reply to a call of the other model, or to a non-vertex, is $0$, which carries no information. The comparison with a real bound $X$ is $x\le\lfloor X\rfloor$, and $\infty\le X$ is false.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4; §2, p.15–16; §7, p.42

import Mathlib
import Definitions.Def_DynOracleConn_GraphAfter
import Definitions.Def_DynOracleConn_Supplement_Incremental
import Definitions.Def_DynOracleConn_Supplement_Machine

namespace DynOracleConn

/-!
# Running a word-RAM program on a dynamic s–t connectivity instance

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4: "At initialization,
the algorithm is given n, s, t, and S. Each update is announced before it takes effect: while
processing an insertion or deletion, the algorithm can inspect the graph as it was before the update,
and it must report whether s and t are connected after the update; the oracle then advances to the
updated graph." "Since the graph is initially empty, we allow no initialization time." "A word
contains Θ(log n) bits." §7, p.42: "we may assume that the update sequence and adjacency-list
orderings have been fixed in advance".

**Formalization Note.**
1. Word size: `wordSize a n = a · ⌈log₂ (n + 1)⌉` bits for a constant `a ≥ 1` fixed before `n`, so a
   word holds every vertex and every integer below `(n + 1)^a`.
2. The machine starts with the words `n, s, t, S` pending (vertices are coded by `v.val`, 0-based)
   and nothing else. Update `k` (0-based) is delivered as the three words `u.val, v.val, b` with
   `b = 1` for an insertion and `b = 0` for a deletion. No step is free: the work before the first
   completed configuration, including reading `n, s, t, S`, is charged to update `0`.
3. Snapshot semantics: the oracle instructions of update `k` are answered by the graph *before* it,
   `graphAfter σ k`; the update is processed until the machine is blocked at a `read` with nothing
   pending; its answer is the list of words written meanwhile, which must be `[1]` if `s` and `t` are
   connected in `graphAfter σ (k + 1)` and `[0]` otherwise.
4. Oracles: `matrixReply G` answers `Adjacent(u, v)` by `1` or `0` (and `0` if `u` or `v` is not a
   vertex); `listReply ρ G` answers `Degree(v)` and `Neighbor(v, j)` as `listOracleBy ρ G` (and `0`
   if `v` is not a vertex). An oracle of one model replies `0` to the calls of the other model, which
   carries no information. In the list model the order may change from update to update: update `k`
   is answered with the keys `ρ k`.
5. `exec` lists one record per processed update: its time (steps), its queries (oracle calls), the
   space reached by its end (`top` of the machine: one more than the largest address accessed since
   the start; cumulative, so also the space used during every earlier update), and its output
   (`none` if it never completes). When an update never completes, its time is `⊤`, its space and
   queries are suprema over the infinite run, and no later update is processed.
6. Comparisons with real bounds are `leR x X : x ≤ ⌊X⌋₊`, which for a natural number `x` and `X ≥ 0`
   is `x ≤ X`; for `x = ⊤` it is false.
-/

namespace Supplement

/-- The word size `a · ⌈log₂ (n + 1)⌉`. -/
def wordSize (a n : ℕ) : ℕ := a * Nat.clog 2 (n + 1)

/-- The words announcing an update: its endpoints and `1` for an insertion, `0` for a deletion. -/
def encodeUpdate {n : ℕ} (e : PunctSketch.Update n) : List ℕ :=
  [e.u.val, e.v.val, if e.insert then 1 else 0]

/-- The matrix-model oracle of `G` on word arguments. -/
noncomputable def matrixReply {n : ℕ} (G : SimpleGraph (Fin n)) : OCall → ℕ
  | .adj u v =>
      if h : u < n ∧ v < n then (if matrixOracle G (⟨u, h.1⟩, ⟨v, h.2⟩) then 1 else 0) else 0
  | .deg _ => 0
  | .nbr _ _ => 0

/-- The list-model oracle of `G`, with lists ordered by the keys `ρ`, on word arguments. -/
noncomputable def listReply {n : ℕ} (ρ : Fin n → Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    OCall → ℕ
  | .adj _ _ => 0
  | .deg v => if h : v < n then listOracleBy ρ G (.degree ⟨v, h⟩) else 0
  | .nbr v j => if h : v < n then listOracleBy ρ G (.neighbor ⟨v, h⟩ j) else 0

/-- The record of one update. -/
structure UpdStat : Type where
  /-- the number of steps (`⊤` if the update never completes) -/
  time : ℕ∞
  /-- the number of oracle calls -/
  queries : ℕ∞
  /-- one more than the largest memory address accessed since the start, by the end of the update -/
  space : ℕ∞
  /-- the words written during the update (`none` if it never completes) -/
  out : Option (List ℕ)

/-- Deliver the words `inp` of an update: they are appended to the pending input, and the output and
query counters of the update start empty. -/
def feed {w : ℕ} (c : Config w) (inp : List ℕ) : Config w :=
  { c with input := c.input ++ inp, output := [], queries := 0 }

/-- The record of the update processed from the configuration `c0` (just fed). -/
noncomputable def phaseStat {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (O : OCall → ℕ)
    (c0 : Config w) : UpdStat where
  time := time P ω O c0
  queries := ⨆ (t : ℕ) (_ : (t : ℕ∞) ≤ time P ω O c0), ((run P ω O c0 t).queries : ℕ∞)
  space := ⨆ (t : ℕ) (_ : (t : ℕ∞) ≤ time P ω O c0), ((run P ω O c0 t).top : ℕ∞)
  out := (complete P ω O c0).map Config.output

/-- The run from update index `k`, configuration `c` and current graph `G` on the remaining updates.
Update `k` is answered by the oracle `orc k G` of the graph before it. -/
noncomputable def execFrom {n w : ℕ} (P : Program) (ω : ℕ → BitVec w)
    (orc : ℕ → SimpleGraph (Fin n) → OCall → ℕ) :
    ℕ → Config w → SimpleGraph (Fin n) → List (PunctSketch.Update n) → List UpdStat
  | _, _, _, [] => []
  | k, c, G, e :: rest =>
      match complete P ω (orc k G) (feed c (encodeUpdate e)) with
      | none => [phaseStat P ω (orc k G) (feed c (encodeUpdate e))]
      | some c' =>
          phaseStat P ω (orc k G) (feed c (encodeUpdate e)) ::
            execFrom P ω orc (k + 1) c' (e.apply G) rest

/-- The run of the program `P` with word size `w` on the instance `(n, s, t, S)` and the update
sequence `σ` from the empty graph, on random tape `ω`, with oracles `orc`. -/
noncomputable def exec {n : ℕ} (P : Program) (w : ℕ) (s t : Fin n) (S : ℕ)
    (orc : ℕ → SimpleGraph (Fin n) → OCall → ℕ) (σ : List (PunctSketch.Update n))
    (ω : ℕ → BitVec w) : List UpdStat :=
  execFrom P ω orc 0 (Config.initial w [n, s.val, t.val, S]) ⊥ σ

open Classical in
/-- The correct answer word after update `k` (0-based): `1` if `s` and `t` are connected in the graph
after it, `0` otherwise. -/
noncomputable def ansWord {n : ℕ} (σ : List (PunctSketch.Update n)) (s t : Fin n) (k : ℕ) : ℕ :=
  if (graphAfter σ (k + 1)).Reachable s t then 1 else 0

/-- The record of update `k` exists and satisfies `p`. -/
def AtUpd (R : List UpdStat) (k : ℕ) (p : UpdStat → Prop) : Prop :=
  ∃ r, R[k]? = some r ∧ p r

/-- Every update of `σ` completes and writes exactly the correct answer word. -/
def AllAnswersCorrect {n : ℕ} (R : List UpdStat) (σ : List (PunctSketch.Update n)) (s t : Fin n) :
    Prop :=
  ∀ k < σ.length, AtUpd R k (fun r => r.out = some [ansWord σ s t k])

/-- `x ≤ X` for an extended natural `x` and a real bound `X` (as `x ≤ ⌊X⌋₊`). -/
def leR (x : ℕ∞) (X : ℝ) : Prop := x ≤ ((⌊X⌋₊ : ℕ) : ℕ∞)

open Classical in
/-- The graph has maximum degree at most `Δ` after every prefix of `σ`. -/
def MaxDegreeLE {n : ℕ} (σ : List (PunctSketch.Update n)) (Δ : ℕ) : Prop :=
  ∀ k ≤ σ.length, ∀ v : Fin n,
    (Finset.univ.filter (fun w => (graphAfter σ k).Adj v w)).card ≤ Δ

end Supplement

end DynOracleConn


