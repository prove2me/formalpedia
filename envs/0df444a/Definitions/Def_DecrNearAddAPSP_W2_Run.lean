-- Prove2me | Definitions.Def_DecrNearAddAPSP_W2_Run
-- name    : DecrNearAddAPSP_W2_Run
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:07:41.64535+00:00
-- url     : https://prove2.me/theorems/4c0535f3-c8c5-42c6-b99a-3072c24c8572
-- title:
--   Running a word-RAM program on a decremental APSP instance: input words, total update time, and the estimate replayed from written records
-- statement:
--   The paper names no machine model. Algorithms run on the published randomized **word RAM** (`DynBrooks_Machine`): $w$-bit words with $w=a\lceil\log_2(n+2)\rceil$ for a constant $a$ fixed together with the program, unit-cost uniform random words read from a coin tape $\omega$, a `read` instruction that blocks until input is pending (so the program processes updates online and cannot look ahead), a `write` instruction, and one step per executed instruction.
--
--   **Input.** Initialization receives the words $n$, $W$, $m$ and then each edge of $G_0$ as $u,v,w(u,v)$ (in the order of an edge listing). After the machine reaches a **completed state** (blocked at a `read` with no input pending), the next update is delivered: a deletion as $0,u,v$, a weight increase to $c$ as $1,u,v,c$. The completed state after initialization is time $0$; the one after update $t$ is time $t$.
--
--   **Total update time.** $T(\omega)\in\mathbb N\cup\{\infty\}$ is the number of steps from the start through initialization and every update until the completed state after the last update, $\infty$ if some completed state is never reached. Reading each input word costs a step.
--
--   **The maintained estimate.** The program reports its distance matrix by writing **records**: three words $u,v,q$ set $d[u,v]$ to $\infty$ if $q=0$ and to $q-1$ otherwise. The estimate $d_t$ at time $t$ is the replay of every record written up to the completed state at time $t$, starting from $d[u,u]=0$ and $d[u,v]=\infty$ for $u\neq v$. Records naming a non-vertex, and a trailing incomplete record, are skipped.
--
--   This makes "maintains a distance estimate in total update time $T$" (p. 1, p. 7) a statement about one program: every change of $d$ is a write, and writes cost steps.
--
--   **Formalization Note** `stateAt`, `totalTime`, `outputAt` follow a run through a list of operations given by their words; `estAt` replays the records; `apspTime` is the total time of an APSP run. `log2 x` is `Real.logb 2 x`.
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 1 (§1: maintained estimate, total update time); pp. 6–7, §2

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic

namespace DecrNearAddAPSP.W2

/-! # Running a word-RAM program on a decremental instance: input words, total update time, and the
maintained distance estimate as a replay of written records

Koveshi, Roditty, Sapir, *First Near-Additive All-Pairs Approximate Shortest Paths in Decremental
Weighted Graphs*, arXiv:2611.04635 (PDF sha256 6bb2b230…), §1 p. 1 (PDF 3: "maintains a distance
estimate", "total update time"), §2 pp. 6–7 (PDF 8–9).

**Formalization Note.**
* The machine is the published word RAM `DynBrooks.Program` (`DynBrooks_Machine`): words of
  `a·⌈log₂(n + 2)⌉` bits (the constant `a` is fixed together with the program), unit-cost uniform
  random words on a coin tape, a `read` that blocks until input is pending (so an online program
  cannot look ahead), and every executed instruction one step.
* A run starts with the initialization words pending. After the completed state of initialization
  (time `0`), the words of each operation are delivered to the completed state that follows the
  previous one; the completed state after operation `t` is time `t`.
* The total time is the number of steps of initialization and of every operation, `∞` if some
  completed state is never reached.
* The APSP input is `n, W, m`, then every initial edge as the three words `u, v, w(uv)`; a deletion
  is the words `0, u, v`, a weight increase to `c` the words `1, u, v, c`.
* The maintained estimate `d_t` is the replay of every record written up to the completed state at
  time `t`, starting from `d[u, u] = 0` and `d[u, v] = ∞` for `u ≠ v`: the three words `u, v, q` set
  `d[u, v]` to `∞` if `q = 0` and to `q − 1` otherwise. A record naming a non-vertex, and a trailing
  incomplete record, are skipped. -/

open DynBrooks

/-- The word size `a·⌈log₂(n + 2)⌉` used for an `n`-vertex instance. -/
def wordSize (a n : ℕ) : ℕ := a * Nat.clog 2 (n + 2)

/-- `log₂ x` as a real number. -/
noncomputable def log2 (x : ℕ) : ℝ := Real.logb 2 x

/-- The starting configuration: program counter `0`, memory zero, coin cursor `0`, nothing written,
the initialization words pending. -/
def initConfig (w : ℕ) (inp : List ℕ) : Config w :=
  ⟨0, fun _ => 0, inp, 0, [], ∅⟩

/-- The state after a list of operations (each given by its words) from an optional completed
state, if every one of them completes. -/
noncomputable def stateFrom {w : ℕ} (P : Program) (ω : ℕ → BitVec w) :
    Option (Config w) → List (List ℕ) → Option (Config w)
  | none, _ => none
  | some c, [] => some c
  | some c, op :: ops => stateFrom P ω (complete P ω (feed c op)) ops

/-- The steps spent on a list of operations from an optional completed state: the sum of their
times, and `∞` once one of them does not complete. -/
noncomputable def workFrom {w : ℕ} (P : Program) (ω : ℕ → BitVec w) :
    Option (Config w) → List (List ℕ) → ℕ∞
  | none, _ => ⊤
  | some _, [] => 0
  | some c, op :: ops => time P ω (feed c op) + workFrom P ω (complete P ω (feed c op)) ops

/-- The completed state at time `t`: after initialization on `inp` and the first `t` operations of
`ops`, on tape `ω` (`none` if it is not reached). -/
noncomputable def stateAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) (t : ℕ) : Option (Config w) :=
  stateFrom P ω (complete P ω (initConfig w inp)) (ops.take t)

/-- The total time: every step of initialization and of every operation (`∞` if some run does not
complete). -/
noncomputable def totalTime (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) : ℕ∞ :=
  time P ω (initConfig w inp) + workFrom P ω (complete P ω (initConfig w inp)) ops

/-- Every word written up to the completed state at time `t` (empty if it is not reached). -/
noncomputable def outputAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) (t : ℕ) : List ℕ :=
  match stateAt P ω inp ops t with
  | some s => s.output
  | none => []

/-- The words of a decremental update: `0, u, v` deletes `{u, v}`; `1, u, v, c` raises the weight
of `{u, v}` to `c`. -/
def Upd.words {n : ℕ} : Upd n → List ℕ
  | .del u v => [0, u.val, v.val]
  | .inc u v c => [1, u.val, v.val, c]

/-- The APSP initialization words: `n`, `W`, the number of edges, and every edge as `u, v, w(uv)`. -/
def apspInitWords {n : ℕ} (W : ℕ) (G : WGraph (Fin n)) (es : List (Fin n × Fin n)) : List ℕ :=
  [n, W, es.length] ++ es.flatMap fun e => [e.1.val, e.2.val, G.wt s(e.1, e.2)]

/-- Decode an estimate word: `0` is `∞`, `q + 1` is `q`. -/
def decodeEst (q : ℕ) : ℕ∞ :=
  if q = 0 then ⊤ else ((q - 1 : ℕ) : ℕ∞)

/-- Replay estimate records: the three words `u, v, q` set `d[u, v]` to `decodeEst q` when `u` and
`v` are vertices; any other triple is skipped, as is a trailing incomplete record. -/
def replayEst {n : ℕ} : (Fin n → Fin n → ℕ∞) → List ℕ → (Fin n → Fin n → ℕ∞)
  | d, u :: v :: q :: rest =>
      replayEst
        (if h : u < n ∧ v < n then
          fun x y => if x = ⟨u, h.1⟩ ∧ y = ⟨v, h.2⟩ then decodeEst q else d x y
        else d) rest
  | d, _ => d

/-- The default estimate before any record: `d[u, u] = 0` and `d[u, v] = ∞` for `u ≠ v`. -/
def defaultEst {n : ℕ} : Fin n → Fin n → ℕ∞ :=
  fun u v => if u = v then 0 else ⊤

/-- The maintained estimate `d_t[u, v]`: every record written up to the completed state at time `t`,
replayed over the default. -/
noncomputable def estAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) {n : ℕ} (W : ℕ)
    (G₀ : WGraph (Fin n)) (es : List (Fin n × Fin n)) (σ : List (Upd n)) (t : ℕ) :
    Fin n → Fin n → ℕ∞ :=
  replayEst defaultEst (outputAt P ω (apspInitWords W G₀ es) (σ.map Upd.words) t)

/-- The total update time of an APSP run: initialization and every update of `σ`. -/
noncomputable def apspTime (P : Program) {w : ℕ} (ω : ℕ → BitVec w) {n : ℕ} (W : ℕ)
    (G₀ : WGraph (Fin n)) (es : List (Fin n × Fin n)) (σ : List (Upd n)) : ℕ∞ :=
  totalTime P ω (apspInitWords W G₀ es) (σ.map Upd.words)

end DecrNearAddAPSP.W2


