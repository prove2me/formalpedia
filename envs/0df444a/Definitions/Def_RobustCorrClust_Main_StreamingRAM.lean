-- Prove2me | Definitions.Def_RobustCorrClust_Main_StreamingRAM
-- name    : RobustCorrClust_Main_StreamingRAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:39:38.966374+00:00
-- url     : https://prove2.me/theorems/1ce85482-6602-4ce5-94c7-6462db6e695d
-- title:
--   The streaming machine: a randomized log-cost RAM with persistent memory, a call interface for insertions and requests, reachable memories and space in bits
-- statement:
--   The machine is the published randomized **logarithmic-cost RAM** (`SubsetSumPartialMatch.SubsetSum`): memory cells indexed by $\mathbb N$ holding integers; instructions `const`, `+`, `−`, `×`, Euclidean `/` and `%`, indirect load and store, jumps, and a fair coin; each instruction is charged the bit lengths of its operands and addresses. A program $P$ is a finite instruction list fixed in advance.
--
--   **Calls.** The memory persists between calls. A call starts at instruction $0$ with its own fresh random tape, on the persistent memory with the interface cells $0$–$3$ overwritten: **initialisation** writes $(0,n,p,q)$, where $\varepsilon=p/q$; **insertion** of the pair $\{u,v\}$ writes $(1,u,v,0)$; **request** writes $(2,0,0,0)$. The call ends when the program counter leaves the program; the memory it ends with is the next persistent memory. After a request, vertex $u$ has label (cell $4+u$), and the output clustering puts $u,v$ together iff their labels are equal.
--
--   **Operation sequences.** $\sigma$ is a list of insertions and requests; it is **valid** for $n$ if every insertion is of distinct $u,v<n$ not inserted before (in either order). $G_\sigma$ is the graph on $\{0,\dots,n-1\}$ whose positive pairs are the inserted ones.
--
--   **Reachable memories.** $m$ is reachable after $\sigma$ if, starting from the all-zero memory, the initialisation call and then the calls of $\sigma$ can each halt (on some random tape) so that the last one halts with memory $m$; equivalently, $m$ has positive probability after $\sigma$.
--
--   **Space.** A memory occupies at most $B$ bits if $\sum_{a:\,m(a)\ne0}(\text{bits of }a+\text{bits of }m(a))\le B$: addresses of nonzero cells are charged.
--
--   **Expected output cost.** If a call halts within $K$ steps on every tape, it reads at most $K$ coins, and the expected cost on $G$ of its output clustering is the average over the $2^K$ values of the first $K$ coins.
--
--   **Formalization Note.** Space is checked on every finite set of nonzero cells, which forces finitely many nonzero cells. Running time is the machine's charged log-cost of the call.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), pp. 2-3, §1 (model, adaptive adversaries); pp. 11-12, §3.1-3.2; p. 54, proof of Theorem 1

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM
import Definitions.Def_RobustCorrClust_Main_SignedGraph

namespace RobustCorrClust.Main

open SubsetSumPartialMatch.SubsetSum

/-! The streaming machine of Theorem 1 (§1, pp. 2–3; §3.1–3.2, pp. 11–12): a randomized
logarithmic-cost RAM (the published `SubsetSumPartialMatch.SubsetSum` machine: memory `ℕ → ℤ`,
`const`, `+`, `−`, `×`, Euclidean `/` and `%`, indirect `load`/`store`, `jump`, `jumpPos`, and a
fair coin `rand`; every instruction charged its operand bit lengths) with a persistent memory
across calls, a call interface for an insertion-only edge stream with clustering requests, and a
space measure in bits that charges the addresses of all nonzero cells. -/

/-- An operation of the stream after initialisation: insert the positive pair `{u, v}`, or
request a clustering. -/
inductive Op where
  | insert (u v : ℕ)
  | request
  deriving DecidableEq

/-- Write `c₀, c₁, c₂, c₃` into the interface cells `0, 1, 2, 3`; every other cell keeps its value. -/
def setRegs (m : ℕ → ℤ) (c₀ c₁ c₂ c₃ : ℤ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update m 0 c₀) 1 c₁) 2 c₂) 3 c₃

/-- The memory in which the initialisation call starts: entry code `0`, and `n, p, q` (with
`ε = p/q`) in cells `1, 2, 3`. -/
def loadInit (n p q : ℕ) (m : ℕ → ℤ) : ℕ → ℤ :=
  setRegs m 0 n p q

/-- The memory in which a call for an operation starts from the persistent memory `m`:
an insertion of `{u, v}` writes entry code `1` and `u, v` in cells `1, 2`; a request writes
entry code `2`. -/
def loadOp : Op → (ℕ → ℤ) → (ℕ → ℤ)
  | .insert u v, m => setRegs m 1 u v 0
  | .request, m => setRegs m 2 0 0 0

/-- The memory before anything has happened: every cell is `0`. -/
def zeroMem : ℕ → ℤ := fun _ => 0

/-- The configuration after `t` steps of a call of `P` started (at instruction `0`, no coins used,
no cost charged) on the memory `m`, with the call's own random tape `ω`. -/
def callRun (P : Program) (ω : ℕ → Bool) (m : ℕ → ℤ) (t : ℕ) : Config :=
  (step P ω)^[t] ⟨0, m, 0, 0⟩

/-- `m'` is a memory with which a call of `P` started on `m` halts with positive probability:
on some random tape the call halts, after finitely many steps (and hence finitely many coins),
with memory `m'`. -/
def CallEnds (P : Program) (m m' : ℕ → ℤ) : Prop :=
  ∃ ω t, Halted P (callRun P ω m t) ∧ (callRun P ω m t).mem = m'

/-- `Reach P n p q σ m`: `m` is a memory reachable with positive probability after initialising
`P` on `(n, p, q)` from the all-zero memory and then running the calls of the operations `σ` in
order, each call with fresh independent coins and starting from the memory the previous call
halted with. -/
inductive Reach (P : Program) (n p q : ℕ) : List Op → (ℕ → ℤ) → Prop
  | init {m : ℕ → ℤ} : CallEnds P (loadInit n p q zeroMem) m → Reach P n p q [] m
  | next {σ : List Op} {op : Op} {m m' : ℕ → ℤ} :
      Reach P n p q σ m → CallEnds P (loadOp op m) m' → Reach P n p q (σ ++ [op]) m'

/-- A valid operation sequence on the vertex set `{0, …, n−1}`: every insertion is of a pair of
distinct vertices `u, v < n` that has not been inserted before (in either order). Requests may
come at any time. -/
def Valid (n : ℕ) (σ : List Op) : Prop :=
  ∀ (σ₁ σ₂ : List Op) (u v : ℕ), σ = σ₁ ++ Op.insert u v :: σ₂ →
    u < n ∧ v < n ∧ u ≠ v ∧ Op.insert u v ∉ σ₁ ∧ Op.insert v u ∉ σ₁

/-- The current graph `G_σ` on `Fin n`: its positive pairs are the inserted pairs. -/
def graphOf (n : ℕ) (σ : List Op) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => Op.insert u.val v.val ∈ σ)

/-- The clustering output in a configuration: vertex `u` gets the label in cell `4 + u`, and two
vertices are in the same cluster iff their labels are equal. -/
def outClustering (n : ℕ) (c : Config) : Setoid (Fin n) :=
  Setoid.ker (fun u : Fin n => c.mem (4 + u.val))

/-- Space in bits: `SpaceLE m B` says `∑_{a : m a ≠ 0} (bits of a + bits of m a) ≤ B`, i.e. every
finite set of nonzero cells has total address-plus-content bit length at most `B` (so the set of
nonzero cells is finite and its total is at most `B`). Addresses are charged with `adrLen`, cell
contents with `wordLen` of the published machine. -/
def SpaceLE (m : ℕ → ℤ) (B : ℝ) : Prop :=
  ∀ S : Finset ℕ, (∀ a ∈ S, m a ≠ 0) → ((∑ a ∈ S, (adrLen a + wordLen (m a)) : ℕ) : ℝ) ≤ B

/-- The call of `P` started on `m` halts within `t` steps on every random tape. -/
def HaltsWithin (P : Program) (m : ℕ → ℤ) (t : ℕ) : Prop :=
  ∀ ω, Halted P (callRun P ω m t)

/-- The random tape whose first `K` bits are `b` and whose later bits are `false`. -/
def tapeOf (K : ℕ) (b : Fin K → Bool) : ℕ → Bool :=
  fun i => if h : i < K then b ⟨i, h⟩ else false

/-- The expected cost on `G` of the clustering output by a call of `P` started on `m`, computed
over the `2^K` equally likely values of the first `K` coins and read after `K` steps. When the
call halts within `K` steps on every tape, a run reads at most `K` coins (one per `rand`
step), so this is exactly the expectation over a fair random tape. -/
noncomputable def expOutCost (P : Program) {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ → ℤ)
    (K : ℕ) : ℝ :=
  (∑ b : Fin K → Bool, (cost G (outClustering n (callRun P (tapeOf K b) m K)) : ℝ)) / 2 ^ K

end RobustCorrClust.Main


