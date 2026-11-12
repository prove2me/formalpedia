-- Prove2me | Definitions.Def_FourWayStream_ARHM_Stream
-- name    : FourWayStream_ARHM_Stream
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:39:50.240211+00:00
-- url     : https://prove2.me/theorems/ee2c1074-f424-4daf-b56c-55c23d2768cf
-- title:
--   Definition 5.1, Definition 5.2, §4.2 — ARHM stream, random and data-first orders, quantum and classical streaming algorithms, success and space
-- statement:
--   **Atomized Refreshable Hidden Matching.** Let $N$ be even and let $F=\{F_1,\dots,F_{N-1}\}$ be a **one-factorization** of the complete graph $K_N$: every factor $F_k$ is a **perfect matching** of $[N]$ (a set of edges, none a loop, covering every vertex exactly once), and every unordered pair $\{u,v\}$, $u\ne v$, lies in exactly one factor. For $x\in\{0,1\}^N$, a request list $(k_1,\dots,k_m)\in[N-1]^m$ (repetitions allowed) and a number $L$ of copies, the stream $\mathrm{ARHM}_{N,m}$ consists of the $NL$ labeled **updates** $(j,x_j,\ell)$, $j\in[N]$, $\ell\in[L]$, and the $m$ labeled **requests** $(t,k_t)$, $t\in[m]$. The labels are part of the items. On a request $(t,k_t)$ the algorithm writes an answer: an edge $e=\{u,v\}$ and a bit $b$; it is **correct** if $e\in F_{k_t}$ and $b=x_u\oplus x_v$. A missing answer is wrong; outputs written after updates are ignored. Success means that all $m$ answers are correct.
--
--   **Orders.** The stream has $NL+m$ items. In **random order** they arrive in a uniformly random permutation: a uniformly random bijection $\sigma$ from the positions $0,\dots,NL+m-1$ to the labeled occurrences. In **data-first order** the $NL$ updates come first, in an arbitrary order $\tau$, followed by the $m$ requests in list order.
--
--   **Quantum streaming algorithms.** The memory between two items is a state on $\mathbb C^d$ (classical bits are a diagonal part of it); it starts in an input-independent density matrix $\rho_0$. Item $it$ at stage $s$ is processed by a quantum instrument $\{K_{s,it,o,j}\}$, complete ($\sum_{o,j}K^\dagger K=I$), whose outcome $o$ is the output written after the item. The probability that all answers to the requests of a stream are correct is
--   $$\operatorname{Re}\operatorname{Tr}\Big(\Phi^{\mathrm{good}}_{n-1}\circ\cdots\circ\Phi^{\mathrm{good}}_{0}(\rho_0)\Big),\qquad \Phi^{\mathrm{good}}_s(\rho)=\sum_{o\ \text{good}}\sum_j K_{s,it_s,o,j}\,\rho\,K_{s,it_s,o,j}^\dagger .$$
--   The algorithm is **stage independent** if its instruments depend only on the item (the stage then enters only through stored memory, as §4.2 requires). A **classical** algorithm has $S$ memory states, an initial distribution and stochastic transitions $(a\to b,\ \text{output }o)$ for every stage and item.
--
--   **Error and space.** Error at most $\eta$ in random order: for every $x$ and every request list, all answers are correct with probability at least $1-\eta$ over the permutation, the randomness and the measurements. Error at most $\eta$ in data-first order: the same for every $x$, every list and every order of the updates. The space charged in lower bounds is $\lceil\log_2 d\rceil$ qubits (resp. $\lceil\log_2 S\rceil$ bits); the space charged in the upper bound is $\lceil\log_2 d\rceil+\lceil\log_2(|\mathrm{Output}|\cdot r)\rceil$, which adds an ancilla register holding the outcome of an instrument with $r$ auxiliary Kraus indices, so that each step is one isometry followed by a measurement of the ancilla.
--
--   These definitions underlie every statement of the mission.
--
--   **Formalization Note** Indices are 0-based (`Fin N`, `Fin L`, `Fin m`, `Fin (N - 1)`), an edge is an element of `Sym2 (Fin N)`, an answer is an `Option (Sym2 (Fin N) × Bool)`. Instruments and density matrices use the published `QAlgorithms.IsKrausFamily` and `QAlgorithms.IsDensityMatrix`. Per the mission's reading of §4.2, steps are arbitrary instruments rather than circuits over a finite gate set.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §4.1–4.2, pp.15–16; Definition 5.1, p.18; "Orders" and Definition 5.2, p.19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble

set_option autoImplicit false

/-!
# Atomized Refreshable Hidden Matching: the stream, its two orders, streaming algorithms, space

Nadezhda Voronova, *Four Ways to Stream: Exponential Separations from Random Order and Quantum
Memory*, STOC 2027 submission #1371 (October 2026): §4.1–4.2 (pp.15–16), Definition 5.1 (p.18),
"Orders" and Definition 5.2 (p.19).

Index base: the paper's `[N]`, `[L]`, `[m]`, `[N − 1]` are `Fin N`, `Fin L`, `Fin m`, `Fin (N - 1)`
(0-based). An edge `{u, v}` is `s(u, v) : Sym2 (Fin N)`; a bit is a `Bool`, `⊕` is `xor`.

Model (the reading of §4.2 recorded in the mission): the memory between two items is a state of
`C^d`; classical bits are a diagonal part of it. Every item is processed by a quantum instrument (a
finite Kraus family indexed by an output and an auxiliary index, complete: `Σ K†K = I`), whose output
on a request item is the answer written to the write-only output. A classical algorithm has a finite
state set and stochastic transitions. The instruments of `QStreamAlg` may depend on the stage (the
position in the stream) as well as on the item; `StageIndependent` is the paper's requirement that the
stage enter only through stored memory.
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM

open QAlgorithms
open scoped Matrix

/-! ### One-factorizations of `K_N` -/

/-- A perfect matching on `[N]`: a set of edges, none a loop, such that every vertex lies in exactly
one of them. -/
def IsPerfectMatching {N : ℕ} (M : Finset (Sym2 (Fin N))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag) ∧ ∀ v : Fin N, ∃! e, e ∈ M ∧ v ∈ e

/-- Definition 5.1 (p.18): `F = {F_1, …, F_{N−1}}` is a one-factorization of the complete graph
`K_N`: every factor `F_k` is a perfect matching on `[N]`, and every unordered pair of distinct
elements of `[N]` belongs to exactly one factor. -/
def IsOneFactorization {N : ℕ} (F : Fin (N - 1) → Finset (Sym2 (Fin N))) : Prop :=
  (∀ k, IsPerfectMatching (F k)) ∧ ∀ u v : Fin N, u ≠ v → ∃! k, s(u, v) ∈ F k

/-! ### Items, answers, correctness -/

/-- Definition 5.1 (p.18): the items of `ARHM_{N,m}` with `L` copies: a labeled update
`(j, x_j, ℓ)` and a labeled request `(t, k_t)` naming the factor `F_{k_t}` by its index. The labels
`ℓ` and `t` are part of the item and visible to the algorithm (§4.1, p.15). -/
inductive Item (N m L : ℕ) where
  | update (j : Fin N) (b : Bool) (ℓ : Fin L)
  | request (t : Fin m) (k : Fin (N - 1))
  deriving DecidableEq

/-- What an algorithm writes to the output after an item: nothing (`none`) or an edge and a bit. -/
abbrev Output (N : ℕ) := Option (Sym2 (Fin N) × Bool)

/-- The parity `x_u ⊕ x_v` of the edge `{u, v}` (well defined since `⊕` is symmetric). -/
def edgeParity {N : ℕ} (x : Fin N → Bool) (e : Sym2 (Fin N)) : Bool :=
  Sym2.lift ⟨fun u v => xor (x u) (x v), fun u v => Bool.xor_comm (x u) (x v)⟩ e

/-- Definition 5.1 (p.18): the answer `o` to a request naming the matching `M` is correct for `x`
if it is an edge `e = {u, v} ∈ M` with a bit `b = x_u ⊕ x_v`. A missing answer is wrong. -/
def AnswerCorrect {N : ℕ} (M : Finset (Sym2 (Fin N))) (x : Fin N → Bool) (o : Output N) : Prop :=
  ∃ e b, o = some (e, b) ∧ e ∈ M ∧ edgeParity x e = b

/-- Success requires every answer to a request item to be correct; outputs on update items are
ignored. -/
def GoodOutput {N m L : ℕ} (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (x : Fin N → Bool) :
    Item N m L → Output N → Prop
  | .update _ _ _, _ => True
  | .request _ k, o => AnswerCorrect (F k) x o

/-! ### The stream and its orders -/

/-- The labeled occurrences of `ARHM_{N,m}`: the `N L` updates, labeled by `(j, ℓ)`, and the `m`
requests, labeled by `t`. -/
abbrev Pos (N m L : ℕ) := (Fin N × Fin L) ⊕ Fin m

/-- Definition 5.1 (p.18): the item carried by an occurrence, for the input `x ∈ {0,1}^N` and the
request list `(k_1, …, k_m)` of factor indices (repetitions allowed). -/
def itemAt {N m L : ℕ} (x : Fin N → Bool) (ks : Fin m → Fin (N - 1)) : Pos N m L → Item N m L
  | .inl p => .update p.1 (x p.1) p.2
  | .inr t => .request t (ks t)

/-- The length `N L + m` of the stream: the number of labeled occurrences. -/
def streamLength (N m L : ℕ) : ℕ := Fintype.card (Pos N m L)

/-- "Orders", p.19: a random-order arrival is a bijection from the stream positions
`0, …, N L + m − 1` to the labeled occurrences; the random order is the uniform distribution on
these bijections (§4.1, p.15). -/
abbrev Arrival (N m L : ℕ) := Fin (N * L + m) ≃ Pos N m L

/-- The stream in the arrival order `σ`. -/
def randomStream {N m L : ℕ} (x : Fin N → Bool) (ks : Fin m → Fin (N - 1)) (σ : Arrival N m L) :
    Fin (N * L + m) → Item N m L :=
  fun i => itemAt x ks (σ i)

/-- Definition 5.2 (p.19): the data-first stream: the `N L` updates in the order `τ`, followed by
the `m` requests in list order, revealed one at a time. -/
def dataFirstStream {N m L : ℕ} (x : Fin N → Bool) (ks : Fin m → Fin (N - 1))
    (τ : Fin (N * L) ≃ Fin N × Fin L) : Fin (N * L + m) → Item N m L :=
  Fin.append (fun i => Item.update (τ i).1 (x (τ i).1) (τ i).2) (fun t => Item.request t (ks t))

/-! ### Quantum streaming algorithms -/

/-- A quantum streaming algorithm for `ARHM_{N,m}` with `L` copies (§4.2, p.16, read with
arbitrary channels): memory `C^d` (classical bits included), an input-independent initial state `ρ0`,
and for every stage `s` (position in the stream) and item an instrument with Kraus operators
`kraus s it o j`, indexed by the output `o` written after the item and an auxiliary index
`j : Fin r`. -/
structure QStreamAlg (N m L : ℕ) where
  d : ℕ
  ρ0 : Matrix (Fin d) (Fin d) ℂ
  r : ℕ
  kraus : ℕ → Item N m L → Output N → Fin r → Matrix (Fin d) (Fin d) ℂ

namespace QStreamAlg

variable {N m L : ℕ}

/-- `ρ0` is a density matrix and every instrument is complete (`Σ_{o,j} K†K = I`). -/
def Valid (A : QStreamAlg N m L) : Prop :=
  IsDensityMatrix A.ρ0 ∧
    ∀ s it, IsKrausFamily (fun p : Output N × Fin A.r => A.kraus s it p.1 p.2)

/-- §4.2, p.16: "a step may depend on the stage only through a counter, clock or other control
value that the algorithm stores": the instrument applied to an item does not depend on the stage. -/
def StageIndependent (A : QStreamAlg N m L) : Prop :=
  ∀ s s' it, A.kraus s it = A.kraus s' it

/-- Process item `it` at stage `s`, keeping only the outputs in `keep` (unnormalized). -/
def op (A : QStreamAlg N m L) (s : ℕ) (it : Item N m L) (keep : Output N → Prop)
    (ρ : Matrix (Fin A.d) (Fin A.d) ℂ) : Matrix (Fin A.d) (Fin A.d) ℂ :=
  ∑ o, if keep o then ∑ j, A.kraus s it o j * ρ * (A.kraus s it o j)ᴴ else 0

/-- Process the items `its 0, …, its (n−1)` at stages `s0, …, s0 + n − 1`, keeping at step `i`
only the outputs in `keep i`. -/
def runFrom (A : QStreamAlg N m L) (s0 : ℕ) {n : ℕ} (its : Fin n → Item N m L)
    (keep : Fin n → Output N → Prop) (ρ : Matrix (Fin A.d) (Fin A.d) ℂ) :
    Matrix (Fin A.d) (Fin A.d) ℂ :=
  Fin.foldl n (fun σ i => A.op (s0 + i.val) (its i) (keep i) σ) ρ

/-- The probability, over the measurement outcomes, that every answer to a request of the stream
`str` is correct (outputs on updates are unrestricted). -/
def succProb (A : QStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N)))
    (x : Fin N → Bool) {n : ℕ} (str : Fin n → Item N m L) : ℝ :=
  (A.runFrom 0 str (fun i => GoodOutput F x (str i)) A.ρ0).trace.re

/-- "Orders", p.19: the success probability in random order for `x` and the request list `ks`,
averaged over the uniformly random arrival order and the measurements. -/
def randSucc (A : QStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N)))
    (x : Fin N → Bool) (ks : Fin m → Fin (N - 1)) : ℝ :=
  (∑ σ : Arrival N m L, A.succProb F x (randomStream x ks σ)) /
    (Fintype.card (Arrival N m L) : ℝ)

/-- p.19: error at most `η` in random order: for every `x` and every request list, all answers are
correct with probability at least `1 − η`. -/
def RandErrorLE (A : QStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (η : ℝ) : Prop :=
  ∀ (x : Fin N → Bool) (ks : Fin m → Fin (N - 1)), 1 - η ≤ A.randSucc F x ks

/-- Definition 5.2 (p.19): error at most `η` in data-first order: for every input, request list and
order of the updates, all answers are correct with probability at least `1 − η`. -/
def DataFirstErrorLE (A : QStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (η : ℝ) :
    Prop :=
  ∀ (x : Fin N → Bool) (ks : Fin m → Fin (N - 1)) (τ : Fin (N * L) ≃ Fin N × Fin L),
    1 - η ≤ A.succProb F x (dataFirstStream x ks τ)

/-- Space charged in the lower bounds: `⌈log₂ d⌉`, the number of qubits of the memory between two
items (classical bits included). -/
def space (A : QStreamAlg N m L) : ℕ := Nat.clog 2 A.d

/-- Space charged in the upper bound (§4.2: "including all workspace"): the memory, `⌈log₂ d⌉`
qubits, plus an ancilla register holding the instrument's outcome `(o, j)`, `⌈log₂ (|Output| · r)⌉`
qubits, with which each instrument is applied as one isometry followed by a measurement of the
ancilla (Stinespring dilation). -/
def upperSpace (A : QStreamAlg N m L) : ℕ :=
  Nat.clog 2 A.d + Nat.clog 2 (Fintype.card (Output N) * A.r)

end QStreamAlg

/-! ### Classical streaming algorithms -/

/-- A classical (randomized) streaming algorithm: `S` memory states, an initial distribution, and
for every stage and item a stochastic transition `trans s it a (b, o)` = probability of moving from
state `a` to state `b` while writing the output `o`. -/
structure CStreamAlg (N m L : ℕ) where
  S : ℕ
  init : Fin S → ℝ
  trans : ℕ → Item N m L → Fin S → Fin S × Output N → ℝ

namespace CStreamAlg

variable {N m L : ℕ}

/-- `init` and every row of every transition are probability vectors. -/
def Valid (A : CStreamAlg N m L) : Prop :=
  ((∀ a, 0 ≤ A.init a) ∧ ∑ a, A.init a = 1) ∧
    ∀ s it a, (∀ p, 0 ≤ A.trans s it a p) ∧ ∑ p, A.trans s it a p = 1

/-- The transitions do not depend on the stage (stage only through stored memory, §4.2). -/
def StageIndependent (A : CStreamAlg N m L) : Prop :=
  ∀ s s' it, A.trans s it = A.trans s' it

/-- Process item `it` at stage `s` on the (unnormalized) state distribution `v`, keeping only the
outputs in `keep`. -/
def op (A : CStreamAlg N m L) (s : ℕ) (it : Item N m L) (keep : Output N → Prop)
    (v : Fin A.S → ℝ) : Fin A.S → ℝ :=
  fun b => ∑ a, v a * ∑ o, if keep o then A.trans s it a (b, o) else 0

/-- Process `its 0, …, its (n−1)` at stages `s0, …`, keeping at step `i` the outputs in `keep i`. -/
def runFrom (A : CStreamAlg N m L) (s0 : ℕ) {n : ℕ} (its : Fin n → Item N m L)
    (keep : Fin n → Output N → Prop) (v : Fin A.S → ℝ) : Fin A.S → ℝ :=
  Fin.foldl n (fun w i => A.op (s0 + i.val) (its i) (keep i) w) v

/-- The probability that every answer to a request of the stream `str` is correct. -/
def succProb (A : CStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N)))
    (x : Fin N → Bool) {n : ℕ} (str : Fin n → Item N m L) : ℝ :=
  ∑ b, A.runFrom 0 str (fun i => GoodOutput F x (str i)) A.init b

/-- Success probability in random order, averaged over the uniform arrival order and the
algorithm's randomness. -/
def randSucc (A : CStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N)))
    (x : Fin N → Bool) (ks : Fin m → Fin (N - 1)) : ℝ :=
  (∑ σ : Arrival N m L, A.succProb F x (randomStream x ks σ)) /
    (Fintype.card (Arrival N m L) : ℝ)

/-- Error at most `η` in random order (p.19). -/
def RandErrorLE (A : CStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (η : ℝ) : Prop :=
  ∀ (x : Fin N → Bool) (ks : Fin m → Fin (N - 1)), 1 - η ≤ A.randSucc F x ks

/-- Space: `⌈log₂ S⌉` bits. -/
def space (A : CStreamAlg N m L) : ℕ := Nat.clog 2 A.S

end CStreamAlg

end FourWayStream.ARHM


