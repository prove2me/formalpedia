-- Prove2me | Definitions.Def_FourWayStream_ARHM_Supplement_NGC
-- name    : FourWayStream_ARHM_Supplement_NGC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:59:07.876382+00:00
-- url     : https://prove2.me/theorems/3a31e738-adc8-48a9-a8a8-b2bdeb94dcc5
-- title:
--   Definition 7.1, Definition E.1 — Noisy Gap Cycle, robust one-way protocols, edge-streaming algorithms and orders
-- statement:
--   **Noisy Gap Cycle.** A pair $(n,k)$ is **admissible** if $k\ge3$ and $4k\mid n$. An instance of $\mathrm{NGC}_{n,k}$ is an $n$-vertex labeled graph that is exactly one of
--   1. the disjoint union of $n/(2k)$ cycles of length $k$ and $n/(2k)$ paths of length $k-1$ ($k$ vertices each), or
--   2. the disjoint union of $n/(4k)$ cycles of length $2k$ and $n/(2k)$ paths of length $k-1$.
--
--   The answer is which case holds.
--
--   **Robust one-way protocols.** Each edge is assigned to Alice or Bob independently with probability $1/2$; Alice sends one quantum message (a density matrix on $\mathbb C^d$, $d\le 2^q$, depending on her edges and public coins; no prior entanglement) and Bob applies a two-outcome measurement depending on his edges and the coins. Error at most $\eta$ means: for every promise graph, averaged over the split and the coins, Bob names the case with probability at least $1-\eta$.
--
--   **Edge-streaming algorithms.** A quantum algorithm has memory $\mathbb C^d$, an initial state, a quantum channel for every stage and arriving edge, and a terminal two-outcome measurement; a classical one has a finite state set, stochastic transitions and a randomized decision. They see only the edges. Space is $\lceil\log_2 d\rceil$ qubits or $\lceil\log_2|\sigma|\rceil$ bits.
--
--   **Orders.** Single arrival in uniformly random order (a uniform order of the edges) or in adversarial order (every order). For the $R$-repeated stream of Definition E.1, each edge has $R$ labeled copies: in **uniformly random order** the $R|E|$ copies are permuted uniformly; in **uniformly clustered order** the $R$ copies of each edge are consecutive and the clusters appear in a uniform order. Error at most $\eta$ is required on every promise graph, averaged over the order and the algorithm's randomness.
--
--   These objects state Theorems 7.2, 7.3, 7.11 and 7.13.
--
--   **Formalization Note** The two cases are the relabelings, by a permutation of $[n]$, of a canonical edge set on $\{0,\dots,n-1\}$; the answer `true` means "$2k$-cycles". Alice's share is a uniform subset $A$ of the edge set $E$ and Bob's is $E\setminus A$.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §4.1–4.3, pp.15–17; §7.1, Definition 7.1, p.33; §7.4, p.37; Definition E.1, p.49

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble

set_option autoImplicit false

/-!
# Noisy Gap Cycle: the promise, robust one-way protocols, edge-streaming algorithms, orders

Nadezhda Voronova, *Four Ways to Stream*, STOC 2027 submission #1371 (October 2026): §4.1–4.3
(pp.15–17), Definition 7.1 (p.33), §7.4 (p.37), Definition E.1 (p.49).

* `Admissible n k`: `k ≥ 3` and `4k ∣ n`.
* `ngcCanon n k long`: a canonical labeled instance on `[n]` (0-based `Fin n`): the first `n/2`
  vertices form `n/(2k)` cycles of length `k` (`long = false`, case 1) or `n/(4k)` cycles of length
  `2k` (`long = true`, case 2), consecutive blocks `{cL, …, cL + L − 1}` closed into cycles; the last
  `n/2` vertices form `n/(2k)` paths with `k` vertices (length `k − 1`). `IsNGC n k long E` says that
  the labeled graph with edge set `E` is a relabeling of it: exactly the graphs of case 1 or case 2 of
  Definition 7.1.
* The answer is a bit: `true` means "the cycles have length `2k`" (case 2), `false` means
  "`k`-cycles" (case 1).
* `ShareProtocol V nR`: a one-way protocol on edge shares (§4.3: no prior entanglement, Alice's
  message a density matrix on `C^d`, which includes any classical information, public coins `nR`
  values; Bob a two-outcome POVM chosen from the coins and his edges). `robustSucc` averages over the
  fair independent assignment of every edge to Alice or Bob (Alice's share `A` is a uniform subset of
  `E`, Bob's is `E \ A`) and over the coins.
* `QEdgeAlg V`: a quantum streaming algorithm on edges (§4.2, read with arbitrary channels): memory
  `C^d`, a channel (complete Kraus family) for every stage and edge, a terminal two-outcome POVM; it
  sees only the edges. `CEdgeAlg V σ`: a classical one with finite state set `σ`.
* Orders: single arrival in uniformly random order (a uniform bijection `Fin |E| ≃ E`), adversarial
  order (every bijection), and the two orders of the `R`-repeated stream of Definition E.1: a uniform
  permutation of the `R|E|` labeled copies, and the uniformly clustered order (the `R` copies of each
  edge consecutive, the clusters in a uniform order). Occurrence labels are not seen by the algorithm.
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-! ### The promise -/

/-- §7.1, p.33: `(n, k)` is admissible if `k ≥ 3` and `4k ∣ n`. -/
def Admissible (n k : ℕ) : Prop := 3 ≤ k ∧ 4 * k ∣ n

/-- The ordered adjacency of the canonical instance on `{0, …, n − 1}`: in the cycle part
(`u, v < n/2`, blocks of length `L = k` or `2k`), `v` follows `u` cyclically in the same block; in the
path part (`u, v ≥ n/2`, blocks of `k` vertices), `v = u + 1` in the same block. -/
def ngcRel (n k : ℕ) (long : Bool) (u v : ℕ) : Prop :=
  (u < n / 2 ∧ v < n / 2 ∧
    u / (if long then 2 * k else k) = v / (if long then 2 * k else k) ∧
    v % (if long then 2 * k else k) = (u % (if long then 2 * k else k) + 1) %
      (if long then 2 * k else k)) ∨
  (n / 2 ≤ u ∧ n / 2 ≤ v ∧ (u - n / 2) / k = (v - n / 2) / k ∧
    (v - n / 2) % k = (u - n / 2) % k + 1)

/-- The canonical instance of Definition 7.1 on `Fin n`: case 1 (`long = false`, `n/(2k)` cycles of
length `k`) or case 2 (`long = true`, `n/(4k)` cycles of length `2k`), plus `n/(2k)` paths of length
`k − 1`. -/
def ngcCanon (n k : ℕ) (long : Bool) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter (fun e => Sym2.lift
    ⟨fun u v => ngcRel n k long u.val v.val ∨ ngcRel n k long v.val u.val,
      fun _ _ => propext or_comm⟩ e)

/-- Definition 7.1 (p.33): `E` is the edge set of an `n`-vertex labeled graph of case 1
(`long = false`) or case 2 (`long = true`) of `NGC_{n,k}`: a relabeling of the canonical instance. -/
def IsNGC (n k : ℕ) (long : Bool) (E : Finset (Sym2 (Fin n))) : Prop :=
  ∃ π : Equiv.Perm (Fin n), E = (ngcCanon n k long).image (Sym2.map π)

/-! ### One-way protocols on edge shares -/

/-- A one-way protocol on shares of an edge set over the vertex set `V` (§4.3): public coins with
law `coin`, Alice's message `msg c A` (a density matrix on `C^d`, private randomness averaged in) from
the coins and her edges, Bob's two-outcome POVM `povm c B` from the coins and his edges. -/
structure ShareProtocol (V : Type) (nR : ℕ) where
  coin : Fin nR → ℝ
  d : ℕ
  msg : Fin nR → Finset (Sym2 V) → Matrix (Fin d) (Fin d) ℂ
  povm : Fin nR → Finset (Sym2 V) → Bool → Matrix (Fin d) (Fin d) ℂ

namespace ShareProtocol

variable {V : Type} {nR : ℕ}

/-- Coins form a probability vector, messages are density matrices, Bob's measurements are POVMs. -/
def Valid (P : ShareProtocol V nR) : Prop :=
  ((∀ c, 0 ≤ P.coin c) ∧ ∑ c, P.coin c = 1) ∧ (∀ c A, IsDensityMatrix (P.msg c A)) ∧
    ∀ c B, IsPOVM (P.povm c B)

/-- The probability that Bob outputs `b` when Alice holds `A`, Bob holds `B` (averaged over coins). -/
def outProb (P : ShareProtocol V nR) (A B : Finset (Sym2 V)) (b : Bool) : ℝ :=
  ∑ c, P.coin c * effectProb (P.povm c B b) (P.msg c A)

/-- Definition 7.1, robust model: the success probability on the edge set `E` with correct answer
`ans`, averaged over the fair independent assignment of the edges (Alice's share a uniform subset
`A ⊆ E`, Bob's `E \ A`) and the coins. -/
def robustSucc [Fintype V] (P : ShareProtocol V nR) (E : Finset (Sym2 V)) (ans : Bool) : ℝ :=
  ∑ A ∈ E.powerset, ((2 : ℝ) ^ E.card)⁻¹ * P.outProb A (E \ A) ans

end ShareProtocol

/-- Robust error at most `η` for `NGC_{n,k}` (p.33): for every promise graph, averaged over the edge
split and the protocol's randomness, Bob names the case with probability at least `1 − η`. -/
def RobustNGCErrorLE {n nR : ℕ} (P : ShareProtocol (Fin n) nR) (k : ℕ) (η : ℝ) : Prop :=
  ∀ (long : Bool) (E : Finset (Sym2 (Fin n))), IsNGC n k long E → 1 - η ≤ P.robustSucc E long

/-! ### Edge streaming algorithms -/

/-- A quantum streaming algorithm on edge streams over `V` (§4.2, arbitrary channels): memory `C^d`,
initial state `ρ0`, a channel with Kraus operators `kraus s e` for every stage `s` and edge `e`
(intermediate measurements included, their outcomes kept in memory), and a terminal two-outcome
POVM `dec`. It sees only the edges. -/
structure QEdgeAlg (V : Type) where
  d : ℕ
  ρ0 : Matrix (Fin d) (Fin d) ℂ
  r : ℕ
  kraus : ℕ → Sym2 V → Fin r → Matrix (Fin d) (Fin d) ℂ
  dec : Bool → Matrix (Fin d) (Fin d) ℂ

namespace QEdgeAlg

variable {V : Type}

/-- `ρ0` is a density matrix, every channel is complete, `dec` is a POVM. -/
def Valid (A : QEdgeAlg V) : Prop :=
  IsDensityMatrix A.ρ0 ∧ (∀ s e, IsKrausFamily (A.kraus s e)) ∧ IsPOVM A.dec

/-- The channel applied to an edge does not depend on the stage (§4.2). -/
def StageIndependent (A : QEdgeAlg V) : Prop := ∀ s s' e, A.kraus s e = A.kraus s' e

/-- The memory state after the stream `str`. -/
def run (A : QEdgeAlg V) {n : ℕ} (str : Fin n → Sym2 V) : Matrix (Fin A.d) (Fin A.d) ℂ :=
  Fin.foldl n (fun ρ i => krausApply (A.kraus i.val (str i)) ρ) A.ρ0

/-- The probability that the decision after the stream `str` is `b`. -/
def accept (A : QEdgeAlg V) {n : ℕ} (str : Fin n → Sym2 V) (b : Bool) : ℝ :=
  effectProb (A.dec b) (A.run str)

/-- Space: `⌈log₂ d⌉` qubits. -/
def space (A : QEdgeAlg V) : ℕ := Nat.clog 2 A.d

end QEdgeAlg

/-- A classical randomized streaming algorithm on edge streams over `V` with state set `σ`: initial
distribution, transitions `trans s e a b` (probability of moving from `a` to `b` on edge `e` at stage
`s`) and a terminal decision `dec a b`. -/
structure CEdgeAlg (V σ : Type) where
  init : σ → ℝ
  trans : ℕ → Sym2 V → σ → σ → ℝ
  dec : σ → Bool → ℝ

namespace CEdgeAlg

variable {V σ : Type} [Fintype σ]

/-- All of `init`, `trans s e a`, `dec a` are probability vectors. -/
def Valid (A : CEdgeAlg V σ) : Prop :=
  ((∀ a, 0 ≤ A.init a) ∧ ∑ a, A.init a = 1) ∧
    (∀ s e a, (∀ b, 0 ≤ A.trans s e a b) ∧ ∑ b, A.trans s e a b = 1) ∧
    ∀ a, (∀ b, 0 ≤ A.dec a b) ∧ ∑ b, A.dec a b = 1

/-- The transitions do not depend on the stage. -/
def StageIndependent (A : CEdgeAlg V σ) : Prop := ∀ s s' e, A.trans s e = A.trans s' e

/-- The state distribution after the stream `str`. -/
def run (A : CEdgeAlg V σ) {n : ℕ} (str : Fin n → Sym2 V) : σ → ℝ :=
  Fin.foldl n (fun v i => fun b => ∑ a, v a * A.trans i.val (str i) a b) A.init

/-- The probability that the decision after `str` is `b`. -/
def accept (A : CEdgeAlg V σ) {n : ℕ} (str : Fin n → Sym2 V) (b : Bool) : ℝ :=
  ∑ a, A.run str a * A.dec a b

/-- Space: `⌈log₂ |σ|⌉` bits. -/
def space (_A : CEdgeAlg V σ) : ℕ := Nat.clog 2 (Fintype.card σ)

end CEdgeAlg

/-! ### Orders -/

variable {V : Type} [Fintype V]

/-- Single arrivals in uniformly random order: the average of `f` over the streams
`i ↦ π(i)` for a uniform bijection `π : Fin |E| ≃ E`. -/
def avgRandOrder (E : Finset (Sym2 V)) (f : (Fin E.card → Sym2 V) → ℝ) : ℝ :=
  (∑ π : Fin E.card ≃ E, f (fun i => (π i).1)) / (Fintype.card (Fin E.card ≃ E) : ℝ)

/-- Definition E.1(a): the `R`-repeated stream in uniformly random order, a uniform permutation of
the `R |E|` labeled copies `(e, c)`; the algorithm sees only `e`. -/
def avgRepRandOrder (E : Finset (Sym2 V)) (R : ℕ) (f : (Fin (E.card * R) → Sym2 V) → ℝ) : ℝ :=
  (∑ π : Fin (E.card * R) ≃ (E × Fin R), f (fun i => (π i).1.1)) /
    (Fintype.card (Fin (E.card * R) ≃ (E × Fin R)) : ℝ)

/-- Definition E.1(b): the uniformly clustered order: the clusters appear in the order of a uniform
bijection `π : Fin |E| ≃ E`, and positions `R i, …, R i + R − 1` carry the `R` copies of `π(i)`. -/
def avgClustered (E : Finset (Sym2 V)) (R : ℕ) (f : (Fin (E.card * R) → Sym2 V) → ℝ) : ℝ :=
  (∑ π : Fin E.card ≃ E, f (fun p => (π (finProdFinEquiv.symm p).1).1)) /
    (Fintype.card (Fin E.card ≃ E) : ℝ)

/-- Quantum, single arrivals, uniformly random order: error at most `η` on every promise graph. -/
def QEdgeAlg.RandErrorLE {n : ℕ} (A : QEdgeAlg (Fin n)) (k : ℕ) (η : ℝ) : Prop :=
  ∀ (long : Bool) (E : Finset (Sym2 (Fin n))), IsNGC n k long E →
    1 - η ≤ avgRandOrder E (fun str => A.accept str long)

/-- Quantum, single arrivals, adversarial order: error at most `η` on every promise graph and every
order of its edges. -/
def QEdgeAlg.AdvErrorLE {n : ℕ} (A : QEdgeAlg (Fin n)) (k : ℕ) (η : ℝ) : Prop :=
  ∀ (long : Bool) (E : Finset (Sym2 (Fin n))), IsNGC n k long E →
    ∀ π : Fin E.card ≃ E, 1 - η ≤ A.accept (fun i => (π i).1) long

/-- Quantum, `R`-repeated stream in uniformly clustered order: error at most `η`. -/
def QEdgeAlg.ClusteredErrorLE {n : ℕ} (A : QEdgeAlg (Fin n)) (k R : ℕ) (η : ℝ) : Prop :=
  ∀ (long : Bool) (E : Finset (Sym2 (Fin n))), IsNGC n k long E →
    1 - η ≤ avgClustered E R (fun str => A.accept str long)

/-- Classical, single arrivals, adversarial order: error at most `η`. -/
def CEdgeAlg.AdvErrorLE {n : ℕ} {σ : Type} [Fintype σ] (A : CEdgeAlg (Fin n) σ) (k : ℕ) (η : ℝ) :
    Prop :=
  ∀ (long : Bool) (E : Finset (Sym2 (Fin n))), IsNGC n k long E →
    ∀ π : Fin E.card ≃ E, 1 - η ≤ A.accept (fun i => (π i).1) long

end FourWayStream.ARHM.Supplement


