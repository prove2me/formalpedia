-- Prove2me | Definitions.Def_PermutationStreams_Parity_StreamingAlgorithm
-- name    : PermutationStreams_Parity_StreamingAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:48.373202+00:00
-- url     : https://prove2.me/theorems/06e04363-d966-4d64-b9fe-e7001af242eb
-- title:
--   Randomized multi-pass streaming algorithms on permutation streams
-- statement:
--   Fix natural numbers $n,p$ (the theorems take $p\ge1$) and a finite set $S$ of memory states. A **deterministic $p$-pass streaming machine** consists of an initial state $\sigma_0\in S$, a transition rule and an output rule $S\to\{-1,+1\}$. The input permutation $\pi$ of $[n]$ is read as the stream $\pi_1,\dots,\pi_n$, and the stream is read $p$ times, always forwards; the memory state is kept from one pass to the next. When the $i$-th value of pass $k$ arrives, the new state is a function of the current state, the arriving value $\pi_i$, and the public clock $(k,i)$ only:
--
--   $$
--   \sigma\ \longmapsto\ \operatorname{step}_{k,i}(\sigma,\pi_i).
--   $$
--
--   After the last pass the machine outputs $\operatorname{out}(\sigma)$. The machine never sees the input except through the current value; everything it remembers is in the state. It uses **$s$ bits of space** when $|S|\le 2^s$.
--
--   A **randomized $p$-pass streaming algorithm** with state set $S$ draws an input-independent random outcome $\omega$ from a finite probability space $(\Omega,w)$ (arbitrary real weights $w(\omega)\ge0$ with $\sum_\omega w(\omega)=1$) and then runs the deterministic machine $M_\omega$ on the common state set $S$. Its error on input $\pi$ is
--
--   $$
--   \operatorname{err}(\pi)=\sum_{\omega\in\Omega} w(\omega)\,\mathbf 1\{M_\omega(\pi)\ne\operatorname{sgn}(\pi)\},
--   $$
--
--   and it computes the sign with error at most $\delta$ when $\operatorname{err}(\pi)\le\delta$ for **every** permutation $\pi$ of $[n]$.
--
--   This is the computational model of Theorem 1.1. No time bound is imposed and the local computation of the transitions is unrestricted.
--
--   **Formalization Note** The finite mixture loses no randomized algorithm: for fixed $n,p$ and $S$ there are finitely many clock-aware deterministic machines, and random bits read during the run can be sampled in advance for each clock step $(k,i)$, so every randomized algorithm with memory $S$ (random bits not charged to memory, as usual) induces a probability distribution on these machines with the same output distribution on every input. Letting transitions depend on the publicly known pass and position only enlarges the class of algorithms.
--
--   Differences from the source:
--   - generalization: a streaming algorithm whose transition depends on its state and the arriving value → the transition may also depend on the public clock (pass index, position); reason: every source algorithm is a machine that ignores the clock; the clock is input independent
--   - encoding: randomized algorithm with random coins → a finite probability space of coin outcomes, each selecting a deterministic machine on the common state set S; reason: for fixed n, p and S there are finitely many clock-aware machines and online random bits can be pre-sampled per clock step, so every source algorithm induces such a mixture with the same output law on each input
--   - encoding: s bits of space → a state set S with |S| ≤ 2^s; reason: s bits store exactly 2^s states
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §1, p. 1 (streaming model, permutation promise); §1.1, p. 2 (Theorem 1.1); §4.3, p. 8 (p forward passes, state kept between passes)

import Definitions.Def_PermutationStreams_Parity_Inversions

namespace PermutationStreams.Parity

/-- A deterministic `p`-pass streaming machine for permutations of `[n]` with state set `S`
(§1 p.1, §1.1 p.2, §4.3 p.8). The values `π(0), …, π(n-1)` are read in order, `p` times,
always forwards; the state is kept between passes. `step k i σ v` is the new state when the
`i`-th value of pass `k` is `v` and the current state is `σ`: it sees only the current value,
the current state and the public clock `(k, i)`, never the rest of the input. -/
structure StreamMachine (n p : ℕ) (S : Type) where
  init : S
  step : Fin p → Fin n → S → Fin n → S
  out : S → ℤˣ

/-- One forward pass `k` over the stream `π(0), …, π(n-1)` starting in state `σ`. -/
def StreamMachine.pass {n p : ℕ} {S : Type} (M : StreamMachine n p S) (k : Fin p)
    (π : Equiv.Perm (Fin n)) (σ : S) : S :=
  (List.finRange n).foldl (fun st i => M.step k i st (π i)) σ

/-- The state after all `p` passes, starting from `init`. -/
def StreamMachine.finalState {n p : ℕ} {S : Type} (M : StreamMachine n p S)
    (π : Equiv.Perm (Fin n)) : S :=
  (List.finRange p).foldl (fun st k => M.pass k π st) M.init

/-- The answer `±1` returned after the last pass. -/
def StreamMachine.output {n p : ℕ} {S : Type} (M : StreamMachine n p S)
    (π : Equiv.Perm (Fin n)) : ℤˣ :=
  M.out (M.finalState π)

/-- A randomized `p`-pass streaming algorithm with state set `S`: input-independent random
coins `ω ∈ Ω` drawn with arbitrary real probability weights, each selecting a deterministic
machine on the common state set `S`. The memory is `s` bits when `Fintype.card S ≤ 2^s`. -/
structure RandStreamAlg (n p : ℕ) (S Ω : Type) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1
  machine : Ω → StreamMachine n p S

/-- The probability, over the coins, that the algorithm's answer on `π` is not `sgn π`. -/
noncomputable def RandStreamAlg.errorProb {n p : ℕ} {S Ω : Type} [Fintype Ω]
    (A : RandStreamAlg n p S Ω) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ ω, A.weight ω * (if (A.machine ω).output π = sgn π then 0 else 1)

/-- The algorithm computes the sign with error at most `δ` on **every** input permutation. -/
def RandStreamAlg.ComputesSignWithError {n p : ℕ} {S Ω : Type} [Fintype Ω]
    (A : RandStreamAlg n p S Ω) (δ : ℝ) : Prop :=
  ∀ π : Equiv.Perm (Fin n), A.errorProb π ≤ δ

end PermutationStreams.Parity


