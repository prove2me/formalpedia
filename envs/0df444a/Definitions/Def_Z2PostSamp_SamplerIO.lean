-- Prove2me | Definitions.Def_Z2PostSamp_SamplerIO
-- name    : Z2PostSamp_SamplerIO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:08.87943+00:00
-- url     : https://prove2.me/theorems/780a41f2-5983-4535-87e8-2ab739bf1baa
-- title:
--   Input layout, output decoding and the output law $\widehat\mu(\cdot\mid Y)$ of a sampler program
-- statement:
--   A sampler program receives the input list $[n]$ and the real oracle holding $Y$ row by row followed by $\lambda$: cell $i\,n+j$ holds $Y_{ij}$ for $i,j<n$, cell $n^2$ holds $\lambda$, and every other cell holds $0$. Its output list is decoded as a configuration: coordinate $i$ is $+1$ exactly when the $i$-th output entry equals $1$, and $-1$ otherwise (also when the entry is missing or the machine has not halted).
--
--   The **output law** of a program $P$ at step budget $T$ is
--
--   $$\widehat\mu(s\mid Y)=\mathbb P_\omega\big(\text{the decoded output of }P\text{ on }(Y,\lambda,\omega)\text{ after }T\text{ steps is }s\big),\qquad s\in\{\pm1\}^n,$$
--
--   the probability being over the fair-coin tape $\omega$.
--
--   This is the conditional output law $\widehat\mu(\cdot\mid Y)$ of Theorem 1.1, once $T$ is at least the halting cost (every step before halting costs at least one, so the machine has halted by step $T$).
--
--   **Formalization Note** A malformed output is just another configuration, so the decoding gives a program no advantage.
--
--   **Subroutine layouts (Lemmas 2.2 and 2.3).** A logit program has oracle $(J,\lambda)$ in the same layout, and input $[n,k,I_1,x_{I_1},\dots,I_k,x_{I_k}]$ with signs written as $1$ ($+1$) or $0$ ($-1$). It runs on the all-false coin tape, so it is deterministic, and an output list $[p,c_0,c_1,\dots]$ denotes the dyadic numbers $\mathrm{unzig}(c_i)/2^p$, where $\mathrm{unzig}$ inverts the zigzag code. A proposal-sampling program has input $[K,n,k_0,I_1,\dots,I_n]$; a log-density program also receives the signs of the supplied configuration, in coordinate order.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Theorem 1.1, p.2; §2 preamble, p.6

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_Z2PostSamp_Machine

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory OAI.CriticalSK

namespace Z2PostSamp

noncomputable section

/-!
# Input and output layout of a sampler program, and its output law

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Theorem 1.1, p.2: the algorithm "takes `Y` and the known parameter `λ` as input
and outputs a sample `θ̂ ∼ μ̂`"; §2 preamble, p.6: the real observation and known parameter are
accessed through deterministic dyadic approximations.

**Formalization Note.** The machine input is the list `[n]`. The real oracle holds `Y` row by row and
then `λ`: cell `i·n + j` is `Y_ij` (`i, j < n`), cell `n·n` is `λ`, all other cells are `0`. The
output is decoded as a configuration: coordinate `i` is `+1` iff the `i`-th output entry is `1`; a
missing, other, or absent output decodes to `−1` (a malformed output is just another configuration,
so the encoding gives a program no advantage). The output law `μ̂(· | Y)` is the coin-tape probability
of each decoded configuration, read at step budget `T`; at a budget no smaller than the halting cost
this is the law of the halted output, because every step before halting costs at least one.

The subroutines of Lemmas 2.2 and 2.3 use the same oracle (with `J` in place of `Y`) and these
layouts. A logit program (Lemma 2.2, p.8: `ℓ̂^{(k)}(x_{S_k})` is computed "from `J`, `λ` and the exposed
pairs `(I_a, x_{I_a})_{1≤a≤k}`") receives `[n, k, I_1, x_{I_1}, …, I_k, x_{I_k}]`, with sites as
0-based labels and signs as `1` (`+1`) or `0` (`−1`), so it cannot read the unexposed part of the order
or of the configuration. It is deterministic (§3.3, App. B, and the replay of p.37): it is run on the
all-`false` coin tape `zeroTape`, which makes every coin instruction a constant. An output list
`[p, c_0, c_1, …]` denotes the dyadic numbers `unzig(c_i) / 2^p`, `unzig` being the inverse of the
zigzag code. The proposal programs (Lemma 2.3, p.9; Algorithm 3, p.12) receive
`[K, n, k₀, I_1, …, I_n]`, and the evaluation program also the signs of the supplied configuration
in coordinate order; `K` prescribes the accuracy `n^{−K}` (p.6: "a prescribed inverse-polynomial
absolute accuracy").
-/

/-- The real oracle of the input `(Y, λ)`. -/
def oracleOf (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) : ℕ → ℝ := fun m =>
  if h : m < n * n then
    Y ⟨m / n, Nat.div_lt_of_lt_mul h⟩ ⟨m % n, Nat.mod_lt _ (Nat.pos_of_mul_pos_left
      (lt_of_le_of_lt (Nat.zero_le m) h))⟩
  else if m = n * n then lam else 0

/-- Decoding an output list as a configuration: coordinate `i` is `+1` iff entry `i` equals `1`. -/
def decodeSpin (n : ℕ) (o : Option (List ℕ)) : Spin n :=
  fun i => decide ((o.getD []).getD i.val 0 = 1)

/-- The output law `μ̂(· | Y)(s)` of program `P` at step budget `T`: the probability, over the fair
coin tape, that the decoded output is `s`. -/
def outLaw (P : Program) (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (T : ℕ) :
    Spin n → ℝ := fun s =>
  (coinLaw {ω | decodeSpin n (outputAt P (oracleOf n Y lam) [n] ω T) = s}).toReal

/-- The all-`false` coin tape, on which a program runs deterministically. -/
def zeroTape : ℕ → Bool := fun _ => false

/-- The exposed pairs `I_1, x_{I_1}, …, I_k, x_{I_k}`, with signs written as `1` (`+1`), `0` (`−1`). -/
def exposedPairs {n : ℕ} (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ) : List ℕ :=
  ((List.finRange n).filter fun a => decide (a.val < k)).flatMap fun a =>
    [(I a).val, if x (I a) then 1 else 0]

/-- The input `[n, k, I_1, x_{I_1}, …, I_k, x_{I_k}]` of a logit program (Lemma 2.2, p.8). -/
def prefixInput {n : ℕ} (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ) : List ℕ :=
  [n, k] ++ exposedPairs I x k

/-- The inverse of the zigzag code `zig`. -/
def unzig (m : ℕ) : ℤ :=
  if m % 2 = 0 then ((m / 2 : ℕ) : ℤ) else -(((m + 1) / 2 : ℕ) : ℤ)

/-- Entry `i` of a dyadic output `[p, c_0, c_1, …]`: the number `unzig(c_i) / 2^p`. -/
def decodeDyadic (o : Option (List ℕ)) (i : ℕ) : ℝ :=
  ((unzig ((o.getD []).getD (i + 1) 0) : ℤ) : ℝ) / (2 : ℝ) ^ ((o.getD []).getD 0 0)

/-- The vector `ℓ̂^{(k)}(x_{S_k})` computed by the logit program `P` on `(J, λ)` and the exposed pairs,
read at step budget `T`. -/
def algoLogit (P : Program) (n : ℕ) (lam : ℝ) (T : ℕ) (J : Matrix (Fin n) (Fin n) ℝ)
    (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ) : Fin n → ℝ := fun i =>
  decodeDyadic (outputAt P (oracleOf n J lam) (prefixInput I x k) zeroTape T) i.val

/-- The input `[K, n, k₀, I_1, …, I_n]` of a proposal-sampling program. -/
def sampleInput {n : ℕ} (K k₀ : ℕ) (I : Equiv.Perm (Fin n)) : List ℕ :=
  [K, n, k₀] ++ (List.finRange n).map fun a => (I a).val

/-- The input of a log-density program: `sampleInput` followed by the signs of `x`, in coordinate
order, written as `1` (`+1`), `0` (`−1`). -/
def evalInput {n : ℕ} (K k₀ : ℕ) (I : Equiv.Perm (Fin n)) (x : Spin n) : List ℕ :=
  sampleInput K k₀ I ++ (List.finRange n).map fun i => if x i then 1 else 0

/-- The coin-tape law of the decoded output of `P` on a general input, read at step budget `T`. -/
def tapeLaw (P : Program) (x : ℕ → ℝ) (input : List ℕ) (n T : ℕ) : Spin n → ℝ := fun s =>
  (coinLaw {ω | decodeSpin n (outputAt P x input ω T) = s}).toReal

end

end Z2PostSamp


