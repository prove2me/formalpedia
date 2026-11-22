-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_StarLanguage
-- name    : QuantumKtSoI_Supplement_StarLanguage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:32:07.251711+00:00
-- url     : https://prove2.me/theorems/bf11574f-56fe-40c8-8ca0-cb571b9e5e96
-- title:
--   Oracle procedures, downward and random self-reducibility, and the properties of $L_\star$ (Theorem 2.4)
-- statement:
--   An **oracle procedure** is an algorithm that writes queries and receives answers through a specified external interface; with a Boolean function $f$ as oracle, a query $y$ returns $f(y)$ in one oracle step. A function $f:\{0,1\}^*\to\{0,1\}$ is **downward self-reducible** if a deterministic polynomial-time oracle procedure with oracle $f$ outputs $f(x)$ on every input $x$, making only queries of length less than $|x|$. It is **random self-reducible with positive integer parameters $a,b,c$** if there are polynomial-time computable $g,h$ such that for every sufficiently large $n$: for every $x\in\{0,1\}^n$ and $i\in[n^a]$, $g(i,x,r)$ is uniform on $\{0,1\}^n$ when $r$ is uniform on $\{0,1\}^{n^c}$; and for every $x\in\{0,1\}^n$ and every $\tilde f$ agreeing with $f$ on all but a $1/n^b$ fraction of $\{0,1\}^n$,
--   $$f(x)=h\big(x,r,\tilde f(g(1,x,r)),\dots,\tilde f(g(n^a,x,r))\big)$$
--   with probability at least $1-2^{-2n}$ over $r$.
--
--   A language $L$ has the **Theorem 2.4 properties** if it is computable on inputs of length $n$ in time $O(2^{n^{d}})$ for a constant $d$, it is complete for PSPACE under deterministic polynomial-time many-one reductions, and it is downward self-reducible and random self-reducible with positive integer parameters.
--
--   Theorem 2.4 (a cited result) supplies one such language $L_\star$; Theorem 6.16 is about it.
--
--   **Formalization Note** The oracle interface is pinned: a deterministic coded machine with a designated query tape and states `query`, `yes`, `no`; a step from `query` moves to `yes` or `no` according to $f$ of the string on the query tape. The arguments of $g$ and $h$ are encoded by the pairing. PSPACE and reductions are the published definitions of the base mission.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), p.18 (oracle procedures, self-reducibility); Theorem 2.4, p.19

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine
import Definitions.Def_QuantumKtSoI_PSPACEHard
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- A deterministic **oracle procedure** (p.18 of Myrisiotis, STOC 2027 submission, held version
sha256 6616571c…): a deterministic machine (a valid coded machine without gate states) with a
designated query tape and three designated states `query`, `yes`, `no`, where `query` is coded as a
final state of the underlying machine. With an oracle `f : {0,1}* → {0,1}`, a step from the state
`query` moves to `yes` if `f(y) = 1` and to `no` otherwise, `y` the string written on the query tape,
leaving tapes and heads unchanged (one oracle step); every other step is the machine's classical
step. The procedure has halted when it is in a final state other than `query`.

**Formalization Note** The paper fixes only "an algorithm that writes queries and receives answers
through a specified external interface", counting one step per oracle call and the procedure's own
steps; this is one such interface. -/
structure OracleProc where
  B : CodedMachine
  valid : B.Valid
  gateFree : B.GateFree
  qT : Fin (B.k + 2)
  qQuery : Fin B.s
  qYes : Fin B.s
  qNo : Fin B.s
  query_final : B.toMachine.isFinal qQuery = true

namespace OracleProc

variable (A : OracleProc)

/-- The string written on a tape: the longest binary string on cells `1, 2, …` of that tape. -/
def tapeString (C : A.B.toMachine.Config) (t : Fin (A.B.k + 2)) : List Bool :=
  let len := sSup {k : ℕ | ∀ i < k, C.cont t ((i : ℤ) + 1) = Sym.b0 ∨ C.cont t ((i : ℤ) + 1) = Sym.b1}
  List.ofFn fun i : Fin len => decide (C.cont t ((i : ℤ) + 1) = Sym.b1)

/-- One step of the procedure with oracle `f`. -/
def ostep (f : List Bool → Bool) (C : A.B.toMachine.Config) : A.B.toMachine.Config :=
  if C.state = A.qQuery then
    { C with state := if f (A.tapeString C A.qT) then A.qYes else A.qNo }
  else if A.B.toMachine.isFinal C.state then C
  else C.classicalNext

/-- The configuration after `s` steps on input `x` with oracle `f`. -/
def oconf (f : List Bool → Bool) (x : List Bool) : ℕ → A.B.toMachine.Config
  | 0 => A.B.toMachine.initConfig x
  | s + 1 => A.ostep f (oconf f x s)

/-- The procedure **computes** `f(x)` on input `x` with oracle `f` within `T` steps, making only
queries of length less than `m`: after `T` steps it is in a final state other than `query` with
output `f(x)` (the one-bit string), and every query made before has length less than `m`. -/
def ComputesWithin (f : List Bool → Bool) (x : List Bool) (T m : ℕ) : Prop :=
  (A.oconf f x T).state ≠ A.qQuery ∧ A.B.toMachine.isFinal (A.oconf f x T).state = true ∧
    (A.oconf f x T).output = [f x] ∧
    ∀ s < T, (A.oconf f x s).state = A.qQuery → (A.tapeString (A.oconf f x s) A.qT).length < m

end OracleProc

/-- `f : {0,1}* → {0,1}` is **downward self-reducible** (p.18, [AGG+22, Definition 2.14]): a
deterministic polynomial-time oracle procedure `A` such that, for every input `x`, `A` with oracle
`f` outputs `f(x)` and makes only queries of length less than `|x|`; polynomial time is `c(|x|+2)^k`
steps. -/
def DownwardSelfReducible (f : List Bool → Bool) : Prop :=
  ∃ A : OracleProc, ∃ c k : ℕ, ∀ x : List Bool, A.ComputesWithin f x (c * (x.length + 2) ^ k) x.length

/-- `f` is **random self-reducible with positive integer parameters `a, b, c`** (p.18,
[AGG+22, Definition 2.15]): there are polynomial-time computable `g` and `h` such that for every
sufficiently large `n`:
1. for every `x ∈ {0,1}ⁿ` and `i ∈ [n^a]`, `g(i, x, r)` is uniform on `{0,1}ⁿ` when `r` is uniform
   on `{0,1}^{n^c}`;
2. for every `x ∈ {0,1}ⁿ` and every `f̃ : {0,1}ⁿ → {0,1}` agreeing with `f` on all but a `1/n^b`
   fraction of `{0,1}ⁿ`, `f(x) = h(x, r, f̃(g(1,x,r)), …, f̃(g(n^a,x,r)))` with probability at least
   `1 − 2^{−2n}` over `r`.

**Formalization Note** The arguments are encoded as strings by the pairing: `g(i, x, r)` is
`G(⟨b(i), ⟨x, r⟩⟩)` and `h(x, r, b₁…b_{n^a})` is the bit `H(⟨x, ⟨r, b₁⋯b_{n^a}⟩⟩)` for functions
`G, H` computable in deterministic polynomial time, `H` returning a one-bit string. -/
def RandomSelfReducible (f : List Bool → Bool) (a b c : ℕ) : Prop :=
  ∃ G H : List Bool → List Bool, PolyTimeFn G ∧ PolyTimeFn H ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (∀ x : List Bool, x.length = n → ∀ i : ℕ, 1 ≤ i → i ≤ n ^ a → ∀ z : Fin n → Bool,
      ((Finset.univ.filter fun r : Fin (n ^ c) → Bool =>
          G (pair (bin i) (pair x (List.ofFn r))) = List.ofFn z).card : ℝ) = 2 ^ (n ^ c) / 2 ^ n) ∧
    (∀ x : List Bool, x.length = n → ∀ ft : List Bool → Bool,
      ((Finset.univ.filter fun z : Fin n → Bool => ft (List.ofFn z) ≠ f (List.ofFn z)).card : ℝ) ≤
          2 ^ n / (n : ℝ) ^ b →
        (1 - 1 / 2 ^ (2 * n) : ℝ) ≤
          ((Finset.univ.filter fun r : Fin (n ^ c) → Bool =>
              H (pair x (pair (List.ofFn r)
                ((List.range (n ^ a)).map fun j => ft (G (pair (bin (j + 1)) (pair x (List.ofFn r)))))))
                = [f x]).card : ℝ) / 2 ^ (n ^ c))

/-- The properties of the language `L⋆` of **Theorem 2.4** (p.19): `L` is computable on inputs of
length `n` in deterministic time `C·2^{n^d}` for constants `C, d ≥ 1`; it is complete for PSPACE
under deterministic polynomial-time many-one reductions; and its characteristic function is
downward self-reducible and random self-reducible with positive integer parameters `a, b, c`. -/
def StarProps (L : Set (List Bool)) : Prop :=
  (∃ A : CodedMachine, A.Valid ∧ A.GateFree ∧ ∃ C d : ℕ, 1 ≤ d ∧ ∀ x : List Bool,
      A.toMachine.HaltsWithin x (C * 2 ^ (x.length ^ d)) ∧
        A.toMachine.outputProb x (C * 2 ^ (x.length ^ d)) [decide (x ∈ L)] = 1) ∧
    InPSPACE L ∧ PSPACEHard L ∧
    DownwardSelfReducible (fun x => decide (x ∈ L)) ∧
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ RandomSelfReducible (fun x => decide (x ∈ L)) a b c

end QuantumKtSoI.Supplement


