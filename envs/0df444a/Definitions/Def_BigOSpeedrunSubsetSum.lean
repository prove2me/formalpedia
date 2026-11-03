-- Prove2me | Definitions.Def_BigOSpeedrunSubsetSum
-- name    : BigOSpeedrunSubsetSum
-- status  : Definition
-- author  : @darkhipo
-- created : 2026-11-02T06:17:48.516991+00:00
-- url     : https://prove2.me/theorems/24e98b31-fcfd-42c3-87bf-4938e7e8db71
-- title:
--   Subset Sum on the bigospeedrun randomized word RAM (with $O(2^{\alpha n})$ time)
-- statement:
--   The decision model and running-time definition of the Big O Speedrun subset-sum race (https://bigospeedrun.com/subset-sum), transcribed byte-exactly from the race's trusted challenge file `challenges/subset-sum/Statement.lean` (sha256 80bc6d28...7517, namespaces preserved).
--
--   **Model.** One finite program over 17 instructions (`one`, `add`, `sub`, `mul`, `div`, `rem`, `and`, `or`, `xor`, `shl`, `shr`, `load`, `store`, `rand`, `blt`, `accept`, `reject`), run on `w = ceil(4(n + b + log2(n+2)))`-bit words, where `n` is the number of inputs and `b` their maximum bit length. Every instruction costs one step, indirect addressing included; arithmetic beyond one word costs proportionally more; a fresh uniform random word costs one step and can be read once. Inputs are addressed relative to a relocation register; the program gets no advice.
--
--   **Decision task.** Given $a_1,\dots,a_n$ and target $t$, decide whether some selection (repeats allowed, empty selection allowed) sums to $t$.
--
--   **Bound.** $T(n) = O(2^{\alpha n})$ is `BigO T alpha`, defined by
--   $$\exists K,\ \forall n \ge 2,\quad T(n)^{\alpha.den} \le K \cdot 2^{\alpha.num \cdot n}.$$
--   For $\alpha = 1/2$ this is exactly $T(n)^2 \le K\,2^n$: one constant, every $n \ge 2$, **no polynomial slack and no threshold**.
--
--   **Solved.** `SolvedInTime alpha` asks for one program correct on every input with $n \ge 2$ (verdict correct on at least $2/3$ of random tapes) and, for every fixed $c$, a bound $T$ with `BigO T alpha` that no run exceeds on any input with $b \le n^c$. The program precedes $c$: it may not depend on it.
--
--   The definitions import nothing and prove nothing.
-- source:
--   https://bigospeedrun.com/subset-sum (race page and computation rules); trusted challenge file challenges/subset-sum/Statement.lean, sha256 80bc6d282676fc056a220968a727ab983b8c5a280cb0d9f24561bb3c90867517, namespace BigOSpeedrun.SubsetSum, copyright (c) 2026 fringewidth, Apache 2.0; model of Section 1.1 of OpenAI, "Subset Sum in Time O(2^0.49n)", 4 October 2026. Local header lines `module` and `@[expose] public section` removed for the platform's Lean v4.33.1 toolchain; the declarations are otherwise byte-identical.

/-
Copyright (c) 2026 fringewidth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-! Subset Sum on the randomized word RAM of Section 1.1 of the paper «Subset Sum in Time O(2^0.49n)» (OpenAI,
4 October 2026), the model of https://bigospeedrun.com/subset-sum. The bound is `α` in `O(2^(α n))`; smaller is
better. Imports nothing, proves nothing. -/


namespace BigOSpeedrun.SubsetSum

/-- `i j k` name cells, `l` a position in the program, `[i]` is the word in cell `i`. The only constant is 1.
Words are unsigned; arithmetic is modulo `2^w`; `[j] / 0 = 0` and `[j] % 0 = [j]`; a shift by `w` or more bits
gives 0. «Arithmetic exceeding these limits is implemented by multiple word operations and charged accordingly»:
the high word of a sum or product takes a constant number of these instructions. -/
inductive Instr where
  | one (i : Nat)              -- [i] := 1
  | add (i j k : Nat)          -- [i] := [j] + [k]
  | sub (i j k : Nat)          -- [i] := [j] - [k]
  | mul (i j k : Nat)          -- [i] := [j] * [k]
  | div (i j k : Nat)          -- [i] := [j] / [k]
  | rem (i j k : Nat)          -- [i] := [j] % [k]
  | and (i j k : Nat)          -- [i] := [j] &&& [k]
  | or (i j k : Nat)           -- [i] := [j] ||| [k]
  | xor (i j k : Nat)          -- [i] := [j] ^^^ [k]
  | shl (i j k : Nat)          -- [i] := [j] <<< [k]
  | shr (i j k : Nat)          -- [i] := [j] >>> [k]
  | load (i j : Nat)           -- [i] := [[j]]
  | store (i j : Nat)          -- [[i]] := [j]
  | rand (i : Nat)             -- [i] := the next random word
  | blt (i j : Nat) (l : Nat)  -- if [i] < [j], go to position l
  | accept
  | reject

/-- The verdict, if `P`, run from position `pc` on memory `m`, the random words `ρ r, ρ (r + 1), …` not yet read,
halts within `t` steps, the halting step counted; past its end `P` rejects. Every instruction is one step: «word
reads and writes, indirect addressing, comparisons, addition, subtraction, multiplication, integer quotient and
remainder …, bitwise Boolean operations, and shifts», and «a fresh independent uniform w-bit random word costs one
operation». Randomness is one-way: `rand` reads the next word of `ρ` once. -/
def exec {w : Nat} (P : List Instr) (ρ : Nat → BitVec w) :
    (t pc r : Nat) → (m : Nat → BitVec w) → Option Bool
  | 0, _, _, _ => none
  | t + 1, pc, r, m =>
    let write (i : Nat) (v : BitVec w) := exec P ρ t (pc + 1) r fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => write i 1
    | .add i j k => write i (m j + m k)
    | .sub i j k => write i (m j - m k)
    | .mul i j k => write i (m j * m k)
    | .div i j k => write i (m j / m k)
    | .rem i j k => write i (m j % m k)
    | .and i j k => write i (m j &&& m k)
    | .or i j k => write i (m j ||| m k)
    | .xor i j k => write i (m j ^^^ m k)
    | .shl i j k => write i (m j <<< m k)
    | .shr i j k => write i (m j >>> m k)
    | .load i j => write i (m (m j).toNat)
    | .store i j => write (m i).toNat (m j)
    | .rand i => exec P ρ t (pc + 1) (r + 1) fun x => if x = i then ρ r else m x
    | .blt i j l => exec P ρ t (if m i < m j then l else pc + 1) r m
    | .accept => some true
    | .reject => some false

/-- «positive integers a₁, …, aₙ and a nonnegative integer t. … Equal input integers are allowed». -/
structure Instance (n : Nat) where
  a : Fin n → Nat
  t : Nat
  pos : ∀ i, 0 < a i

/-- «whether there is a set I ⊆ [n] with Σ_{i ∈ I} aᵢ = t»; «the empty subset is allowed». -/
def Instance.yes {n : Nat} (x : Instance n) : Prop :=
  ∃ S : Fin n → Bool, (List.ofFn fun i => if S i then x.a i else 0).sum = x.t

/-- `max{t, a₁, …, aₙ}`. -/
def Instance.maxValue {n : Nat} (x : Instance n) : Nat :=
  (List.ofFn x.a).foldl max x.t

/-- «b = max{1, ⌈log₂(1 + max{t, a₁, …, aₙ})⌉}»: for `m ≥ 1`, `⌈log₂(1 + m)⌉ = ⌊log₂ m⌋ + 1`, and `m = 0` gives 1. -/
def Instance.bits {n : Nat} (x : Instance n) : Nat :=
  Nat.log2 x.maxValue + 1

/-- (1.1): «w = ⌈4(n + b + log₂(n + 2))⌉», that is `4(n + b) + ⌈log₂((n + 2)^4)⌉`, and `⌈log₂ M⌉ = ⌊log₂(M − 1)⌋ + 1`
for `M ≥ 2`. -/
def wordLength (n b : Nat) : Nat :=
  4 * (n + b) + Nat.log2 ((n + 2) ^ 4 - 1) + 1

/-- The memory at the start: `n` in cell 0, `a₁, …, aₙ` in cells 1, …, n, `t` in cell n + 1, and 0 in every other cell.
Each value has at most `b ≤ w` bits, so no word is truncated. -/
def Instance.input {n : Nat} (x : Instance n) : List Nat :=
  n :: (List.ofFn x.a ++ [x.t])

def loadWords (w : Nat) (ws : List Nat) : Nat → BitVec w :=
  fun a => BitVec.ofNat w (ws.getD a 0)

/-- One run of `P` on `x` with the random words `ρ`, in words of the length (1.1). -/
def run {n : Nat} (P : List Instr) (x : Instance n) (ρ : Nat → BitVec (wordLength n x.bits)) (t : Nat) :
    Option Bool :=
  exec P ρ t 0 0 (loadWords _ x.input)

/-- The random words `ρ 0, ρ 1, …` read off `s` as base-`2^w` digits, least significant first, 0 past its digits. As `s`
ranges over `0, …, 2^(w t) − 1`, the first `t` words range over all their `2^(w t)` equally likely values. -/
def tape (w : Nat) (s : Nat) : Nat → BitVec w :=
  fun r => BitVec.ofNat w (s / 2 ^ (w * r))

/-- The number of `s < N` with `p s`. -/
def count (p : Nat → Prop) [DecidablePred p] : Nat → Nat
  | 0 => 0
  | N + 1 => count p N + if p N then 1 else 0

/-- «halts on every execution and outputs the correct answer with probability at least 2/3»: for some horizon `t`, every
run halts within `t` steps, and the right verdict comes from at least two thirds of the `2^(w t)` equally likely
values of the first `t` random words, the only ones a run of at most `t` steps can read. A program that halts on
every execution has such a horizon by König's lemma, as each random word has finitely many values. -/
def Correct {n : Nat} (P : List Instr) (x : Instance n) : Prop :=
  ∃ t : Nat, (∀ ρ, (run P x ρ t).isSome) ∧
    let N := 2 ^ (wordLength n x.bits * t)
    (x.yes ∧ 2 * N ≤ 3 * count (fun s => run P x (tape _ s) t = some true) N) ∨
    (¬ x.yes ∧ 2 * N ≤ 3 * count (fun s => run P x (tape _ s) t = some false) N)

/-- `T(n) = O(2^(α n))`, both sides raised to the power `α.den`: core Lean has no fractional powers. For `α = 0.49 =
49/100` it says `T(n)^100 ≤ K 2^(49 n)`. -/
def BigO (T : Nat → Nat) (α : Rat) : Prop :=
  ∃ K : Nat, ∀ n ≥ 2, T n ^ α.den ≤ K * 2 ^ (α.num.toNat * n)

/-- Theorem 1.1 with `α` in place of 0.49: «a single finite program for all n and b», correct on every input with
`n ≥ 2`; «for every fixed positive integer c», a bound `T(n) = O(2^(α n))` on the steps of every run on every input
with `b ≤ n^c`. «The program is not given c and does not depend on c»: `P` comes before `c`. The thresholds `N_c` of
the paper are absorbed by `K`: for each `n`, finitely many inputs have `b ≤ n^c`, and each halts within some horizon. -/
def SolvedInTime (α : Rat) : Prop :=
  ∃ P : List Instr,
    (∀ (n : Nat) (x : Instance n), 2 ≤ n → Correct P x) ∧
    ∀ c : Nat, ∃ T : Nat → Nat, BigO T α ∧
      ∀ (n : Nat) (x : Instance n), 2 ≤ n → x.bits ≤ n ^ c → ∀ ρ, (run P x ρ (T n)).isSome

end BigOSpeedrun.SubsetSum


