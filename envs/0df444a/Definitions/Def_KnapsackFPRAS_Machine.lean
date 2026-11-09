-- Prove2me | Definitions.Def_KnapsackFPRAS_Machine
-- name    : KnapsackFPRAS_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:47.716268+00:00
-- url     : https://prove2.me/theorems/68e431fe-a97f-4490-8ddd-8d184b5e4e5b
-- title:
--   The randomized word RAM: instructions, runs, input layout, output, coin tape
-- statement:
--   The machine of Theorem 1.1. A **program** is a finite list of instructions. The memory is an infinite array of cells $[0],[1],\dots$, each holding an unsigned $W$-bit word. The instructions are: the constant $[i]:=1$; $[i]:=[j]\circ[k]$ for $\circ\in\{+,-,\times,\div,\bmod,\wedge,\vee,\oplus,\ll,\gg\}$, computed modulo $2^W$ with $x\div0=0$, $x\bmod0=x$ and shifts by $W$ or more bits giving $0$; indirect load $[i]:=[[j]]$ and store $[[i]]:=[j]$; `rand i`, which stores the next word of the **random tape** $\rho_0,\rho_1,\dots$ (each word read once); the branch "if $[i]<[j]$ go to position $\ell$"; and `halt`. Every executed instruction costs one step, and running past the end of the program halts.
--
--   A run is described by `exec P ρ t pc r m`: it returns the final memory if the program, started at position `pc` on memory `m` with tape words $\rho_r,\rho_{r+1},\dots$ still unread, halts within $t$ steps (the halting step counted), and nothing otherwise.
--
--   The module also fixes:
--
--   1. the **input layout**: cell $0$ holds $n$, cell $1$ holds $T$, cell $2$ holds $K$, cells $3,\dots,n+2$ hold the weights, the following cells hold any extra input words, and every other cell holds $0$;
--   2. the **word length** $W=c\,(\lfloor\log_2(n+1)\rfloor+\lfloor\log_2K\rfloor+\lfloor\log_2(T+1)\rfloor+1)$, that is $O(\log(n/\varepsilon)+\log T)$ bits when $K=\lceil1/\varepsilon\rceil$;
--   3. the **output** of a halted run, $\hat F=[0]\cdot2^{[1]}$, where cell $0$ is read unsigned and cell $1$ as a signed (two's-complement) exponent;
--   4. the **coin tape** of an integer $s$: the words $\rho_r=\lfloor s/2^{Wr}\rfloor\bmod 2^W$. As $s$ ranges over $\{0,\dots,2^{WN}-1\}$ the first $N$ words take every value equally often, so counting the values of $s$ is computing a probability;
--   5. `count p N`, the number of $s<N$ with property $p$.
--
--   **Formalization Note** The paper says only "the word RAM model with $O(\log(n/\varepsilon)+\log T)$-bit words". No instruction computes a real number, an exponential, a logarithm or a sum over subsets; the paper's $O(\kappa)$-bit floating-point arithmetic is software on this machine. The instruction set is that of the public `BigOSpeedrun.SubsetSum` model, with `halt` in place of accept/reject so that a run returns its memory.
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Theorem 1.1, p.1 (PDF p.2); footnote 6, p.54 (PDF p.55); machine not specified in the paper

import Mathlib

set_option autoImplicit false

namespace KnapsackFPRAS

/-! # The randomized word RAM

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Theorem 1.1, p.1 (PDF p.2): "in the word RAM model with
O(log(𝑛/𝜀) + log 𝑇)-bit words"; footnote 6, p.54 (PDF p.55): "We stop the algorithm if its
running time exceeds a sufficiently large constant times Õ(𝑛 + 𝑁samp ℓ) and return 0."

**Formalization Note.** The paper names no instruction set. This module fixes the standard one:
words are unsigned `W`-bit words (`BitVec W`); memory is `ℕ → BitVec W`; operands `i j k` are
cell addresses fixed in the program and `l` is a program position. Arithmetic is modulo `2^W`,
`x / 0 = 0`, `x % 0 = x`, and a shift by `W` or more bits gives `0` (the `BitVec` conventions).
`load`/`store` are indirect accesses. `rand i` stores the next word of the random tape
`ρ : ℕ → BitVec W` (one fresh uniform word per `rand`, read once). Every executed instruction is
one step; `halt`, and running past the end of the program, stop the machine. There is no
floating point, no `exp`/`log`, no real register and no instruction that counts or sums over
subsets: the paper's `O(κ)`-bit floating-point arithmetic is software on this machine. The
instruction set and `exec` follow the public `BigOSpeedrun.SubsetSum` model (24e98b31), with
`accept`/`reject` replaced by `halt` and `exec` returning the final memory. -/

namespace Machine

/-- The instruction set. `[i]` is the word in cell `i`; the only constant is `1`. -/
inductive Instr where
  /-- `[i] := 1` -/
  | one (i : ℕ)
  /-- `[i] := [j] + [k]` -/
  | add (i j k : ℕ)
  /-- `[i] := [j] - [k]` -/
  | sub (i j k : ℕ)
  /-- `[i] := [j] * [k]` -/
  | mul (i j k : ℕ)
  /-- `[i] := [j] / [k]` -/
  | div (i j k : ℕ)
  /-- `[i] := [j] % [k]` -/
  | rem (i j k : ℕ)
  /-- `[i] := [j] &&& [k]` -/
  | and (i j k : ℕ)
  /-- `[i] := [j] ||| [k]` -/
  | or (i j k : ℕ)
  /-- `[i] := [j] ^^^ [k]` -/
  | xor (i j k : ℕ)
  /-- `[i] := [j] <<< [k]` -/
  | shl (i j k : ℕ)
  /-- `[i] := [j] >>> [k]` -/
  | shr (i j k : ℕ)
  /-- `[i] := [[j]]` -/
  | load (i j : ℕ)
  /-- `[[i]] := [j]` -/
  | store (i j : ℕ)
  /-- `[i] :=` the next random word -/
  | rand (i : ℕ)
  /-- if `[i] < [j]` go to position `l` -/
  | blt (i j l : ℕ)
  /-- stop -/
  | halt

/-- `exec P ρ t pc r m`: run program `P` from position `pc` on memory `m`, with the random words
`ρ r, ρ (r + 1), …` not yet read. It is `some m'` if the machine halts within `t` steps (the
halting step counted) with final memory `m'`, and `none` otherwise. Past its end the program
halts. -/
def exec {W : ℕ} (P : List Instr) (ρ : ℕ → BitVec W) :
    (t pc r : ℕ) → (m : ℕ → BitVec W) → Option (ℕ → BitVec W)
  | 0, _, _, _ => none
  | t + 1, pc, r, m =>
    let write (i : ℕ) (v : BitVec W) := exec P ρ t (pc + 1) r fun x => if x = i then v else m x
    match P.getD pc .halt with
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
    | .halt => some m

/-- The initial memory: `n` in cell 0, `T` in cell 1, `K` in cell 2, the (capped) weights
`w' 0, …, w' (n−1)` in cells `3, …, n + 2`, the extra words `extra` in cells `n + 3, …`, and `0`
in every other cell. Values are reduced modulo `2^W` (`BitVec.ofNat`). -/
def input (W n T K : ℕ) (w' : Fin n → ℕ) (extra : List ℕ) : ℕ → BitVec W := fun a =>
  if a = 0 then BitVec.ofNat W n
  else if a = 1 then BitVec.ofNat W T
  else if a = 2 then BitVec.ofNat W K
  else if h : a - 3 < n then BitVec.ofNat W (w' ⟨a - 3, h⟩)
  else BitVec.ofNat W (extra.getD (a - 3 - n) 0)

/-- The word length `c · (⌊log₂(n+1)⌋ + ⌊log₂ K⌋ + ⌊log₂(T+1)⌋ + 1)`: "O(log(n/ε) + log T)-bit
words" with one coefficient `c`, where `K = ⌈1/ε⌉`. -/
def wordLen (c n K T : ℕ) : ℕ :=
  c * (Nat.log2 (n + 1) + Nat.log2 K + Nat.log2 (T + 1) + 1)

/-- The number output by a halted machine: `F̂ = [0] · 2^{[1]}`, the mantissa in cell 0 read
unsigned and the exponent in cell 1 read as a signed (two's-complement) word. -/
noncomputable def outReal {W : ℕ} (m : ℕ → BitVec W) : ℝ :=
  ((m 0).toNat : ℝ) * (2 : ℝ) ^ (m 1).toInt

/-- The random words `ρ 0, ρ 1, …` read off `s` as base-`2^W` digits, least significant first.
As `s` ranges over `0, …, 2^(W t) − 1`, the first `t` words range over all their `2^(W t)`
equally likely values. -/
def tape (W s : ℕ) : ℕ → BitVec W :=
  fun r => BitVec.ofNat W (s / 2 ^ (W * r))

/-- The number of `s < N` with `p s`. -/
noncomputable def count (p : ℕ → Prop) (N : ℕ) : ℕ :=
  Nat.card {s : Fin N // p s}

end Machine

end KnapsackFPRAS


