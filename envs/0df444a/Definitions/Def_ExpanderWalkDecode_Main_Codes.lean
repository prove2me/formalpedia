-- Prove2me | Definitions.Def_ExpanderWalkDecode_Main_Codes
-- name    : ExpanderWalkDecode_Main_Codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:42.443598+00:00
-- url     : https://prove2.me/theorems/98fc1708-32f5-4a55-b167-b7528967e630
-- title:
--   Binary linear codes, bias, rate, $\mathrm{LIST}(Y,\rho)$ and list decoding on the machine
-- statement:
--   A binary word of length $N$ is $y \in \mathbb F_2^N$, with sign vector $((-1)^{y_i})_i \in \{\pm1\}^N$. A **binary linear code** of blocklength $N$ is an $\mathbb F_2$-subspace $C \subseteq \mathbb F_2^N$. Its **rate** is $\log_2|C|/N$. The **correlation** of two words is
--   $$\langle y, c\rangle = \mathbb E_{i\sim[N]}\big[(-1)^{y_i}(-1)^{c_i}\big].$$
--   The code has **bias at most $\varepsilon$** if every nonzero codeword $c$ satisfies $\big|\mathbb E_{i\sim[N]}(-1)^{c_i}\big| \le \varepsilon$; equivalently every two distinct codewords have correlation of absolute value at most $\varepsilon$. For a received word $y$ and $\rho\in\mathbb R$,
--   $$\mathrm{LIST}(y,\rho) = \{c\in C : \langle y, c\rangle \ge \rho\}.$$
--
--   A program list-decodes the member $C^{(N)}$ of a code family at radius $\rho$ within $B$ steps with success probability $p$ if, for every received word $y$ of length $N$, run on the input $(N,\rho,y)$ (blocklength in an integer cell, $\rho$ and the signs of $y$ in real banks), it halts within $B$ steps on every coin string and outputs exactly $\mathrm{LIST}(y,\rho)$, written as the concatenated sign vectors of its codewords, each exactly once and in some order, with probability at least $p$ (Definition 1). The same program serves every blocklength of the family. A generator matrix is output as the concatenated bit vectors of a spanning family.
--
--   **Formalization Note** The bias is the standard absolute small-bias notion used by the paper's correlation arguments; it implies the $\varepsilon$-balanced distance condition of §1.
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 1 (§1, distance, rate, ε-balanced), p. 3 (§1.1, LIST), p. 8 (Definition 1)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Machine

namespace ExpanderWalkDecode.Main

open scoped Classical

/-!
# Binary linear codes, bias, rate, the list `LIST(Y, ρ)`, and list decoding on the machine

Source: §1 (p. 1), §1.1 (p. 3), Definition 1 (§3.1, p. 8). A word of length `N` is `Fin N → ZMod 2`;
its sign vector is `(-1)^{bit}`. Correlation is the uniform average of the coordinatewise product
of signs. Bias bounds the absolute sign average of every nonzero codeword (equivalently, the
absolute correlation of every pair of distinct codewords). `LIST(Y, ρ)` is the set of codewords
whose correlation with `Y` is at least `ρ`.

A list decoder is one machine program used for every member of a code family: on the input
`(N, ρ, Y)` (blocklength `N` in integer bank `0` at address `0`; `ρ` in real bank `0` at address
`0`; the signs `Y₀,…,Y_{N-1}` in real bank `1` at addresses `0,…,N-1`) it must output the list
`LIST(Y, ρ)`, written as the concatenated sign vectors of its codewords, each once, in any order.
-/

/-- A binary word of length `N`. -/
abbrev Word (N : ℕ) := Fin N → ZMod 2

/-- A binary linear code of blocklength `N`: an `F₂`-subspace of `F₂^N`. -/
abbrev BinaryLinearCode (N : ℕ) := Submodule (ZMod 2) (Word N)

/-- The sign `(-1)^b ∈ {±1}` of a bit. -/
def sgn (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

/-- Correlation `E_{i ∼ [N]} [(-1)^{y_i} (-1)^{c_i}]`. -/
noncomputable def corr {N : ℕ} (y c : Word N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, sgn (y i) * sgn (c i)

/-- `C` has bias at most `ε`: every nonzero codeword has absolute sign average at most `ε`. -/
def HasBias {N : ℕ} (C : BinaryLinearCode N) (ε : ℝ) : Prop :=
  ∀ c ∈ C, c ≠ 0 → |(N : ℝ)⁻¹ * ∑ i, sgn (c i)| ≤ ε

/-- The rate `log₂ |C| / N` (`0` when `N = 0`). -/
noncomputable def rate {N : ℕ} (C : BinaryLinearCode N) : ℝ :=
  Real.logb 2 (Nat.card C) / N

/-- `LIST(Y, ρ)`: the codewords of `C` whose correlation with `y` is at least `ρ`. -/
noncomputable def LIST {N : ℕ} (C : BinaryLinearCode N) (y : Word N) (ρ : ℝ) : Finset (Word N) :=
  Finset.univ.filter fun c => c ∈ C ∧ ρ ≤ corr y c

/-- The sign vector of a word, as a list of reals. -/
def signList {N : ℕ} (c : Word N) : List ℝ := List.ofFn fun i => sgn (c i)

/-- `out` lists the words of `L`, each exactly once and in some order, as concatenated sign
vectors. -/
def EncodesWordList {N : ℕ} (out : List ℝ) (L : Finset (Word N)) : Prop :=
  ∃ l : List (Word N), l.Nodup ∧ l.toFinset = L ∧ out = l.flatMap signList

/-- The input `(N, ρ, y)`: integer bank `0` holds `N` at address `0`; real bank `0` holds `ρ` at
address `0`; real bank `1` holds the signs of `y` at addresses `0, …, N-1`. All else is `0`. -/
noncomputable def receivedInput (N : ℕ) (ρ : ℝ) (y : Word N) : State :=
  init (fun k => if k = 0 then listBank [ρ] else if k = 1 then listBank (signList y) else fun _ => 0)
    (fun k => if k = 0 then listIBank [(N : ℤ)] else fun _ => 0)

/-- The program `P` list-decodes the member `C N` of the family `C` at radius `ρ` within `B` steps
with success probability at least `p`: on every received word `y` of length `N`, run on
`(N, ρ, y)`, it halts within `B` steps on every coin tape and outputs exactly `LIST(y, ρ)` with
probability at least `p`. -/
def ListDecodesWithin (P : Program) (C : ∀ N : ℕ, BinaryLinearCode N) (ρ : ℝ) (N : ℕ) (B p : ℝ) :
    Prop :=
  ∀ y : Word N, RunsWithin P (receivedInput N ρ y) B (fun out => EncodesWordList out (LIST (C N) y ρ)) p

/-- `out` lists the bits (as reals `0`, `1`) of a family of words of length `N` spanning `C`, the
words concatenated. This is the output format of a generator matrix. -/
def EncodesGenerator {N : ℕ} (out : List ℝ) (C : BinaryLinearCode N) : Prop :=
  ∃ rows : List (Word N),
    out = rows.flatMap (fun r => List.ofFn fun i => ((r i).val : ℝ)) ∧
    Submodule.span (ZMod 2) {r | r ∈ rows} = C

/-- The input `n` alone, in integer bank `0` at address `0`. -/
def natInput (n : ℕ) : State :=
  init (fun _ _ => 0) (fun k => if k = 0 then listIBank [(n : ℤ)] else fun _ => 0)

end ExpanderWalkDecode.Main


