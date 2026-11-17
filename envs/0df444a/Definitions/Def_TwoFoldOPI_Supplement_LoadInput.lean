-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_LoadInput
-- name    : TwoFoldOPI_Supplement_LoadInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:57:55.773431+00:00
-- url     : https://prove2.me/theorems/6dcaa8fd-cdf2-4f6e-90de-399128dc3fe4
-- title:
--   A load set given as in Definition 10.2, as algorithm input
-- statement:
--   A load set is given to an algorithm by $m$, $n$, the allowed loads $B_a\subseteq\{0,\dots,m\}$ of every symbol $a\in[n]$ — as indicator tables or as Boolean membership circuits on $\lceil\log_2(m+1)\rceil$ bits — and the precision parameter $t=\lceil\log_2(1/\epsilon)\rceil$.
--
--   The encoding writes $m,n,t$ in self-delimiting binary followed by the tables or circuits; the size parameter is $m+n+t$ plus the total circuit size.
--
--   **Formalization Note** Circuits that are uniformly constructible in $\mathrm{poly}(m,n)$ time are covered by composing that construction with an algorithm for public circuits.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.1, Definition 10.2, p. 53; §10.2, Theorem 10.5, p. 54

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_LearningSeparation

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **A load set given as in Definition 10.2, with a precision parameter, as algorithm input.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.1, Definition 10.2, p.53: "For each symbol a ∈ [n], let B_a ⊆ {0, 1, …, m} be given by
its indicator table or by a membership circuit of size poly(m, n). In the circuit representation,
the circuits are public input or are uniformly constructible in poly(m, n) time, and decide k ∈ B_a
for every a ∈ [n] and 0 ≤ k ≤ m."; Theorem 10.5, p.54 ("to trace-distance error ϵ").

An input is `m`, `n`, the allowed loads `B_a` (`a ∈ [n] = {0, …, n−1}`) either as indicator
tables `tab a k` (`0 ≤ k ≤ m`) or as Boolean circuits `C_a` on `⌈log₂(m+1)⌉` input bits (`k`
in binary, most significant bit first), and `t = ⌈log₂(1/ϵ)⌉`.
* `allowedLoads x a = B_a = {k ≤ m : tab a k = 1}`, resp. `{k ≤ m : C_a(k) = 1}`;
* `encode` writes `m, n, t` in self-delimiting binary, a tag bit, and then the tables (bit by
  bit) or the circuits (`QAlgorithms.Learning.encBoolCircuit`);
* `scale = m + n + t`, plus the total number of gates of the circuits in the circuit case.

**Formalization Note.** The module holds the input type with its decoding, encoding and size. Circuits
that are "uniformly constructible in poly(m, n) time" are covered by composing that constructor
with an algorithm for public circuits. -/
structure LoadInput where
  /-- The word length. -/
  m : ℕ
  /-- The alphabet size. -/
  n : ℕ
  /-- The allowed loads: indicator tables (`inl`) or membership circuits (`inr`). -/
  allowed : (Fin n → Fin (m + 1) → Bool) ⊕ (Fin n → BoolCircuit (Nat.clog 2 (m + 1)) 1)
  /-- The precision parameter `⌈log₂(1/ϵ)⌉`. -/
  t : ℕ

/-- The allowed loads `B_a ⊆ {0, …, m}` of symbol `a`. -/
def LoadInput.allowedLoads (x : LoadInput) (a : Fin x.n) : Set ℕ :=
  {k | ∃ hk : k < x.m + 1,
    match x.allowed with
    | .inl tab => tab a ⟨k, hk⟩ = true
    | .inr C => (C a).eval (natToBits (Nat.clog 2 (x.m + 1)) k) 0 = true}

/-- The bit encoding of an input. -/
def LoadInput.encode (x : LoadInput) : List Bool :=
  LocalHamiltonian.encBin x.m ++ LocalHamiltonian.encBin x.n ++ LocalHamiltonian.encBin x.t ++
    match x.allowed with
    | .inl tab => false :: (List.ofFn fun a => List.ofFn (tab a)).flatten
    | .inr C => true :: (List.ofFn fun a => Learning.encBoolCircuit (C a)).flatten

/-- The size parameter. -/
def LoadInput.scale (x : LoadInput) : ℕ :=
  x.m + x.n + x.t +
    match x.allowed with
    | .inl _ => 0
    | .inr C => ∑ a, (C a).size

end Supplement

end TwoFoldOPI


