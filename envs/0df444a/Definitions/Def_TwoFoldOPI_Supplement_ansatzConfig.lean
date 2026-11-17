-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_ansatzConfig
-- name    : TwoFoldOPI_Supplement_ansatzConfig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:56:57.138763+00:00
-- url     : https://prove2.me/theorems/7adb3a48-c10b-41d1-ad07-2005a2c0f7ee
-- title:
--   The input of Algorithm 8.1 in the memory of the field-operation machine
-- statement:
--   To count the field operations of Algorithm 8.1, its input $(\xi,B,A,h,w,s)$ is written in the memory of the published field-operation machine: $\xi$ at address $0$, then $B$ and $A$ row by row, then $h$, $w$ and $s$; index registers $0,1,2$ hold $m,n,\ell$, and everything else is $0$.
--
--   This start configuration is the input of the machine program in Theorem 8.2.
--
--   **Formalization Note** The codes $V=\operatorname{im}B^{\top}$ and $E$ (spanned by the rows of $A$) are determined by $B$ and $A$ and are not stored.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.1, Algorithm 8.1 and Theorem 8.2, p. 45

import Mathlib
import Definitions.Def_LinSysAmp_Machine

namespace TwoFoldOPI

namespace Supplement

/-- **The input of Algorithm 8.1 laid out in the memory of the field-operation machine.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.1, Algorithm 8.1, p.45 (Input: "a nonsquare ξ ∈ F_q^×; … a matrix B ∈ F_q^{n×m} …;
… A ∈ F_q^{ℓ×m}; A vector h ∈ F_q^m …; A vector w ∈ F_q^m …; A target syndrome s ∈ F_q^n") and
Theorem 8.2, p.45 ("Given ξ, the algorithm is deterministic and uses polynomially many field
operations in m, n, ℓ"); the machine is the published `LinSysAmp` field-operation machine.

The start configuration of a machine whose output has length `m`: index registers `0, 1, 2` hold
`m, n, ℓ`, all other registers and both counters are `0`, the program counter is `0`, and memory
holds, from address `0`:
* `ξ` at address `0`;
* `B` row-major: `B_{ij}` at `1 + m·i + j`;
* `A` row-major: `A_{ij}` at `a_A + m·i + j`, `a_A = 1 + n·m`;
* `h_j` at `a_A + ℓ·m + j`, `w_j` at `a_A + ℓ·m + m + j`, `s_i` at `a_A + ℓ·m + 2m + i`;
* `0` at every other address.

**Formalization Note.** The code `V = im Bᵀ` and `E` (spanned by the rows of `A`) are determined
by `B` and `A` and are not stored. Out-of-range reads return `0`; the `dite` guards never fail on
the addresses listed. -/
def ansatzConfig {K : Type*} [Zero K] (m n ℓ : ℕ) (ξ : K) (B : Matrix (Fin n) (Fin m) K)
    (A : Matrix (Fin ℓ) (Fin m) K) (h w : Fin m → K) (s : Fin n → K) : LinSysAmp.Config m K where
  pc := 0
  reg := fun _ => 0
  ireg := fun r => if r = 0 then (m : ℤ) else if r = 1 then (n : ℤ) else if r = 2 then (ℓ : ℤ) else 0
  mem := fun a =>
    let aA : ℤ := 1 + (n : ℤ) * m
    let ah : ℤ := aA + (ℓ : ℤ) * m
    if a = 0 then ξ
    else if 1 ≤ a ∧ a < aA then
      (if hB : ((a - 1) / m).toNat < n ∧ ((a - 1) % m).toNat < m then
        B ⟨((a - 1) / m).toNat, hB.1⟩ ⟨((a - 1) % m).toNat, hB.2⟩ else 0)
    else if aA ≤ a ∧ a < ah then
      (if hA : ((a - aA) / m).toNat < ℓ ∧ ((a - aA) % m).toNat < m then
        A ⟨((a - aA) / m).toNat, hA.1⟩ ⟨((a - aA) % m).toNat, hA.2⟩ else 0)
    else if ah ≤ a ∧ a < ah + m then
      (if hh : (a - ah).toNat < m then h ⟨(a - ah).toNat, hh⟩ else 0)
    else if ah + m ≤ a ∧ a < ah + 2 * m then
      (if hw : (a - ah - m).toNat < m then w ⟨(a - ah - m).toNat, hw⟩ else 0)
    else if ah + 2 * m ≤ a ∧ a < ah + 2 * m + n then
      (if hs : (a - ah - 2 * m).toNat < n then s ⟨(a - ah - 2 * m).toNat, hs⟩ else 0)
    else 0
  ops := 0
  calls := 0
  status := .running

end Supplement

end TwoFoldOPI


