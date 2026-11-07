-- Prove2me | Definitions.Def_TwoFoldOPI_pairConfig
-- name    : TwoFoldOPI_pairConfig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:51.672076+00:00
-- url     : https://prove2.me/theorems/8fa7948d-5272-4c64-8acb-fb5846fba3f2
-- title:
--   Input layout of Lemma 7.3's field-operation algorithm
-- statement:
--   The initial configuration of the field-operation machine for Lemma 7.3 on a matrix $H\in K^{r\times m}$ with tag $\mathrm{gen}$ and pairs presented as $(a_i,a'_i)$: index registers $0,1,2$ hold $m$, $r$ and $\mathrm{gen}$ ($1$ for a generator matrix, $0$ for a parity-check matrix); memory cell $mi+j$ holds $H_{ij}$, cell $rm+i$ holds $a_i$ and cell $rm+m+i$ holds $a'_i$; every other cell, register and counter is $0$, and the program counter is $0$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.2, Lemma 7.3 and its proof, p. 39

import Mathlib
import Definitions.Def_LinSysAmp_Machine

namespace TwoFoldOPI

/-- **The input layout of Lemma 7.3's classical algorithm.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.2, Lemma 7.3, p.39: "Let C ⊆ F_q^m be a code given by a generator or parity-check matrix
… The input to the algorithm consists of the unordered pairs {c_1, c′_1}, …, {c_m, c′_m}"; proof:
"Order each pair arbitrarily as (a_i, a′_i)".

The initial configuration of the field-operation machine (`LinSysAmp`, output length `m`):
index registers `0, 1, 2` hold `m`, `r` and `gen` (`1` for a generator matrix, `0` for a
parity-check matrix), all others `0`; memory cell `m·i + j` holds `H i j`, cell `r·m + i` holds
`a i` and cell `r·m + m + i` holds `a′ i`; all other cells, all field registers and both counters
are `0`; the program counter is `0`.

**Formalization Note.** This replaces the machine's own `initConfig`, whose layout is for
`n × n` linear systems. -/
def pairConfig {K : Type*} [Field K] [Fintype K] [DecidableEq K] (m r : ℕ) (gen : Bool)
    (H : Matrix (Fin r) (Fin m) K) (a a' : Fin m → K) : LinSysAmp.Config m K where
  pc := 0
  reg := fun _ => 0
  ireg := fun i => if i = 0 then (m : ℤ) else if i = 1 then (r : ℤ) else
    if i = 2 then (if gen then 1 else 0) else 0
  mem := (List.finRange r).foldr (fun (i : Fin r) acc => LinSysAmp.writeVec m acc ((m : ℤ) * (i.val : ℤ)) (H i))
    (LinSysAmp.writeVec m (LinSysAmp.writeVec m (fun _ => 0) ((r : ℤ) * m) a)
      ((r : ℤ) * m + m) a')
  ops := 0
  calls := 0
  status := .running

end TwoFoldOPI


