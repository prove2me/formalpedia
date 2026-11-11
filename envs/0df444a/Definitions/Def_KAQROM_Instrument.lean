-- Prove2me | Definitions.Def_KAQROM_Instrument
-- name    : KAQROM_Instrument
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:27.691458+00:00
-- url     : https://prove2.me/theorems/878c2e50-b139-4ecc-8bcf-073f1121ca4d
-- title:
--   Quantum instruments in Kraus form
-- statement:
--   A **quantum instrument** from a register $R$ to a register $R'$ with classical outcomes in a finite set $O$ is a family of Kraus operators $K_{o,i}:\mathbb C^{R}\to\mathbb C^{R'}$, indexed by outcomes $o\in O$ and a finite index $i$, satisfying
--   $$
--   \sum_{o\in O}\sum_i K_{o,i}^\dagger K_{o,i}=\mathbb 1 .
--   $$
--   Applied to an operator $\rho$ with outcome $o$ it gives the unnormalized post-measurement state $\sum_i K_{o,i}\,\rho\,K_{o,i}^\dagger$, whose trace is the probability of $o$. A quantum channel is an instrument with a single outcome, and a POVM is an instrument onto a trivial register.
--
--   Instruments are the oracle-independent operations of the paper's oracle algorithms (Definition 3.1): every operation between two oracle queries, together with any classical outcomes it produces, is one instrument.
--
--   **Formalization Note** Registers are finite types and operators are complex matrices. The Kraus index type is a parameter; padding with zero operators lets one index type serve many instruments.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1, p.16; §3.2, p.16

import Mathlib

namespace KAQROM

open Matrix

/-- A **quantum instrument** with classical outcomes `O` from register `R` to register `R'`, given
by Kraus operators: for each outcome `o` a family `kraus o i : R' × R` (indexed by a finite type
`ι`), with `∑_o ∑_i (kraus o i)† (kraus o i) = 1` (trace preservation of the total operation).
A quantum channel is an instrument with one outcome (`O = Unit`); a POVM is an instrument whose
output register is trivial.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1,
p.16 ("oracle-independent operations") and §3.2, p.16.

**Formalization Note.** Registers are finite types and operators are complex matrices. The
paper's circuits interleave oracle-independent operations with measurements; every such
operation between two queries, with its classical outcomes, is one instrument (Stinespring:
parties are computationally unbounded and may use any workspace). The Kraus index type `ι` is a
parameter; padding with zero operators lets one `ι` serve every instrument of a protocol. -/
structure Instrument (O R R' ι : Type) [Fintype O] [Fintype R] [Fintype R'] [Fintype ι]
    [DecidableEq R] where
  /-- The Kraus operators of outcome `o`. -/
  kraus : O → ι → Matrix R' R ℂ
  /-- Trace preservation of the total operation. -/
  complete : ∑ o, ∑ i, (kraus o i)ᴴ * kraus o i = 1

/-- The unnormalized post-measurement state of outcome `o`: `∑_i K_{o,i} ρ K_{o,i}†`. Its trace
is the probability of `o` (times the trace of `ρ`). -/
noncomputable def Instrument.apply {O R R' ι : Type} [Fintype O] [Fintype R] [Fintype R']
    [Fintype ι] [DecidableEq R] (I : Instrument O R R' ι) (o : O) (ρ : Matrix R R ℂ) :
    Matrix R' R' ℂ :=
  ∑ i, I.kraus o i * ρ * (I.kraus o i)ᴴ

end KAQROM


