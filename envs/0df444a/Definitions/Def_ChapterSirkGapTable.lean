-- Prove2me | Definitions.Def_ChapterSirkGapTable
-- name    : ChapterSirkGapTable
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T09:13:50.765571+00:00
-- url     : https://prove2.me/theorems/4f50eb5b-44ba-4577-80af-06f69580dc13
-- title:
--   `CONSOLIDATED_PLAN.md` §13.7 (T11 and T12). T6 (`ChapterSirkCertifiedGap`) turns one emitted certificate into a lower bo ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkGapTable`, source chapter `BookProof/ChapterSirkGapTable.lean`).
--
--   `CONSOLIDATED_PLAN.md` §13.7 (T11 and T12). T6 (`ChapterSirkCertifiedGap`) turns one emitted certificate into a lower bound for the parity gap of the truncated Hamiltonian. Two things are still wanted around it:
--
--   * **T11** — a *table*: one certified row per coupling constant `g`, each row a T6 instantiation, together with the comparison against the analytic strong-coupling value `g²/2`; * **T12** — the finite-size → thermodynamic-limit **Richardson extrapolation**, stated as the conditional theorem the plan asks for ("if the finite-size correction is `O(l^{-p})` for a known `p`, then the extrapolated gap is …").
--
--   * Every certified statement is about the **truncated** operator `H_m(g)` at the given coupling; the continuum passage is the standing boundary of §13 and is not used. * The rows of the table are *conditional*: a row proves what it proves given the two (or, for the two-sided version, four) enclosures the certificate for that coupling asserts. The repository records the aggregates of exactly one solve — the `g = 2`, `m = 4` run — so exactly one row is instantiated with data; the rest of the table is the general statement, ready to be instantiated when further certificates are emitted. * The Richardson section proves an *algebraic identity and its error propagation*. The numerical values it is evaluated on are transcribed data, and the extrapolated number is a numerical estimate, not a certified bound: nothing here claims the thermodynamic-limit gap.
--
--   * `gap_le_of_certificate` — the upper half of T6, so a certificate with two-sided enclosures gives a genuine *enclosure* `certified_gap_mem_interval` of the sector gap. * `CouplingCertificate`, `CouplingCertificate.lo/hi`, **T11** `certified_gap_table` (every row of a table of certificates bounds the gap of its own operator from below) and `certified_gap_table_interval` (the two-sided form). * `strongCoupling`, `strongCoupling_lt` and `strongCoupling_mem_of_certificate` — the analytic `g²/2` prediction, its strict monotonicity in the coupling, and the per-row consistency check; `qcdG2M4_row`, `qcdG2M4_row_lo`, `qcdG2M4_strongCoupling_consistent` — the one recorded row, whose certified window `[1.932, 2.043]` does contain the analytic value `g²/2 = 2` at `g = 2`. * **T12** `richardson`, `richardson_exact` (the extrapolation is exact for a pure `C·l^{-p}` correction), `richardson_error` (its error propagation), and `richardson_qym_g4` — the evaluation on the recorded finite-size data.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

import Definitions.Def_ChapterSirkCertifiedGap
import Mathlib

import Mathlib

/-!
# Chapter SirkGapTable — the per-coupling certified gap table and Richardson extrapolation
(T11, T12)

`CONSOLIDATED_PLAN.md` §13.7 (T11 and T12).  T6 (`ChapterSirkCertifiedGap`) turns one
emitted certificate into a lower bound for the parity gap of the truncated Hamiltonian.
Two things are still wanted around it:

* **T11** — a *table*: one certified row per coupling constant `g`, each row a T6
  instantiation, together with the comparison against the analytic strong-coupling
  value `g²/2`;
* **T12** — the finite-size → thermodynamic-limit **Richardson extrapolation**, stated
  as the conditional theorem the plan asks for ("if the finite-size correction is
  `O(l^{-p})` for a known `p`, then the extrapolated gap is …").

## Honest boundary

* Every certified statement is about the **truncated** operator `H_m(g)` at the given
  coupling; the continuum passage is the standing boundary of §13 and is not used.
* The rows of the table are *conditional*: a row proves what it proves given the two
  (or, for the two-sided version, four) enclosures the certificate for that coupling
  asserts.  The repository records the aggregates of exactly one solve — the `g = 2`,
  `m = 4` run — so exactly one row is instantiated with data; the rest of the table is
  the general statement, ready to be instantiated when further certificates are emitted.
* The Richardson section proves an *algebraic identity and its error propagation*.  The
  numerical values it is evaluated on are transcribed data, and the extrapolated number
  is a numerical estimate, not a certified bound: nothing here claims the
  thermodynamic-limit gap.

## Deliverables

* `gap_le_of_certificate` — the upper half of T6, so a certificate with two-sided
  enclosures gives a genuine *enclosure* `certified_gap_mem_interval` of the sector gap.
* `CouplingCertificate`, `CouplingCertificate.lo/hi`, **T11** `certified_gap_table`
  (every row of a table of certificates bounds the gap of its own operator from below)
  and `certified_gap_table_interval` (the two-sided form).
* `strongCoupling`, `strongCoupling_lt` and `strongCoupling_mem_of_certificate` — the
  analytic `g²/2` prediction, its strict monotonicity in the coupling, and the
  per-row consistency check; `qcdG2M4_row`, `qcdG2M4_row_lo`,
  `qcdG2M4_strongCoupling_consistent` — the one recorded row, whose certified window
  `[1.932, 2.043]` does contain the analytic value `g²/2 = 2` at `g = 2`.
* **T12** `richardson`, `richardson_exact` (the extrapolation is exact for a pure
  `C·l^{-p}` correction), `richardson_error` (its error propagation), and
  `richardson_qym_g4` — the evaluation on the recorded finite-size data.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.SirkGapTable

open BookProof.SirkCertifiedGap

/-! ## 1. The upper half: a certificate encloses the gap -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]





end Operator

/-! ## 2. T11 — the per-coupling table -/

/-- One row of the certified gap table: a coupling constant with the measured sector
Ritz difference and the assembled width of its solve. -/
structure CouplingCertificate where
  /-- The coupling constant `g` of the row. -/
  g : ℝ
  /-- The measured sector Ritz difference `θᵒ − θᵉ`. -/
  gap : ℝ
  /-- The assembled certified width `δᵒ + δᵉ`. -/
  width : ℝ
  /-- Widths are nonnegative. -/
  width_nonneg : 0 ≤ width

/-- The lower end of a row's certified window. -/
def CouplingCertificate.lo (c : CouplingCertificate) : ℝ := c.gap - c.width

/-- The upper end of a row's certified window. -/
def CouplingCertificate.hi (c : CouplingCertificate) : ℝ := c.gap + c.width



section Table

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]





end Table

/-! ## 3. The analytic strong-coupling value and the per-row check -/

/-- The analytic strong-coupling prediction for the parity gap: `g²/2`.  (The excluded
`O(g⁴)` magnetic correction is kept outside, exactly as in
`certified_parity_gap_strong_coupling`.) -/
def strongCoupling (g : ℝ) : ℝ := g ^ 2 / 2



/-- A row is *consistent with the strong-coupling prediction* when the analytic value
`g²/2` lies inside its certified window. -/
def CouplingCertificate.strongCouplingConsistent (c : CouplingCertificate) : Prop :=
  strongCoupling c.g ∈ Set.Icc c.lo c.hi



/-- The one row the repository records: the `g = 2`, `m = 4` run of the lattice-era
cross-benchmark (historical fixture; the mass-gap object of record is the gauge-fixed
QYM Hamiltonian `qcd_ym_hamiltonian(g)`, whose reflection-sector certificates fill the
same row type), measured sector gap `1.9875`, assembled width `0.0555` (the same two
transcribed numbers
as `SirkCertifiedGap.qcdG2M4`). -/
def qcdG2M4Row : CouplingCertificate where
  g := 2
  gap := 1.9875
  width := 0.0555
  width_nonneg := by norm_num





/-! ## 4. T12 — Richardson extrapolation of the finite-size gaps

The plan writes the extrapolation as `Δ(∞) ≈ Δ(l₂) + (Δ(l₂) − Δ(l₁))/((l₁/l₂)^p − 1)`.
With `l₁ < l₂` that ratio is the wrong way round — the correction then *adds* the tail
instead of cancelling it — so the definition below uses `(l₂/l₁)^p − 1`, which is what
makes the extrapolation exact (`richardson_exact`). -/

open Real

/-- The Richardson extrapolant of two finite-size values `d₁ = Δ(l₁)`, `d₂ = Δ(l₂)` for a
leading correction exponent `p`. -/
def richardson (d1 d2 l1 l2 p : ℝ) : ℝ := d2 + (d2 - d1) / ((l2 / l1) ^ p - 1)







/-! ### The recorded finite-size data

The three numbers below are transcribed numerical data (the `g = 4` finite-size study of
the lattice-era cross-benchmark at sizes `l = 2, 3, 4` — a solver-level record only,
*not* part of the gauge-fixed formalization chain).  The theorem is the *evaluation* of the
extrapolant on
them for `p = 2`; it is a numerical record, not a certified bound on the
thermodynamic-limit gap. -/

/-- The recorded finite-size gap at lattice size `l = 3`, coupling `g = 4`. -/
def qymG4L3 : ℝ := 7.999826

/-- The recorded finite-size gap at lattice size `l = 4`, coupling `g = 4`. -/
def qymG4L4 : ℝ := 7.999830





end BookProof.SirkGapTable


