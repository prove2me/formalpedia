-- Prove2me | Definitions.Def_ChapterSirkBandLedger
-- name    : ChapterSirkBandLedger
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T10:52:42.6606+00:00
-- url     : https://prove2.me/theorems/1bb6bb9e-1281-4cdc-b944-cb1e84ac6fb8
-- title:
--   Plan item **QYM-1, task 1** of `CONSOLIDATED_PLAN.md`: "prove that the certified bands the kernel emits are *nested comp ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkBandLedger`, source chapter `BookProof/ChapterSirkBandLedger.lean`).
--
--   Plan item **QYM-1, task 1** of `CONSOLIDATED_PLAN.md`: "prove that the certified bands the kernel emits are *nested compatible* enclosures in the sense `BandEnclosure` requires (same operator, mesh refinement) — a Lean statement over the band interface (`ChapterSirkCertificateReader` / `ChapterBandEnclosure`), not over f64 outputs."
--
--   `ChapterBandEnclosure` consumes its bands through one predicate, `BandEnclosure.NestedBands lo hi`, and everything downstream (`band_enclosure_of_nested`, `ritz_band_enclosure_of_nested`, `friedrichs_form_gap_of_nested_ritz_bands`) is stated for functions `lo hi : ℕ → ℝ`. What the emitter actually produces is a *finite* list of records, one per truncation order. This chapter is the missing adapter, and the proof that the adapter's output is nested.
--
--   * `BandRecord` — one emitted band: the operator tag `op` (constructor / version / coupling / truncation / enclosure-convention identity), the mesh order `order`, and the two endpoints `lo`, `hi` as **exact decimals** (`Decimal` of `ChapterSirkCertificateReader`; no `Float` occurs anywhere in this file). * `parseBandLine`, `parseLedger` — the reader for the NDJSON band stream, built from the exact-decimal parser of the certificate reader. * `ledgerLo`, `ledgerHi : List BandRecord → ℕ → ℝ` — the adapter: the order-`m` endpoints, extended by the last recorded band beyond the end of the ledger (a finite ledger says nothing after its last order, so it repeats it).
--
--   `LedgerWf L` is a **decidable** conjunction of exactly the conditions the plan names, checked on the recorded exact decimals:
--
--   * the ledger is non-empty; * **same operator**: every record carries the same operator tag; * the orders are `0, 1, 2, …` in sequence (no gaps, no reordering); * **mesh refinement**: `lo` is nondecreasing and `hi` is nonincreasing along the ledger; * each band encloses (`lo ≤ hi`).
--
--   `nestedBands_of_wf` : a well-formed ledger yields `NestedBands (ledgerLo L) (ledgerHi L)`. Composing with `ChapterBandEnclosure`:
--
--   * `ritz_band_enclosure_of_ledger` — for a bounded positive self-adjoint one-particle operator, every ledger band encloses `sInf (spectrum ℝ A)`; * `friedrichs_form_gap_of_ledger` — for the unbounded Hamiltonian on the finite-mode core, a ledger whose first band has lower end `≥ μ` gives `⟪y, A y⟫ ≥ μ‖y‖²` on the whole domain of the Friedrichs extension the Hashimoto shift-invert selects; * `friedrichs_form_gap_of_ledger_lo_zero` — the same, with `μ` read off the ledger's first band.
--
--   * Nesting and the "same operator" property are properties of the **recorded numbers and metadata**, and that is exactly what this chapter proves. That the order-`m` Ritz value really lies in the order-`m` band is the analytic / finite-precision input (`ChapterSirkFinitePrecision`, `ChapterSirkCertifiedGap`), carried here as the hypothesis `hritz` — it is not established by inspecting the ledger. * A **finite** ledger cannot certify band collapse: beyond its last order the extension repeats the last band, so the widths are eventually constant (`ledger_width_eventually_const`) and tend to `0` only if the last recorded width is `0` (`ledger_width_tendsto_zero_iff`). The theorems used above are precisely the ones that do *not* need vanishing widths; the collapse remains the analytic input (`ChapterH6.sirk_error_decay_exponential`). * No floating-point value is read: the endpoints are exact decimals, compared through integer cross-multiplication (`Decimal.leB`).
--
--   Everything in this module is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

import Definitions.Def_ChapterSirkCertificateReader
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
open BookProof.SirkCertificateReader
open BookProof.BandEnclosure
open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum
open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension


/-!
# QYM-1 task 1 — the emitted bands are *nested compatible* enclosures

Plan item **QYM-1, task 1** of `CONSOLIDATED_PLAN.md`: "prove that the certified
bands the kernel emits are *nested compatible* enclosures in the sense
`BandEnclosure` requires (same operator, mesh refinement) — a Lean statement over
the band interface (`ChapterSirkCertificateReader` / `ChapterBandEnclosure`), not
over f64 outputs."

`ChapterBandEnclosure` consumes its bands through one predicate,
`BandEnclosure.NestedBands lo hi`, and everything downstream
(`band_enclosure_of_nested`, `ritz_band_enclosure_of_nested`,
`friedrichs_form_gap_of_nested_ritz_bands`) is stated for functions
`lo hi : ℕ → ℝ`.  What the emitter actually produces is a *finite* list of
records, one per truncation order.  This chapter is the missing adapter, and the
proof that the adapter's output is nested.

## The ledger

* `BandRecord` — one emitted band: the operator tag `op` (constructor / version /
  coupling / truncation / enclosure-convention identity), the mesh order `order`,
  and the two endpoints `lo`, `hi` as **exact decimals** (`Decimal` of
  `ChapterSirkCertificateReader`; no `Float` occurs anywhere in this file).
* `parseBandLine`, `parseLedger` — the reader for the NDJSON band stream, built
  from the exact-decimal parser of the certificate reader.
* `ledgerLo`, `ledgerHi : List BandRecord → ℕ → ℝ` — the adapter: the order-`m`
  endpoints, extended by the last recorded band beyond the end of the ledger (a
  finite ledger says nothing after its last order, so it repeats it).

## The compatibility conditions, and the theorem

`LedgerWf L` is a **decidable** conjunction of exactly the conditions the plan
names, checked on the recorded exact decimals:

* the ledger is non-empty;
* **same operator**: every record carries the same operator tag;
* the orders are `0, 1, 2, …` in sequence (no gaps, no reordering);
* **mesh refinement**: `lo` is nondecreasing and `hi` is nonincreasing along the
  ledger;
* each band encloses (`lo ≤ hi`).

`nestedBands_of_wf` : a well-formed ledger yields
`NestedBands (ledgerLo L) (ledgerHi L)`.  Composing with `ChapterBandEnclosure`:

* `ritz_band_enclosure_of_ledger` — for a bounded positive self-adjoint
  one-particle operator, every ledger band encloses `sInf (spectrum ℝ A)`;
* `friedrichs_form_gap_of_ledger` — for the unbounded Hamiltonian on the
  finite-mode core, a ledger whose first band has lower end `≥ μ` gives
  `⟪y, A y⟫ ≥ μ‖y‖²` on the whole domain of the Friedrichs extension the
  Hashimoto shift-invert selects;
* `friedrichs_form_gap_of_ledger_lo_zero` — the same, with `μ` read off the
  ledger's first band.

## Honest boundary

* Nesting and the "same operator" property are properties of the **recorded
  numbers and metadata**, and that is exactly what this chapter proves.  That the
  order-`m` Ritz value really lies in the order-`m` band is the analytic /
  finite-precision input (`ChapterSirkFinitePrecision`, `ChapterSirkCertifiedGap`),
  carried here as the hypothesis `hritz` — it is not established by inspecting the
  ledger.
* A **finite** ledger cannot certify band collapse: beyond its last order the
  extension repeats the last band, so the widths are eventually constant
  (`ledger_width_eventually_const`) and tend to `0` only if the last recorded
  width is `0` (`ledger_width_tendsto_zero_iff`).  The theorems used above are
  precisely the ones that do *not* need vanishing widths; the collapse remains the
  analytic input (`ChapterH6.sirk_error_decay_exponential`).
* No floating-point value is read: the endpoints are exact decimals, compared
  through integer cross-multiplication (`Decimal.leB`).

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SirkBandLedger


/-! ## 1. Exact comparison of decimals -/

/-- Comparison of exact decimals by integer cross-multiplication: no division, no
`Float`, and cheap for the kernel to check. -/
def Decimal.leB (d e : Decimal) : Prop :=
  d.mant * 10 ^ e.exp ≤ e.mant * 10 ^ d.exp

instance (d e : Decimal) : Decidable (Decimal.leB d e) := by
  unfold Decimal.leB; infer_instance



/-! ## 2. The band ledger -/

/-- One emitted band: the operator identity tag, the mesh/truncation order, and the
two endpoints as exact decimals. -/
structure BandRecord where
  /-- The operator identity: constructor / version / coupling / truncation /
  enclosure convention, as emitted.  "Same operator" is equality of this tag. -/
  op : List Char
  /-- The mesh / truncation order this band was computed at. -/
  order : ℕ
  /-- The lower endpoint of the certified band. -/
  lo : Decimal
  /-- The upper endpoint of the certified band. -/
  hi : Decimal
deriving DecidableEq, Repr

instance : Inhabited BandRecord := ⟨⟨[], 0, ⟨0, 0⟩, ⟨0, 0⟩⟩⟩

/-- Parse one emitted band line, e.g.
`{"op":"qym3d/v1","order":0,"lo":0.90,"hi":2.40}`.  A band whose lower endpoint
exceeds its upper endpoint is rejected rather than trusted. -/
def parseBandLine (line : List Char) : Option BandRecord := do
  let opC ← fieldChars line "op".toList
  let ordC ← fieldChars line "order".toList
  let loC ← fieldChars line "lo".toList
  let hiC ← fieldChars line "hi".toList
  let ord ← parseNatDigits (ordC.filter (fun c => c != '"'))
  let lo ← parseDec loC
  let hi ← parseDec hiC
  if Decimal.leB lo hi then
    some ⟨opC.filter (fun c => c != '"'), ord, lo, hi⟩
  else
    none

/-- **The reader for the band stream.**  Every line that is a well-formed band
record is read; anything else (a header line, a trailing newline) is ignored. -/
def parseLedger (s : String) : List BandRecord :=
  (splitLines s.toList).filterMap parseBandLine

/-- The record the ledger supplies at order `m`: the `m`-th record while the
ledger lasts, its last record afterwards. -/
def recAt (L : List BandRecord) (m : ℕ) : BandRecord :=
  L.getD (min m (L.length - 1)) default

/-- The order-`m` lower endpoint, exactly. -/
def loQ (L : List BandRecord) (m : ℕ) : ℚ := (recAt L m).lo.toQ

/-- The order-`m` upper endpoint, exactly. -/
def hiQ (L : List BandRecord) (m : ℕ) : ℚ := (recAt L m).hi.toQ

/-- The order-`m` lower endpoint, as the real-valued band function
`ChapterBandEnclosure` consumes. -/
def ledgerLo (L : List BandRecord) (m : ℕ) : ℝ := ((loQ L m : ℚ) : ℝ)

/-- The order-`m` upper endpoint, as the real-valued band function
`ChapterBandEnclosure` consumes. -/
def ledgerHi (L : List BandRecord) (m : ℕ) : ℝ := ((hiQ L m : ℚ) : ℝ)

/-! ## 3. Nested compatibility, decidably checked -/

/-- **The compatibility conditions**, as a decidable check on the emitted data:
non-empty; one and the same operator tag throughout; the orders in sequence
`0, 1, 2, …`; the lower endpoints nondecreasing and the upper endpoints
nonincreasing (mesh refinement); and every band an enclosure. -/
def ledgerWfB (L : List BandRecord) : Bool :=
  !L.isEmpty &&
  L.all (fun r => r.op == (L.getD 0 default).op) &&
  (List.range L.length).all (fun i => (L.getD i default).order == i) &&
  (List.range (L.length - 1)).all (fun i =>
      decide (Decimal.leB (L.getD i default).lo (L.getD (i + 1) default).lo) &&
      decide (Decimal.leB (L.getD (i + 1) default).hi (L.getD i default).hi)) &&
  L.all (fun r => decide (Decimal.leB r.lo r.hi))

/-- A well-formed ledger. -/
def LedgerWf (L : List BandRecord) : Prop := ledgerWfB L = true

instance (L : List BandRecord) : Decidable (LedgerWf L) := by
  unfold LedgerWf; infer_instance























/-! ## 4. What a finite ledger can and cannot certify -/





/-! ## 5. Feeding the enclosure chain -/

section Bounded


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



end Bounded

section Unbounded


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]





end Unbounded

/-! ## 6. The wire format worked through

A three-order band stream in the emitted format.  The numbers are an
illustration of the format — the shape a refinement sequence has — not
transcribed solve output; what is *proved* about them is that they satisfy the
nested-compatibility conditions and therefore feed the enclosure chain. -/

-- The reader and the well-formedness check are evaluated by the kernel on the
-- example stream below; the default recursion depth is not enough for that.
set_option maxRecDepth 10000

/-- An emitted band stream at orders `0, 1, 2` for one and the same operator. -/
def formatExampleLedgerNdjson : String :=
  "{\"op\":\"qym3d/v1\",\"order\":0,\"lo\":0.900,\"hi\":2.400}\n" ++
  "{\"op\":\"qym3d/v1\",\"order\":1,\"lo\":1.500,\"hi\":2.100}\n" ++
  "{\"op\":\"qym3d/v1\",\"order\":2,\"lo\":1.850,\"hi\":1.960}\n"

/-- The parsed band stream. -/
def formatExampleLedger : List BandRecord :=
  [⟨"qym3d/v1".toList, 0, ⟨900, 3⟩, ⟨2400, 3⟩⟩,
   ⟨"qym3d/v1".toList, 1, ⟨1500, 3⟩, ⟨2100, 3⟩⟩,
   ⟨"qym3d/v1".toList, 2, ⟨1850, 3⟩, ⟨1960, 3⟩⟩]









end BookProof.SirkBandLedger


