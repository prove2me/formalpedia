-- Prove2me | Definitions.Def_ChapterSirkCertificateReader
-- name    : ChapterSirkCertificateReader
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T10:49:09.948837+00:00
-- url     : https://prove2.me/theorems/f8edbec6-0e7d-4f07-9fb5-1391a696f747
-- title:
--   `CONSOLIDATED_PLAN.md` §13.4 / §13.7 (T8). `ChapterSirkCertifiedGap` proves the certified-gap theorem **T6** for the tru ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkCertificateReader`, source chapter `BookProof/ChapterSirkCertificateReader.lean`).
--
--   `CONSOLIDATED_PLAN.md` §13.4 / §13.7 (T8). `ChapterSirkCertifiedGap` proves the certified-gap theorem **T6** for the truncated Hamiltonian; the kernel's certificate emitter writes, one JSON object per line, a parity label together with the sector Ritz value `θ` and the assembled width `δ = residual + roundoff + enclosure`. This chapter is the missing *reader*: a parser that turns those lines into the parameters of T6, and the theorems that make a parsed line usable inside a proof.
--
--   * **No floating-point value is trusted, and none is even used.** The wire format is read as an *exact decimal literal*: `Decimal` records a mantissa and a power of ten, so `-0.4231` becomes `(-4231, 4)` and its value `(-4231 : ℚ)/10^4` is exact. Nothing in this file mentions `Float`. * **No numerical claim is verified here.** The parser is a total function on strings; the theorems are *conditional* on the two enclosures the certificate asserts (`sectorGround ≤ θᵉ + δᵉ` and `θᵒ − δᵒ ≤ sectorGround`), exactly as T6 is. Those enclosures are what the finite-precision layer `ChapterSirkFinitePrecision` (T1–T5) supplies for a given solve; the reader only carries the numbers across. * Every statement is about the **truncated** operator: the continuum leg stays the recorded boundary of §13.
--
--   * `Decimal`, `Decimal.toQ`, `parseDec` — exact decimal literals, with `parseDec_neg_example` and friends as reduction sanity checks. * `fieldChars`, `parseSectorLine`, `parseCertificate`, `ndjsonLower` — the reader: NDJSON text ↦ the two sector records ↦ the certified lower bound `θᵒ − θᵉ − (δᵒ + δᵉ)` as an exact rational. * `CertificateData.toGapCertificate` — the bridge to `SirkCertifiedGap.GapCertificate`, refusing (rather than trusting) a negative assembled width. * **T8** `gap_ge_of_ndjson` and `gap_pos_of_ndjson`: what a parsed certificate proves about the sector gap of the truncated Hamiltonian, via T6. * `formatExampleNdjson` with `formatExample_parse`, `formatExample_lower` and `formatExample_certified_gap` — the wire format worked through end to end on the recorded `g = 2`, `m = 4` aggregates.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

import Definitions.Def_ChapterSirkCertifiedGap
import Mathlib

import Mathlib

/-!
# Chapter SirkCertificateReader — the instantiation seam (T8)

`CONSOLIDATED_PLAN.md` §13.4 / §13.7 (T8).  `ChapterSirkCertifiedGap` proves the
certified-gap theorem **T6** for the truncated Hamiltonian; the kernel's certificate
emitter writes, one JSON object per line, a parity label together with the sector Ritz
value `θ` and the assembled width `δ = residual + roundoff + enclosure`.  This chapter
is the missing *reader*: a parser that turns those lines into the parameters of T6, and
the theorems that make a parsed line usable inside a proof.

## What is and is not trusted

* **No floating-point value is trusted, and none is even used.**  The wire format is
  read as an *exact decimal literal*: `Decimal` records a mantissa and a power of ten,
  so `-0.4231` becomes `(-4231, 4)` and its value `(-4231 : ℚ)/10^4` is exact.  Nothing
  in this file mentions `Float`.
* **No numerical claim is verified here.**  The parser is a total function on strings;
  the theorems are *conditional* on the two enclosures the certificate asserts
  (`sectorGround ≤ θᵉ + δᵉ` and `θᵒ − δᵒ ≤ sectorGround`), exactly as T6 is.  Those
  enclosures are what the finite-precision layer `ChapterSirkFinitePrecision` (T1–T5)
  supplies for a given solve; the reader only carries the numbers across.
* Every statement is about the **truncated** operator: the continuum leg stays the
  recorded boundary of §13.

## Deliverables

* `Decimal`, `Decimal.toQ`, `parseDec` — exact decimal literals, with
  `parseDec_neg_example` and friends as reduction sanity checks.
* `fieldChars`, `parseSectorLine`, `parseCertificate`, `ndjsonLower` — the reader:
  NDJSON text ↦ the two sector records ↦ the certified lower bound `θᵒ − θᵉ − (δᵒ + δᵉ)`
  as an exact rational.
* `CertificateData.toGapCertificate` — the bridge to `SirkCertifiedGap.GapCertificate`,
  refusing (rather than trusting) a negative assembled width.
* **T8** `gap_ge_of_ndjson` and `gap_pos_of_ndjson`: what a parsed certificate proves
  about the sector gap of the truncated Hamiltonian, via T6.
* `formatExampleNdjson` with `formatExample_parse`, `formatExample_lower` and
  `formatExample_certified_gap` — the wire format worked through end to end on the
  recorded `g = 2`, `m = 4` aggregates.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SirkCertificateReader

open BookProof.SirkCertifiedGap

/-! ## 1. Exact decimal literals

The reader never produces a `Float`.  A decimal literal is stored as a mantissa and a
power of ten, so its value is an exact rational. -/

/-- A decimal literal `mant · 10^(-exp)`, stored exactly. -/
structure Decimal where
  /-- The mantissa (all the digits, sign included). -/
  mant : ℤ
  /-- The number of fractional digits. -/
  exp : ℕ
deriving DecidableEq, Repr

/-- The exact rational value of a decimal literal. -/
def Decimal.toQ (d : Decimal) : ℚ := (d.mant : ℚ) / (10 : ℚ) ^ d.exp



/-- The digit value of a character. -/
def digitVal : Char → Option ℕ
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

/-- Horner accumulation of a digit string. -/
def digitsAux : ℕ → List Char → Option ℕ
  | acc, [] => some acc
  | acc, c :: cs =>
      match digitVal c with
      | none => none
      | some d => digitsAux (10 * acc + d) cs

/-- Parse a nonempty string of decimal digits. -/
def parseNatDigits : List Char → Option ℕ
  | [] => none
  | l => digitsAux 0 l

/-- Split a character list at the first `'.'`; the second component is `none` when there
is no decimal point. -/
def splitDot : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
      if c == '.' then ([], some cs)
      else
        let r := splitDot cs
        (c :: r.1, r.2)

/-- Parse an unsigned decimal literal. -/
def parseUnsignedDec (l : List Char) : Option Decimal :=
  match splitDot l with
  | (i, none) => (parseNatDigits i).map (fun n => ⟨(n : ℤ), 0⟩)
  | (i, some f) => do
      let n ← parseNatDigits i
      let m ← parseNatDigits f
      some ⟨((n * 10 ^ f.length + m : ℕ) : ℤ), f.length⟩

/-- Parse a signed decimal literal. -/
def parseDec : List Char → Option Decimal
  | '-' :: rest => (parseUnsignedDec rest).map (fun d => ⟨-d.mant, d.exp⟩)
  | '+' :: rest => parseUnsignedDec rest
  | l => parseUnsignedDec l









/-! ## 2. Reading a JSON object line

The emitted format is one flat JSON object per line, e.g.

```
{"sector":"even","theta":-0.4231,"delta":0.0271}
```

Only the three fields the proof consumes are read; any other field is ignored, and a
line missing one of them fails to parse (it is never defaulted). -/

/-- Match a literal prefix, returning the remainder. -/
def matchPrefix : List Char → List Char → Option (List Char)
  | [], l => some l
  | _ :: _, [] => none
  | p :: ps, x :: xs => if p == x then matchPrefix ps xs else none

/-- The remainder of `l` after the first occurrence of the pattern `pat`. -/
def findAfter (pat : List Char) : List Char → Option (List Char)
  | [] => matchPrefix pat []
  | x :: xs =>
      match matchPrefix pat (x :: xs) with
      | some r => some r
      | none => findAfter pat xs

/-- The raw value of the field `key` on a JSON object line: the characters after
`"key":` up to the next `,` or `}`, with spaces removed. -/
def fieldChars (line key : List Char) : Option (List Char) :=
  (findAfter ('"' :: (key ++ ['"', ':'])) line).map
    (fun r => (r.takeWhile (fun c => c != ',' && c != '}')).filter (fun c => c != ' '))

/-- One emitted line: the parity label with its Ritz value and assembled width. -/
structure SectorRecord where
  /-- The parity label, `even` or `odd` (quotes stripped). -/
  sector : List Char
  /-- The delivered sector Ritz value `θ`. -/
  theta : Decimal
  /-- The assembled certified width `δ = residual + roundoff + enclosure`. -/
  delta : Decimal
deriving DecidableEq, Repr

/-- Parse one emitted line.  A negative width is rejected: a certificate may not widen
a bound by asserting a negative uncertainty. -/
def parseSectorLine (line : List Char) : Option SectorRecord := do
  let lab ← fieldChars line "sector".toList
  let th ← fieldChars line "theta".toList
  let de ← fieldChars line "delta".toList
  let theta ← parseDec th
  let delta ← parseDec de
  if 0 ≤ delta.mant then
    some ⟨lab.filter (fun c => c != '"'), theta, delta⟩
  else
    none

/-- Split text into lines. -/
def splitLines : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
      let r := splitLines cs
      if c == '\n' then [] :: r
      else
        match r with
        | [] => [[c]]
        | h :: t => (c :: h) :: t

/-- The two sector records a certificate delivers. -/
structure CertificateData where
  /-- The even-sector record. -/
  even : SectorRecord
  /-- The odd-sector record. -/
  odd : SectorRecord
deriving DecidableEq, Repr

/-- **The reader.**  Parse an emitted NDJSON certificate: every line that is a
well-formed sector record is read, and the `even` and `odd` records are selected.  Lines
that are not sector records (a header line, a trailing newline) are ignored. -/
def parseCertificate (s : String) : Option CertificateData := do
  let recs := (splitLines s.toList).filterMap parseSectorLine
  let e ← recs.find? (fun r => r.sector == "even".toList)
  let o ← recs.find? (fun r => r.sector == "odd".toList)
  some ⟨e, o⟩

/-- The measured sector Ritz difference `θᵒ − θᵉ` carried by parsed data. -/
def CertificateData.gapQ (d : CertificateData) : ℚ := d.odd.theta.toQ - d.even.theta.toQ

/-- The assembled certified width `δᵒ + δᵉ` carried by parsed data. -/
def CertificateData.widthQ (d : CertificateData) : ℚ := d.odd.delta.toQ + d.even.delta.toQ

/-- The certified lower bound `θᵒ − θᵉ − (δᵒ + δᵉ)` carried by parsed data. -/
def CertificateData.lowerQ (d : CertificateData) : ℚ := d.gapQ - d.widthQ

/-- The certified lower bound read off an emitted NDJSON certificate. -/
def ndjsonLower (s : String) : Option ℚ := (parseCertificate s).map CertificateData.lowerQ

/-! ## 3. The bridge to the T6 certificate structure -/

/-- Parsed data as a `GapCertificate` of `ChapterSirkCertifiedGap`; a negative assembled
width is refused rather than trusted. -/
noncomputable def CertificateData.toGapCertificate (d : CertificateData) :
    Option GapCertificate :=
  if h : (0 : ℝ) ≤ ((d.widthQ : ℚ) : ℝ) then
    some { gap := ((d.gapQ : ℚ) : ℝ), width := ((d.widthQ : ℚ) : ℝ), width_nonneg := h }
  else
    none



section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]





end Operator

/-! ## 4. The wire format worked through

The two numbers that are *data* — transcribed from the historical `g = 2`, `m = 4`
run of the lattice-era cross-benchmark recorded in `MASS_GAP_CERTIFIED.md` (the
mass-gap object of record is the 3D gauge-fixed nested-Fock QYM Hamiltonian;
the abstract T6 consumes certificates from either identically) — are the measured sector gap
`θᵒ − θᵉ = 1.9875` and the assembled width `δᵒ + δᵉ = 0.0555`.  The record keeps only
those two aggregates, so the *split* of each aggregate between the two sectors in the
example line pair below is an illustration of the wire format, not transcribed data;
the theorems consume only the aggregates, which the example reproduces exactly. -/

/-- An emitted certificate in the wire format.  Only the aggregates `θᵒ − θᵉ = 1.9875`
and `δᵒ + δᵉ = 0.0555` are transcribed data; the per-sector split shown here illustrates
the format. -/
def formatExampleNdjson : String :=
  "{\"sector\":\"even\",\"theta\":0.0000,\"delta\":0.0255}\n" ++
  "{\"sector\":\"odd\",\"theta\":1.9875,\"delta\":0.0300}\n"

/-- The parsed contents of the example certificate. -/
def formatExampleData : CertificateData :=
  ⟨⟨"even".toList, ⟨0, 4⟩, ⟨255, 4⟩⟩, ⟨"odd".toList, ⟨19875, 4⟩, ⟨300, 4⟩⟩⟩













end BookProof.SirkCertificateReader


