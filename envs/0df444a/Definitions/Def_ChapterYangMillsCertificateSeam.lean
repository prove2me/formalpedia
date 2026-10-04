-- Prove2me | Definitions.Def_ChapterYangMillsCertificateSeam
-- name    : ChapterYangMillsCertificateSeam
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T09:04:45.25639+00:00
-- url     : https://prove2.me/theorems/6876d005-bdeb-4e0f-adc7-decff045a031
-- title:
--   Chapter YangMillsCertificateSeam
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterYangMillsCertificateSeam.lean`): generated def bundle for ChapterYangMillsCertificateSeam. See BookProof/ChapterYangMillsCertificateSeam.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsCertificateSeam.lean

import Definitions.Def_ChapterSirkCertificateReader
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# Chapter YangMillsCertificateSeam — the certificate→theorem seam for the Yang–Mills gap

`CONSOLIDATED_PLAN.md` (2026-09-04f), QYM next step 2: *"the theorem that consumes
certified matrix-element data (emitted by `GapCertificate.lean` / the NDJSON fixture) and
discharges the Gershgorin tail + Schur coupling hypotheses, giving
`ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds` for the concrete
`qcd_ym_hamiltonian(g)` — never reading a displayed Ritz value as a lower bound."*

`BookProof.ChapterSchurGershgorinGap` already reduces the nested-Fock conclusion to
matrix-element inequalities, but it states them as five separate quantified hypotheses with
*independent* real parameters `mu`, `eps`, `d`, `r`.  A certificate does not emit five
parameters: it emits **one line of exact decimals**.  This chapter is the missing seam.

## What is and is not trusted

* **No floating-point value is trusted, and none is used.**  As in
  `BookProof.ChapterSirkCertificateReader`, a wire-format number is read as an exact
  `Decimal` (mantissa, power of ten), so its value is an exact rational.
* **No numerical claim is verified here.**  What the seam discharges is the *arithmetic*
  side of the criterion — `0 ≤ ε`, `ε < μ`, `μ ≤ dmin − rmax` — from the emitted decimals,
  by kernel-checkable rational arithmetic, and the bookkeeping that turns the two uniform
  tail numbers into the index-wise families `d`, `r` the lift consumes.  The *analytic*
  content — that the recorded numbers really do bound the matrix elements of the
  Yang–Mills Hamiltonian, and that the order-`m` truncation really does have the recorded
  level gap — stays as explicit enclosure hypotheses, exactly as T6/T8 do.  A displayed
  Ritz value is never read as a lower bound.
* Nothing here claims the physical Yang–Mills mass gap.

## Deliverables

* `MatrixBoundRecord`, `parseMatrixBoundLine`, `parseMatrixBounds` — the wire format for
  matrix-element data: `{"m":4,"mu":1.9320,"eps":0.0300,"dmin":2.0000,"rmax":0.0500}`.
* `MatrixBoundRecord.checkBounds`, `MatrixBoundRecord.Valid`, `valid_of_checkBounds` — the
  decidable arithmetic side conditions and their reading as propositions.
* **`ym_fock_gap_of_matrix_certificate`** — the quantitative seam: the certified level gap
  plus the uniform Gershgorin/Schur enclosures give the nested-Fock energy bound with the
  explicit constant `μ − ε`.
* **`ym_fock_mass_gap_of_matrix_certificate`** — the seam in the form the chain consumes:
  a positive-definite nested-Fock energy on the vacuum-orthogonal sector, with the
  Friedrichs extension and the annihilated vacuum.
* `exampleNdjson`, `example_parse`, `example_checkBounds`, `example_ym_fock_mass_gap` — the
  wire format worked through end to end on the recorded `g = 2`, `m = 4` band.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.YangMillsCertificateSeam

open BookProof.SirkCertificateReader
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore

/-! ## 1. The wire format of matrix-element data -/

/-- One emitted matrix-bound line: the truncation order `m`, the level gap `μ` certified on
the order-`m` truncation, the Schur bound `ε` on the coupling block, and the two uniform
Gershgorin numbers of the tail — a diagonal lower bound `dmin` and an off-diagonal row-sum
bound `rmax`. -/
structure MatrixBoundRecord where
  /-- The truncation order. -/
  m : ℕ
  /-- The level gap certified on the order-`m` truncation. -/
  mu : Decimal
  /-- The Schur bound on the coupling block. -/
  eps : Decimal
  /-- The uniform lower bound for the tail diagonal entries. -/
  dmin : Decimal
  /-- The uniform bound for the tail off-diagonal absolute row sums. -/
  rmax : Decimal
deriving DecidableEq, Repr

/-- The certified level gap as an exact rational. -/
def MatrixBoundRecord.muQ (c : MatrixBoundRecord) : ℚ := c.mu.toQ

/-- The Schur coupling bound as an exact rational. -/
def MatrixBoundRecord.epsQ (c : MatrixBoundRecord) : ℚ := c.eps.toQ

/-- The tail diagonal bound as an exact rational. -/
def MatrixBoundRecord.dminQ (c : MatrixBoundRecord) : ℚ := c.dmin.toQ

/-- The tail row-sum bound as an exact rational. -/
def MatrixBoundRecord.rmaxQ (c : MatrixBoundRecord) : ℚ := c.rmax.toQ

/-- The certified mass-gap constant `μ − ε` carried by a record. -/
def MatrixBoundRecord.lowerQ (c : MatrixBoundRecord) : ℚ := c.muQ - c.epsQ

/-- Parse one emitted matrix-bound line.  Every field the proof consumes is read; a line
missing one of them fails to parse (it is never defaulted). -/
def parseMatrixBoundLine (line : List Char) : Option MatrixBoundRecord := do
  let ms ← fieldChars line "m".toList
  let m ← parseNatDigits ms
  let mus ← fieldChars line "mu".toList
  let mu ← parseDec mus
  let epss ← fieldChars line "eps".toList
  let eps ← parseDec epss
  let dmins ← fieldChars line "dmin".toList
  let dmin ← parseDec dmins
  let rmaxs ← fieldChars line "rmax".toList
  let rmax ← parseDec rmaxs
  some ⟨m, mu, eps, dmin, rmax⟩

/-- **The reader.**  The first well-formed matrix-bound line of an emitted certificate;
lines that are not matrix-bound records are ignored. -/
def parseMatrixBounds (s : String) : Option MatrixBoundRecord :=
  ((splitLines s.toList).filterMap parseMatrixBoundLine).head?

/-! ## 2. The decidable arithmetic side conditions -/

/-- **The arithmetic check** a record must pass: a non-negative coupling bound, a coupling
bound strictly below the level gap, and tail diagonal dominance at least as strong as the
level gap. -/
def MatrixBoundRecord.checkBounds (c : MatrixBoundRecord) : Bool :=
  decide (0 ≤ c.epsQ) && decide (c.epsQ < c.muQ) && decide (c.muQ ≤ c.dminQ - c.rmaxQ)

/-- The same three conditions as propositions. -/
structure MatrixBoundRecord.Valid (c : MatrixBoundRecord) : Prop where
  /-- The coupling bound is non-negative. -/
  eps_nonneg : 0 ≤ c.epsQ
  /-- The coupling bound is strictly below the certified level gap. -/
  eps_lt_mu : c.epsQ < c.muQ
  /-- The tail is diagonally dominant at least down to the level gap. -/
  dominance : c.muQ ≤ c.dminQ - c.rmaxQ



/-! ## 3. The seam -/

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)





/-! ## 4. The wire format worked through

The transcribed datum of the recorded `g = 2`, `m = 4` run (`MASS_GAP_CERTIFIED.md`,
`GapCertificate.lean`) is the certified band `[1.932, 2.043]`, whose lower end is the level
gap `μ = 1.9320` of the order-`4` truncation.  The three remaining numbers of the line —
the Schur coupling bound and the two Gershgorin tail numbers — are **not** transcribed
data: they illustrate the wire format, and the theorems consume them only through the
enclosure hypotheses. -/

/-- An emitted matrix-bound certificate in the wire format.  Only `mu` is transcribed data;
the other three numbers illustrate the format. -/
def exampleNdjson : String :=
  "{\"m\":4,\"mu\":1.9320,\"eps\":0.0300,\"dmin\":2.0000,\"rmax\":0.0500}\n"

/-- The parsed contents of the example certificate. -/
def exampleRecord : MatrixBoundRecord :=
  ⟨4, ⟨19320, 4⟩, ⟨300, 4⟩, ⟨20000, 4⟩, ⟨500, 4⟩⟩











end BookProof.YangMillsCertificateSeam

end


