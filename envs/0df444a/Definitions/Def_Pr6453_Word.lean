-- Prove2me | Definitions.Def_Pr6453_Word
-- name    : Pr6453_Word
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T18:19:56.437204+00:00
-- url     : https://prove2.me/theorems/1c4e6fc2-0342-4f80-8917-f0ccf729f74b
-- title:
--   PR #6453: the word and the native maps
-- statement:
--   The word layer of PR #6453: the word of the accumulated-block-composition schema, and the native maps it is built from.
--
--   The word is a straight-line program over columns: 770 public inputs, 104 ports, 1095 column frames, 104 live columns, 29 owned fields, and a program of 17 926 events tagged `INIT` (45), `MOVE` (3458), `SCALE` (854), `ADD` (13524) and `CLEAR` (45).
--
--   A *native map* is one of the elementary linear maps the native development provides, which the word calls through `LOCAL` events. The certificate records them by count and by the rank of the helper that performs them: 2 941 distinct maps, 1 124 helper normalizers and 208 main adapters, with the helper histogram by rank 1:14, 2:8, 3:4, 4:107, 5:15, 6:3, 7:9, 8:39, 9:363 — 562 helpers. The individual maps (which pair of roles each acts on, with which coefficient) are not in the certificate; they live in the native source, and a full formalisation must take them from there. This bundle fixes the shape a map has and the counts it must satisfy.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: research/p104-third-anchor-clean-mixed-root/WORD.json (schema p104-accumulated-block-composition/2) and RESULT.json (native, physical).

/-
# PR #6453: the word layer

The word of the accumulated-block-composition schema (`WORD.json` of
`research/p104-third-anchor-clean-mixed-root`, 466 KB, schema
`p104-accumulated-block-composition/2`), and the notion of a *native map* that it is built from.

## The word

The word is a straight-line program over columns. It records

* the public inputs (`770` of them),
* the ports (`104`),
* the frame map: for each of the `1095` columns the list of frames at which it is live,
* the live set (`104` columns) and the owned-field count (`29`),
* the program: `17 926` events with tags `INIT` (45), `MOVE` (3458), `SCALE` (854), `ADD` (13524)
  and `CLEAR` (45).

The blocks are read off by the pricing engine (`pricing.py → assemble`), which is why the word enters
the arithmetic through its event census and its diagonal; both are already formalised in
`Pr6453.invoice`.

## The native maps

A *native map* is one of the elementary linear maps the native development provides; the word calls
them through `LOCAL` events. The certificate records them by count and by the rank of the helper
that performs them:

* `2 941` distinct native maps,
* `1 124` helper normalizers and `208` main adapters,
* the helper histogram by rank, `1:14, 2:8, 3:4, 4:107, 5:15, 6:3, 7:9, 8:39, 9:363` (562 helpers).

What the certificate does *not* carry is the individual maps — which pair of roles each one acts on,
and with which coefficient. Those live in the native source, and a full formalisation has to take
them from there; this file fixes the shape a map must have and the counts it must satisfy.
-/
import Definitions.Def_Pr6453_RankMoments

namespace Pr6453

noncomputable section

/-! ## The word -/

/-- The five event tags of the word. -/
inductive EventTag : Type
  | INIT
  | MOVE
  | SCALE
  | ADD
  | CLEAR
  deriving DecidableEq, Repr

/-- The word: its public inputs, ports, frames, live set, owned fields and program. -/
structure Word where
  /-- number of public inputs, 770 -/
  publicInputs : ℕ
  /-- the ports (columns an event may reach from outside), 104 -/
  ports : List ℕ
  /-- the frame map: column index to the frames at which it is live, 1095 entries -/
  frames : List (List ℕ)
  /-- the live columns, 104 -/
  live : List ℕ
  /-- the owned fields, 29 -/
  ownedFields : ℕ
  /-- the program: the tags of the 17 926 events -/
  program : List EventTag
  deriving Repr

/-- The event census of `WORD.json`. -/
def census : List (EventTag × ℕ) :=
  [(EventTag.INIT, 45), (EventTag.MOVE, 3458), (EventTag.SCALE, 854), (EventTag.ADD, 13524), (EventTag.CLEAR, 45)]

/-! ## The native maps -/

/-- A native map: an elementary linear map acting on the rows of a helper. The certificate fixes the
rank (how many rows it touches) and the number of maps at that rank; the source role and target role
are what a formalisation of the native development has to supply. -/
structure NativeMap where
  /-- the rank of the helper that performs the map -/
  rank : ℕ
  /-- the source role -/
  source : ℕ
  /-- the target role -/
  target : ℕ

/-- The helper histogram by rank, `RESULT.json → native.helpers`. -/
def helperHistogram : List (ℕ × ℕ) :=
  [(1, 14), (2, 8), (3, 4), (4, 107), (5, 15), (6, 3), (7, 9), (8, 39), (9, 363)]

/-- The native receipt: distinct maps, helper normalizers, main adapters
(`RESULT.json → native`). -/
def nativeReceipt : ℕ × ℕ × ℕ := (2941, 1124, 208)

/-- The physical receipt: `799` columns, `7 488` physical contacts, `53 248` central square columns,
`18` full calls, `104` ports (`RESULT.json → physical`). -/
def physicalReceipt : ℕ × ℕ × ℕ × ℕ := (799, 7488, 53248, 18)

end
end Pr6453


