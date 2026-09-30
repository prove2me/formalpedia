-- Prove2me | Definitions.Def_SP4RankNine
-- name    : SP4RankNine
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T01:59:52.733551+00:00
-- url     : https://prove2.me/theorems/eda2a359-5fb9-4abf-87fd-d993e01aaf94
-- title:
--   Graded cancellation pairings and symmetric eight-atom profiles
-- statement:
--   A **graded cancellation pairing** is defined on an arbitrary set of atoms $\alpha$, integer-valued filtration and degree functions
--   $$
--   A,M:\alpha\longrightarrow\mathbb Z,
--   $$
--   an involutive bijection $p:\alpha\to\alpha$, and a Boolean source marker $s$. Partners have opposite source markers:
--   $$
--   p(p(i))=i,\qquad s(p(i))=\neg s(i).
--   $$
--   Every marked source has strictly higher filtration and degree exactly one above its target:
--   $$
--   s(i)=\mathrm{true}\Longrightarrow A(p(i))<A(i),
--   $$
--   $$
--   s(i)=\mathrm{true}\Longrightarrow M(i)=M(p(i))+1.
--   $$
--   Thus every atom belongs to exactly one oriented cancellation pair; this is actual pairing data, not an assumed numerical balance.
--
--   The bundled profiles use the eight atoms indexed by $0,\ldots,7$. For arbitrary integers $g,h,a,b,c,d$, the five-level profile is:
--
--   | Indices | Filtration values | Integer degrees |
--   | --- | --- | --- |
--   | $0,1$ | $g,g$ | $a,b$ |
--   | $2,3$ | $h,h$ | $c,d$ |
--   | $4,5$ | $-h,-h$ | $c-2h,d-2h$ |
--   | $6,7$ | $-g,-g$ | $a-2g,b-2g$ |
--
--   The other profile has four atoms at $g$, with degrees $a,b,c,d$, and four at $-g$, with degrees
--   $$
--   a-2g,\quad b-2g,\quad c-2g,\quad d-2g.
--   $$
--   The negative-level shifts encode the grading symmetry assumed by the motivating argument. Positivity and parity are hypotheses of the theorem, not restrictions imposed by these definitions.
--
--   These eight atoms model only the nonpermanent part of the motivating nine-generator profile. A central permanent generator is not encoded. No knot, homology theory, chain complex, realization, or geometric bridge is defined here.
-- source:
--   Unpublished project note, gt_e12_rank18_cube_attack.md, corrected current copy, §2.1–2.2 (lines 155–194); SHA-256 ac06bc38602b5eb920f798ed749c06e06f56430eb0151d213ca2650834ccb883. Companion historical audit: gt_e12_rank18_cube_independent_audit.md, §3 (lines 137–181); SHA-256 921889fb6acd8297b81e8662c2210573f668c08a880cd65c4da62f0c22b5b0e8. The audit records corrections to an older memo hash; the selected finite cancellation argument is present in the corrected current source. Newly authored Lean formalization of this finite argument, checked on Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. No public manuscript URL, authorship priority, or novelty claim is asserted.

import Mathlib

set_option autoImplicit false

/-!
# Finite graded cancellation data for the rank-nine arithmetic layer

This definition bundle describes finite graded pairings, not knot Floer
homology. The eight atoms are the acyclic part of the motivating nine-atom
profile; the central permanent atom is not part of the finite set below.
-/

namespace SP4RankNine

/-- Every atom has a unique partner. Sources strictly decrease filtration
and have integer degree exactly one above their targets. -/
structure CancellationPairing {α : Type*} (A M : α → ℤ) where
  mate : α ≃ α
  involutive : Function.Involutive mate
  source : α → Bool
  exchange : ∀ i, source (mate i) = !(source i)
  lower : ∀ i, source i = true → A (mate i) < A i
  degree : ∀ i, source i = true → M i = M (mate i) + 1

/-- The ordered filtration levels of the eight nonpermanent atoms in a
five-level profile, omitting the central permanent atom. -/
def fiveLevel (g h : ℤ) : Fin 8 → ℤ := ![g, g, h, h, -h, -h, -g, -g]

/-- The labels at negative filtration are shifted by twice that level,
as in the motivating conjugation relation. -/
def fiveMaslov (g h a b c d : ℤ) : Fin 8 → ℤ :=
  ![a, b, c, d, c - 2*h, d - 2*h, a - 2*g, b - 2*g]

/-- Four top and four bottom atoms, omitting the central permanent atom. -/
def fourFourLevel (g : ℤ) : Fin 8 → ℤ := ![g, g, g, g, -g, -g, -g, -g]

/-- The four negative-level labels are shifted from the positive-level
labels by twice the positive filtration height. -/
def fourFourMaslov (g a b c d : ℤ) : Fin 8 → ℤ :=
  ![a, b, c, d, a - 2*g, b - 2*g, c - 2*g, d - 2*g]

end SP4RankNine


