-- Prove2me | Definitions.Def_WardInvariant
-- name    : WardInvariant
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:51.897203+00:00
-- url     : https://prove2.me/theorems/40f7cc6b-1bf8-4d9c-b236-67ef8d7cc8f4
-- title:
--   The single-index Ward invariant
-- statement:
--   Using the conserved numerator and denominator, the file defines the predicate $$cN_n=(d+b^4)D_n.$$ This is the $s=1$ form of the Ward or van der Poorten–Swart invariant, equivalently asserting that $N_n/D_n$ is independent of $n$ when division is legitimate. It is the invariant relation used to derive the general elliptic divisibility sequence laws.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardConservation
/-!
# Single-index invariant for `normEDS`  (Ward / van der Poorten–Swart conserved quantity)

`c · N_n = (d + b⁴) · D_n` for all `n`, where `N_n`, `D_n` are `Nseq`, `Dseq` (the Somos-4
numerator / denominator). Equivalently `N_n / D_n` is the index-independent conserved quantity
`λ = (d+b⁴)/c` — this is the `s = 1` case of the general-`s` invariant
(`invarNum s n / invarDenom s n` in Mathlib PR #13155, alreadydone; van der Poorten–Swart Thm 3).

**Scope note (deliberate, see WARD_FULL_DOCTRINE.md):** we prove only the `s = 1` invariant, which
is exactly what the `AddRel`/`OffRel` gap induction needs to reach the *fully general*
`IsEllSequence (normEDS)`. The general-`s` form (PR #13155) is intermediate-lemma generality, not a
stronger theorem; if a future need arises it can be generalized here. Source of the approach:
van der Poorten–Swart Theorem 3; cf. Mathlib PR #13155 (alreadydone / Junyan Xu). The code is ours.

Proof: it is a polynomial identity in `(b,c,d)`, proved over the universal domain (where `D_n` is a
non-zero-divisor for `n ≥ 2`) by induction off the conserved ratio (`normEDS_conservation`), then it
holds over every `CommRing` since both sides are the same `(b,c,d)`-polynomial.
-/

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The `s = 1` invariant relation `c · N_n = (d + b⁴) · D_n`. -/
@[expose] public def InvarRel (b c d : R) (n : ℤ) : Prop :=
  c * Nseq b c d n = (d + b ^ 4) * Dseq b c d n

end FLT.EDS


