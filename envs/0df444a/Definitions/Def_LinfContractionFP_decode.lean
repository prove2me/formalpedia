-- Prove2me | Definitions.Def_LinfContractionFP_decode
-- name    : LinfContractionFP_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:33.249239+00:00
-- url     : https://prove2.me/theorems/6a474a3d-4e63-4a9c-a333-5205d29199c5
-- title:
--   The decoding rule (8)
-- statement:
--   Given tallies $F$ and budgets $B_\pm$, the **decoding rule** (8) sets
--   $$\ell_i=\begin{cases}+1 & \text{if } 3^{F_i}\ge B_-/B_+,\\ -1 & \text{otherwise.}\end{cases}$$
--   Amplify uses it for the labels it has not set directly (Algorithm 3, lines 2 and 19); Lemma 3 shows it is correct once $B_+B_-<1$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Lemma 3, (8), p.14

import Mathlib
import Definitions.Def_LinfContractionFP_Lbl

namespace LinfContractionFP

/-- The decoding rule (8): `ℓ_i = +1` if `3^{F_i} ≥ B₋/B₊`, and `−1` otherwise.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Lemma 3, display (8), p.14:
"consider the decoding rule for labels ℓ_i := +1 if 3^{F_i} ≥ B−/B+; −1 otherwise. (8)"

**Formalization Note.** `3^{F_i}` is the integer power `(3 : ℝ) ^ (F i)`; `+1` is `hi`, `−1`
is `lo`. -/
noncomputable def decode {κ : Type} (F : κ → ℤ) (Bp Bm : ℝ) : κ → Lbl := fun i =>
  if Bm / Bp ≤ (3 : ℝ) ^ (F i) then .hi else .lo

end LinfContractionFP


