-- Prove2me | Definitions.Def_LinfContractionFP_roundsBound
-- name    : LinfContractionFP_roundsBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:21.047246+00:00
-- url     : https://prove2.me/theorems/e976253c-db9d-4065-bec4-1de8ac602c5e
-- title:
--   $U_d(a)$: one plus the Lemma 5 bound on boosting rounds of Label
-- statement:
--   For a dimension $d$ and an amplification ratio $a$, with $k=1+\lceil\log_{4/3}(4d^2)\rceil$ and $h=\lceil\log_2 a\rceil$,
--   $$U_d(a)=1+130^k\binom{h+k}{k}.$$
--   This is one plus the bound of Lemma 5 on the boosting rounds of $\mathrm{Amplify}(0,2\tau,0,n,n)$ with $n=2d$, so $B_+B_-=4d^2$; it enters the recurrence of the proof of Theorem 1.
--
--   **Formalization Note** The ceilings are natural-number ceilings ($0$ for a nonpositive logarithm).
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), proof of Theorem 1, p.21; Lemma 5, (15), p.20

import Mathlib

namespace LinfContractionFP

/-- `U_d(a)`, one plus the bound of Lemma 5 on the number of boosting rounds of one call of
Label in dimension `d` at amplification ratio `a`: with `n = 2d` and `B₊ = B₋ = n` (Algorithm 4),
`k = 1 + ⌈log_{4/3}(4d²)⌉` and `h = ⌈log₂ a⌉`,
`U_d(a) = 1 + 130^k · C(h + k, k)`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), proof of Theorem 1, p.21
("where U_d(a) bounds one plus the number of boosting rounds") and Lemma 5, display (15), p.20
("N := 130^k C(h+k, k) [...] where k = 1 + ⌈log_{4/3}(B+B−)⌉ and h = ⌈log₂(τ/ρ)⌉").

**Formalization Note.** `B₊B₋ = (2d)² = 4d²`; the ceilings are `Nat.ceil` of `Real.logb`
(`0` for a nonpositive logarithm). -/
noncomputable def roundsBound (d : ℕ) (a : ℝ) : ℝ :=
  let k := 1 + Nat.ceil (Real.logb (4 / 3) (4 * (d : ℝ) ^ 2))
  let h := Nat.ceil (Real.logb 2 a)
  1 + (130 : ℝ) ^ k * ((h + k).choose k : ℝ)

end LinfContractionFP


