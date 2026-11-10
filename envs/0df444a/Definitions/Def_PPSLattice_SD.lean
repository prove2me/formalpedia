-- Prove2me | Definitions.Def_PPSLattice_SD
-- name    : PPSLattice_SD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:10.609779+00:00
-- url     : https://prove2.me/theorems/62089522-464e-48c7-8eb1-f2623e40234a
-- title:
--   Statistical distance $\mathrm{SD}(X,Y)$
-- statement:
--   For laws $X,Y$ on a countable set $\Omega$,
--   $$\mathrm{SD}(X,Y)=\frac12\sum_{\alpha\in\Omega}\bigl|\Pr[\alpha\leftarrow X]-\Pr[\alpha\leftarrow Y]\bigr|.$$
--   Two ensembles are statistically indistinguishable when this is negligible in $\lambda$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The **statistical distance** `SD(X, Y) = ½ Σ_α |Pr[α ← X] − Pr[α ← Y]|` of two laws on a
countable set.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15 ("SD(X_λ, Y_λ) = ½ Σ_{α∈Ω} |Pr[α ← X_λ] − Pr[α ← Y_λ]|").

**Formalization Note.** Probabilities are `PMF` values in `ℝ≥0∞`, converted with `toReal` (they
are at most `1`); the sum is a `tsum`, which converges because the summands are bounded by
`p α + p′ α`. -/
noncomputable def SD {α : Type} (p p' : PMF α) : ℝ :=
  (1 / 2) * ∑' a, |(p a).toReal - (p' a).toReal|

end PPSLattice


