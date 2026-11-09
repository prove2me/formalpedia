-- Prove2me | Definitions.Def_LinfContractionFP_Contract1
-- name    : LinfContractionFP_Contract1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:19.517199+00:00
-- url     : https://prove2.me/theorems/681dec6c-386e-4876-a28f-52fd7a094305
-- title:
--   Contract 1 of Amplify
-- statement:
--   A labeling $\ell$ satisfies **Contract 1** for $\mathrm{Amplify}(b,\tau,F,B_+,B_-)$ if
--   $$\Phi_+(F)\le B_+\ \Longrightarrow\ \ell_i=+1\ \ \forall i\in R_+,\qquad \Phi_-(F)\le B_-\ \Longrightarrow\ \ell_i=-1\ \ \forall i\in R_-,$$
--   with the bands and potentials of $\sigma+b$ at tolerance $\tau$. It is the inductive invariant of the correctness proof of Amplify (Theorem 3).
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Contract 1, pp.15–16

import Mathlib
import Definitions.Def_LinfContractionFP_Lbl
import Definitions.Def_LinfContractionFP_potentials

namespace LinfContractionFP

/-- Contract 1: a labeling `ℓ` returned by `Amplify(b, τ, F, B₊, B₋)` is valid on `R₊` when `B₊`
bounds `Φ₊(F)`, and on `R₋` when `B₋` bounds `Φ₋(F)`:
`Φ₊(F) ≤ B₊ ⟹ ℓ_i = +1 ∀ i ∈ R₊` and `Φ₋(F) ≤ B₋ ⟹ ℓ_i = −1 ∀ i ∈ R₋`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Contract 1, pp.15–16: "If
the quantity B± indeed bounds the potential Φ±, then the call to Amplify(b, τ, F, B+, B−)
returns valid labels ℓ_i for the coordinates in R±. More specifically, Φ+(F) ≤ B+ ⟹ ℓ_i = +1
∀i ∈ R+; Φ−(F) ≤ B− ⟹ ℓ_i = −1 ∀i ∈ R−."

**Formalization Note.** `+1` is `Lbl.hi`, `−1` is `Lbl.lo`. The bands and potentials are those
of `σ + b` at tolerance `τ` (`bandRplus`, `phiPlus`, …). -/
def Contract1 {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) (F : κ → ℤ) (Bp Bm : ℝ)
    (ℓ : κ → Lbl) : Prop :=
  (phiPlus σ b τ F ≤ Bp → ∀ i ∈ bandRplus σ b τ, ℓ i = .hi) ∧
    (phiMinus σ b τ F ≤ Bm → ∀ i ∈ bandRminus σ b τ, ℓ i = .lo)

end LinfContractionFP


