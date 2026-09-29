-- Prove2me | Definitions.Def_ChapterH4
-- name    : ChapterH4
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:40:36.00885+00:00
-- url     : https://prove2.me/theorems/997d21a3-cc07-455c-871a-1cbd446cab20
-- title:
--   This file closes the remaining deliverables of the Hashimoto–Nodera *Shift-invert Rational Krylov (SIRK)* package (sourc ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.H4`, source chapter `BookProof/ChapterH4.lean`).
--
--   This file closes the remaining deliverables of the Hashimoto–Nodera *Shift-invert Rational Krylov (SIRK)* package (source `RiemannProof/Hashimoto.md`), building on `ChapterH1.lean` (φ-functions, resolvent shift identity) and `ChapterH2.lean` (Arnoldi/Krylov Hessenberg compression).
--
--   * **H1.5 — the operator φ-function via the resolvent (Definition 2.4), scalar core.** `psi k γ w := phi k (γ − w⁻¹)` is the function whose functional calculus at the resolvent `X = (γ − A)⁻¹` *defines* `φ_k(A)`. The spectral consistency of that definition is the scalar identity `psi_shift_eq_phi : psi k γ ((γ − z)⁻¹) = phi k z` (for `γ − z ≠ 0`): under the shift-invert change of variable `w = (γ − z)⁻¹` one has `γ − w⁻¹ = z`, so `ψ_{k,γ}` evaluated at the shift-invert image of `z` returns `φ_k(z)`.
--
--   * **H2.2 — the SIRK compression and the rational-function transfer (eq. 10).** For an isometric embedding `V : F →L E` (`V∗V = 1`) whose range is invariant under a bounded operator `X`, the *compression* `B := V∗ X V : F →L F` is exactly the paper's `Hₘ Kₘ⁻¹` (eq. 10 is literally this definition), and it satisfies the transfer identities `Xⁿ ∘ V = V ∘ Bⁿ` (`compress_pow`), `Xⁿ v = V (Bⁿ (V∗ v))` on the range of `V` (`compress_transfer`), and the invertible-factor transfer `q(X)⁻¹ ∘ V = V ∘ q(B)⁻¹` (`compress_inv_transfer`). Together these give the load-bearing identity `r(Xₘ) v = Vₘ r(Hₘ Kₘ⁻¹) Vₘ∗ v` used in Theorem 4.1.
--
--   * **H2.3 — the SIRK convergence headline (Theorem 4.1), CONDITIONAL.** The two genuinely deep analytic inputs — Crouzeix's inequality (Crouzeix 2007, Crouzeix–Palencia) and the deferred `e^{−hm}` deformation of the last step of the source Theorem 5 [10] — are **named hypotheses with citation docstrings, never axioms**. Given them, the triangle-inequality core `sirk_error_bound` proves `‖φ_k(A)v − Vₘ ψ(HₘKₘ⁻¹) Vₘ∗ v‖ ≤ 2C‖v‖·‖ψ−r‖`, and `sirk_error_bound_decay` assembles the eq.-(12) form with the `e^{−hm}` decay.
--
--   * **H2.4 — the existing-methods comparison (Remark 4.2), CONDITIONAL.** `sia_error_bound` is the analogous SIA bound (15) and `sirk_le_sia` records the `e^{−hm}` advantage of SIRK over SIA as an inequality of the two bounds.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`). The only non-proved inputs are the **named** `Crouzeix`/decay hypotheses of H2.3/H2.4 — by design (the `IsSchurFull`/`EXTERNAL` pattern), never `axiom`s.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH4.lean

import Definitions.Def_ChapterH1

import Mathlib

/-!
# Chapter H4 — Hashimoto SIRK: operator φ-function core, compression transfer,
and the conditional convergence headline (roadmap N13, §0 S7)

This file closes the remaining deliverables of the Hashimoto–Nodera
*Shift-invert Rational Krylov (SIRK)* package (source `RiemannProof/Hashimoto.md`),
building on `ChapterH1.lean` (φ-functions, resolvent shift identity) and
`ChapterH2.lean` (Arnoldi/Krylov Hessenberg compression).

## Deliverables (this file)

* **H1.5 — the operator φ-function via the resolvent (Definition 2.4), scalar
  core.** `psi k γ w := phi k (γ − w⁻¹)` is the function whose functional
  calculus at the resolvent `X = (γ − A)⁻¹` *defines* `φ_k(A)`.  The spectral
  consistency of that definition is the scalar identity
  `psi_shift_eq_phi : psi k γ ((γ − z)⁻¹) = phi k z` (for `γ − z ≠ 0`): under the
  shift-invert change of variable `w = (γ − z)⁻¹` one has `γ − w⁻¹ = z`, so
  `ψ_{k,γ}` evaluated at the shift-invert image of `z` returns `φ_k(z)`.

* **H2.2 — the SIRK compression and the rational-function transfer (eq. 10).**
  For an isometric embedding `V : F →L E` (`V∗V = 1`) whose range is invariant
  under a bounded operator `X`, the *compression* `B := V∗ X V : F →L F` is
  exactly the paper's `Hₘ Kₘ⁻¹` (eq. 10 is literally this definition), and it
  satisfies the transfer identities `Xⁿ ∘ V = V ∘ Bⁿ`
  (`compress_pow`), `Xⁿ v = V (Bⁿ (V∗ v))` on the range of `V`
  (`compress_transfer`), and the invertible-factor transfer
  `q(X)⁻¹ ∘ V = V ∘ q(B)⁻¹` (`compress_inv_transfer`).  Together these give the
  load-bearing identity `r(Xₘ) v = Vₘ r(Hₘ Kₘ⁻¹) Vₘ∗ v` used in Theorem 4.1.

* **H2.3 — the SIRK convergence headline (Theorem 4.1), CONDITIONAL.**  The two
  genuinely deep analytic inputs — Crouzeix's inequality (Crouzeix 2007,
  Crouzeix–Palencia) and the deferred `e^{−hm}` deformation of the last step of
  the source Theorem 5 [10] — are **named hypotheses with citation docstrings,
  never axioms**.  Given them, the triangle-inequality core `sirk_error_bound`
  proves `‖φ_k(A)v − Vₘ ψ(HₘKₘ⁻¹) Vₘ∗ v‖ ≤ 2C‖v‖·‖ψ−r‖`, and
  `sirk_error_bound_decay` assembles the eq.-(12) form with the `e^{−hm}` decay.

* **H2.4 — the existing-methods comparison (Remark 4.2), CONDITIONAL.**
  `sia_error_bound` is the analogous SIA bound (15) and `sirk_le_sia` records
  the `e^{−hm}` advantage of SIRK over SIA as an inequality of the two bounds.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).  The only non-proved inputs are the **named** `Crouzeix`/decay
hypotheses of H2.3/H2.4 — by design (the `IsSchurFull`/`EXTERNAL` pattern), never
`axiom`s.
-/

open scoped BigOperators

namespace BookProof.ChapterH4

noncomputable section

/-! ## H1.5 — the operator φ-function via the resolvent (scalar core) -/

/-- **H1.5** (Definition 2.4, scalar function): `ψ_{k,γ}(w) := φ_k(γ − w⁻¹)`.  Its
functional calculus at the resolvent `X = (γ − A)⁻¹` is the Taylor (1951) /
Güttel (2010) definition of the operator φ-function `φ_k(A)`. -/
def psi (k : ℕ) (γ w : ℂ) : ℂ := BookProof.ChapterH1.phi k (γ - w⁻¹)

/-
**H1.5** (spectral consistency of Definition 2.4): under the shift-invert
change of variable `w = (γ − z)⁻¹` one has `γ − w⁻¹ = z`, hence
`ψ_{k,γ}((γ − z)⁻¹) = φ_k(z)`.  This is why applying the functional calculus of
`ψ_{k,γ}` to `X = (γ − A)⁻¹` reproduces `φ_k(A)`.
-/


/-! ## H2.2 — the SIRK compression and rational-function transfer -/

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **SIRK compression** `B := V∗ X V` of an operator `X` to the finite
subspace embedded by the isometry `V`.  With `V = Vₘ` the orthonormal Krylov
basis and `X = Xₘ` the shift-invert resolvent, this is exactly the paper's
`Hₘ Kₘ⁻¹` (eq. 10). -/
def compress (V : F →L[ℂ] E) (X : E →L[ℂ] E) : F →L[ℂ] F :=
  V.adjoint.comp (X.comp V)

/-
**H2.2** (compression intertwines on the range): if `V∗V = 1` and the range
of `V` is `X`-invariant, then `X ∘ V = V ∘ B` for `B = V∗ X V`.
-/


/-
**H2.2** (power transfer): `Xⁿ ∘ V = V ∘ Bⁿ` for all `n`.
-/


/-
**H2.2** (pointwise power transfer on the range): for `v` in the range of `V`
(`V (V∗ v) = v`), `Xⁿ v = V (Bⁿ (V∗ v))`.
-/




/-! ## H2.3 — the SIRK convergence headline (Theorem 4.1), conditional -/

/-
**H2.3** (Theorem 4.1, triangle-inequality core — conditional on Crouzeix).
Abstract statement of the SIRK error bound.  Here:

* `phiA = ψ_{k,γₘ}(Xₘ) = φ_k(A)` is the target operator (`hphi`);
* `psiX, rX : E →L E` are `ψ_{k,γₘ}(Xₘ)` and `r(Xₘ)`;
* `psiB, rB : F →L F` are `ψ_{k,γₘ}(HₘKₘ⁻¹)` and `r(HₘKₘ⁻¹)`;
* `V = Vₘ` is the isometric Krylov embedding (`hViso`, `hVadj`);
* `hrt` is the H2.2 rational-transfer identity `r(Xₘ)v = Vₘ r(HₘKₘ⁻¹) Vₘ∗ v`;
* `hcx1, hcx2` are the two **Crouzeix** operator-norm bounds (eq. 14)
  `‖f(Xₘ)‖ ≤ C‖f‖_{∞,Σ}` — named hypotheses (Crouzeix 2007), **never axioms**.

The conclusion is eq. (13)→(14) of the proof:
`‖φ_k(A)v − Vₘ ψ(HₘKₘ⁻¹) Vₘ∗ v‖ ≤ 2C·D·‖v‖`, with `D = ‖ψ−r‖_{∞,Σ}`.
-/


/-
**H2.3** (Theorem 4.1, eq. 12 form — conditional).  Combining the Crouzeix
core `sirk_error_bound` with the deferred analytic deformation `hdecay`
(`D ≤ e^{−hm}·Dmin`, "the same deformation of the error bound with the last part
of the proof of Theorem 5 [10]", relating `‖ψ_{k,γₘ}−r‖` to
`e^{−hm}·‖f_{k,N}−r‖`) yields the headline exponential-decay bound
`≤ 2C·e^{−hm}·Dmin·‖v‖`.
-/


/-! ## H2.4 — the existing-methods comparison (Remark 4.2), conditional -/

/-
**H2.4** (Remark 4.2, SIA bound (15) — conditional on Crouzeix).  The SIA
approximation `Vₘ ψ_{k,γ}(Hₘ) Vₘ∗ v` obeys the same triangle-inequality bound as
SIRK but *without* the `e^{−hm}` factor: `‖φ_k(A)v − Vₘ ψ(Hₘ) Vₘ∗ v‖ ≤ 2C·Dsia·‖v‖`
with `Dsia = ‖ψ_{k,γ}−p‖_{∞,W((γI−A)⁻¹)}`.  (Same proof shape as
`sirk_error_bound`.)
-/


/-
**H2.4** (the `e^{−hm}` advantage of SIRK over SIA).  For `h, m ≥ 0` the SIRK
eq.-(12) bound is no larger than the corresponding SIA bound (with `Dmin` in the
role of `Dsia`), because `e^{−hm} ≤ 1`.  This is the inequality-of-bounds form of
Remark 4.2's conclusion that "the decay speed of the approximation error of SIRK
will be similar or smaller than that of SIA … due to the factor `e^{−hm}`".
-/


end

end BookProof.ChapterH4


