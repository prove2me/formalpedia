-- Prove2me | Definitions.Def_SVFAppt_DilationChain
-- name    : SVFAppt_DilationChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:04.930618+00:00
-- url     : https://prove2.me/theorems/1e03b1d5-0437-4b2b-acd4-8291c26e2721
-- title:
--   Assumption 2.4 (dilation ordering): $B_1\le_{\mathrm{dil}}B_2\le_{\mathrm{dil}}\cdots\le_{\mathrm{dil}}B_n$
-- statement:
--   The service times $B_1,\dots,B_n$, all defined on one probability space, satisfy the **dilation ordering assumption** if
--
--   $$B_1\le_{\mathrm{dil}}B_2\le_{\mathrm{dil}}\cdots\le_{\mathrm{dil}}B_n,$$
--
--   each consecutive pair being ordered in the dilation order. Under this numbering the variances (when finite) are nondecreasing, so the smallest-variance-first sequence is the identity.
--
--   **Formalization Note** Patients are 0-based; the chain is stated for consecutive pairs only, as printed.
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, Assumption 2.4, p. 11

import Mathlib
import Definitions.Def_SVFAppt_DilationOrder

open MeasureTheory

namespace SVFAppt

/-- **Assumption 2.4 (dilation ordering): `B1 ⩽dil B2 ⩽dil … ⩽dil Bn`.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, Assumption 2.4, p. 11: "We have
B1 ⩽dil B2 ⩽dil . . . ⩽dil Bn."

`DilationChain P B` says that each service time is smaller in the dilation order than the next
one, all on the same probability space `(Ω, P)`.

**Formalization Note** Patients are 0-based (`Fin n`), so the chain reads
`B 0 ⩽dil B 1 ⩽dil … ⩽dil B (n−1)`, consecutive pairs only, as printed. Under this numbering the
smallest-variance-first sequence is the identity permutation. -/
def DilationChain {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (B : Fin n → Ω → ℝ) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), DilationOrder P P (B i) (B ⟨i.val + 1, h⟩)

end SVFAppt


