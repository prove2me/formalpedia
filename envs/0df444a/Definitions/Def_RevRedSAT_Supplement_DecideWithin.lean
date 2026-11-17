-- Prove2me | Definitions.Def_RevRedSAT_Supplement_DecideWithin
-- name    : RevRedSAT_Supplement_DecideWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:54:10.044204+00:00
-- url     : https://prove2.me/theorems/c90464ac-d330-4fb9-9a3e-0dafd720d290
-- title:
--   Deterministic decision algorithms within a time bound
-- statement:
--   Let a problem have instances $I$, a set of admissible input words (codes) for each instance, and a set of YES-instances. A machine $M$ **decides the problem within** a time bound $T(I,w)$ if, on every code $w$ of every instance $I$, it halts within $T(I,w)$ steps with the one-bit output $[b]$, where $b$ is true exactly when $I$ is a YES-instance.
--
--   This is the paper's notion of a decision algorithm (App. C, p.92: "A decision algorithm determines whether a feasible solution exists"). It is used for the coloring problems of Theorem 1.4, for MaxSAT in Theorem 10.1, and for the premises and the conclusion of Theorems 5.5 and 6.18.
--
--   **Formalization Note** The run is `HMBinPacking.OutputsWithin`, Mathlib's `TM2OutputsInTime`. Every code of an instance is admissible, so the bound holds for every listing order.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C, p.92 (decision algorithms)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **A deterministic decision algorithm within a time bound.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C, p.92: "A decision algorithm determines whether a feasible solution exists."

For a problem whose instances `I` have codes `IsCode I w` and YES-instances `yes I`, the machine
`M` decides the problem within `T`: on every code `w` of every instance `I` it halts within
`T I w` steps with output `[b]`, where `b = true` exactly when `I` is a YES-instance. Every code
of an instance is an admissible input. -/
def DecideWithin {ι : Type} (M : Turing.TM2ComputableAux Bool Bool)
    (IsCode : ι → List Bool → Prop) (yes : ι → Prop) (T : ι → List Bool → ℕ) : Prop :=
  ∀ I w, IsCode I w → ∃ b : Bool, (b = true ↔ yes I) ∧ HMBinPacking.OutputsWithin M w [b] (T I w)

end RevRedSAT.Supplement


