-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_hiddenPairMeasure
-- name    : RandPurIso_Completion_Supplement_hiddenPairMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:49:57.044205+00:00
-- url     : https://prove2.me/theorems/64236c53-592f-43f4-92c3-e98d3f173912
-- title:
--   The law of the hidden pairs: $L$ independent Haar unitaries on $\mathbb C^d$
-- statement:
--   For each $x\in[L]$ independently, draw a Haar-random unitary $U_x$ on $\mathbb C^d$; its first two columns are the ordered orthonormal pair $|\phi_{x,0}\rangle,|\phi_{x,1}\rangle$ ("hidden pair"). The law of $(U_x)_{x\in[L]}$ is the product
--
--   $$
--   \mu_{L,d}=\bigotimes_{x\in[L]}\mathrm{Haar}\big(\mathrm U(d)\big).
--   $$
--
--   The module also records that the Haar measure on $\mathrm U(d)$ is a probability measure. The SAME and DIFF ensembles of §7 are the channels built from hidden pairs drawn from $\mu_{L,d}$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §7, p. 49

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
open MeasureTheory

namespace RandPurIso.Completion.Supplement

/-- The Haar measure `QAlgorithms.Schur.unitaryHaar d` is a probability measure (it is normalized on
the whole compact group `U(d)`). Needed to form product measures of independent Haar samples. -/
instance unitaryHaar_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

/-- **The law of the hidden pairs** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7, p. 49): for each `x ∈ [L]` independently, a
Haar-random unitary `U_x` on `ℂ^d`, whose first two columns are the ordered orthonormal pair
`|φ_{x,0}⟩, |φ_{x,1}⟩`. The product of `L` independent Haar measures on `U(d)`. -/
noncomputable abbrev hiddenPairMeasure (L d : ℕ) : Measure (Fin L → Matrix.unitaryGroup (Fin d) ℂ) :=
  Measure.pi fun _ : Fin L => QAlgorithms.Schur.unitaryHaar d

end RandPurIso.Completion.Supplement


