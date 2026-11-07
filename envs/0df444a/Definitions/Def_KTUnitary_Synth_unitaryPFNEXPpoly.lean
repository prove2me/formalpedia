-- Prove2me | Definitions.Def_KTUnitary_Synth_unitaryPFNEXPpoly
-- name    : KTUnitary_Synth_unitaryPFNEXPpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:37:18.784378+00:00
-- url     : https://prove2.me/theorems/234f71b5-3090-440f-8e0e-7fbfcb4dab13
-- title:
--   The class $\mathsf{unitaryP}^{\mathsf{FNEXP}^L[\mathrm{poly}]}$
-- statement:
--   $$\mathsf{unitaryP}^{\mathsf{FNEXP}^L[\mathrm{poly}]}=\bigcup_{R\in\mathsf{FNEXP}^L[\mathrm{poly}]}\mathsf{unitaryP}^R.$$
--   It is the second branch of the dichotomy of Lemma 7.4.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), §7.1 and Lemma 7.4, p. 34

import Mathlib
import Definitions.Def_KTUnitary_Synth_unitaryPRel
import Definitions.Def_KTUnitary_Synth_FNEXPpoly

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `unitaryP^{FNEXP^L[poly]}`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), §7.1 and Lemma 7.4, p. 34): "When `ℛ` is a
class of relations, `K^ℛ` is the union thereof, i.e. `K^ℛ := ⋃_{R ∈ ℛ} K^R`", here with
`ℛ = FNEXP^L[poly]` and `K = unitaryP`. -/
def unitaryPFNEXPpoly (L : Oracle) : Set ULang := ⋃ R ∈ FNEXPpoly L, unitaryPRel R

end KTUnitary.Synth


