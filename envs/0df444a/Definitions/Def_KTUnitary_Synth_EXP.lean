-- Prove2me | Definitions.Def_KTUnitary_Synth_EXP
-- name    : KTUnitary_Synth_EXP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:25.573987+00:00
-- url     : https://prove2.me/theorems/dafc01b1-a628-4de3-ae22-41a2af096d3b
-- title:
--   The class $\mathsf{EXP}^L$
-- statement:
--   A language $A$ is in $\mathsf{EXP}^L$ if a deterministic $L$-oracle Turing machine decides it within $2^{p(|x|)}$ steps for some polynomial $p$.
--
--   It is the class in which the easy witness lemma (Lemma 7.7) places witness oracles.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, p. 37 (standard definition)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

open Classical in
/-- **The class `EXP^L`** (used in Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, p. 37; standard definition): a language `A`
is in `EXP^L` if some deterministic `L`-oracle machine `M` and polynomial `p` are such that for
every `x`, `M^L(x)` halts within `2^{p(|x|)}` steps and accepts exactly when `x ∈ A`. -/
def EXP (L : Oracle) : Set (Set Str) :=
  {A | ∃ (M : OTM) (p : Polynomial ℕ), ∀ x : Str,
    M.result L x (2 ^ p.eval x.length) = some (decide (x ∈ A))}

end KTUnitary.Synth


