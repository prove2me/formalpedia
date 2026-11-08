-- Prove2me | Definitions.Def_MantriCVQ_experimentInput
-- name    : MantriCVQ_experimentInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:42.471475+00:00
-- url     : https://prove2.me/theorems/8c3865dc-dcb8-4bba-9922-f8d47df3addc
-- title:
--   The auxiliary experiment of Claim 6.2
-- statement:
--   In the experiment of Claim 6.2, with the data tables $f$ fixed, every block $i$ of a set $I$ has the code table of its secret $\tau_i$ and the data table $f_i$, and all other leaves have fixed values. This is the input whose dependence on the secret tuple $\tau$ Claim 6.3 counts.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.2, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_MantriCVQ_Addr

open QAlgorithms.Complexity

namespace MantriCVQ

/-- The input of the experiment of Claim 6.2 (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33),
Claim 6.2, p. 24 (PDF p. 26)) with the data tables `f` fixed: every block `i` of `I` has the code table
of its secret `τ i` and the data table `f i`, and all other leaves have the fixed values `a`. -/
def experimentInput (C : (m : ℕ) → Bits m → Bits m → Bool) {K m : ℕ} (I : Finset (Fin K))
    (τ : I → Bits m) (f : Fin K → Bits m → Bool) (a : Fin K × Addr [m] → Bool) :
    Fin K × Addr [m] → Bool :=
  fun p =>
    if hi : p.1 ∈ I then
      if p.2.1 then f p.1 p.2.2.1 else C m (τ ⟨p.1, hi⟩) p.2.2.1
    else a p

end MantriCVQ


