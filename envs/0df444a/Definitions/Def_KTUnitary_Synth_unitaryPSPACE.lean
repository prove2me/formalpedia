-- Prove2me | Definitions.Def_KTUnitary_Synth_unitaryPSPACE
-- name    : KTUnitary_Synth_unitaryPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:57.940185+00:00
-- url     : https://prove2.me/theorems/caecbc76-7dc8-465a-aae4-07e52ade3b3b
-- title:
--   The class $\mathsf{unitaryPSPACE}^{\mathcal O}$
-- statement:
--   Defined as $\mathsf{unitaryP}^{\mathcal O}$, but with a **space-uniform** family $\{C_{n,\varepsilon}\}$: the description may have length $2^{\mathrm{poly}(n,\log1/\varepsilon)}$, every gate has a polynomial-length description, and the description is computable in polynomial space. The number of qubits stays $n+\mathrm{poly}(n,\log1/\varepsilon)$, and some extension of $U_n$ must be $\varepsilon$-close to $C_{n,\varepsilon}$ in operator norm.
--
--   **Formalization Note** $\varepsilon=2^{-\lambda}$; space uniformity in the bit-query form of `SpaceUniform`.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.2 and 5.6, pp. 16, 18

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_IsExtension
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_SpaceUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `unitaryPSPACE^𝒪`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 5.2 and 5.6, pp. 16 and 18): defined as
`unitaryP^𝒪`, "but where `{C_{n,ε}}` is a space-uniform family".

Here: as `unitaryP 𝒪`, with the descriptions of `C n l` space-uniform in the parameter string
`tup [1^n, 1^l]`: the description has length at most `2^{p'}`, every gate description has length
at most `p'`, and its bits are decidable in polynomial space without oracle.

**Formalization Note** `ε = 2^{−l}` (footnote 4, p. 14); one FPTEAS encoding per family;
space uniformity by bit queries (see `SpaceUniform`), with polynomial-length gate descriptions
(footnote 5, p. 14). -/
def unitaryPSPACE (O : ULang) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    SpaceUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2]) (fun nl => (C nl.1 nl.2).code)
      (fun nl => (C nl.1 nl.2).gateCodes) ∧
    ∀ n l : ℕ, (C n l).Valid f ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∃ Ub, IsExtension h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
        opNorm (Ub - (C n l).unitary f O) ≤ (2 : ℝ)⁻¹ ^ l}

end KTUnitary.Synth


