-- Prove2me | Definitions.Def_BBPSSW_Distill_bxor
-- name    : BBPSSW_Distill_bxor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:26.374847+00:00
-- url     : https://prove2.me/theorems/b6ce89af-0fbe-41e1-974e-87b283fe45a7
-- title:
--   Bilateral XOR (BXOR) of two pairs
-- statement:
--   Alice holds spins 1 and 3 and Bob holds spins 2 and 4 of two shared pairs, the source pair (1, 2) and the target pair (3, 4). The bilateral XOR is
--
--   $$\mathrm{BXOR}=U_{XOR}^{(1\to3)}\otimes U_{XOR}^{(2\to4)}:$$
--
--   Alice applies $U_{XOR}$ with source 1 and target 3, Bob applies $U_{XOR}$ with source 2 and target 4. It flips spin 3 iff spin 1 is up and spin 4 iff spin 2 is up.
--
--   **Formalization Note** The two-pair index is ((spin 1, spin 2), (spin 3, spin 4)), source pair first; this is the index order of the Kronecker product $\rho_{\text{source}}\otimes\rho_{\text{target}}$.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered ("if Alice holds spins 1 and 3, and Bob holds spins 2 and 4, a BXOR …")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_uxor

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **The bilateral XOR (BXOR) on two pairs.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2: "The bilateral XOR (henceforth BXOR) operates in a similar fashion on corresponding
members of two pairs shared between Alice and Bob: if Alice holds spins 1 and 3, and Bob holds
spins 2 and 4, a BXOR, with spins 1 and 2 as source and spins 3 and 4 as target would
conditionally flip spin 3 if and only if spin 1 was up, while conditionally flipping spin 4 if
and only if spin 2 was up."

The index of a two-pair basis state is `((s₁, s₂), (s₃, s₄))`: the first component is the
source pair (spin 1 = Alice's, spin 2 = Bob's), the second the target pair (spin 3 = Alice's,
spin 4 = Bob's). The matrix entry is the product of Alice's `uxor` on (spin 1, spin 3) and
Bob's `uxor` on (spin 2, spin 4), i.e. BXOR = U_XOR(1→3) ⊗ U_XOR(2→4) after regrouping.

**Formalization Note.** The two-pair space is `QQ × QQ`, pair-major; this is the index order
of `Matrix.kronecker ρ_source ρ_target`. -/
def bxor : Matrix (QQ × QQ) (QQ × QQ) ℂ :=
  Matrix.of fun P Q => uxor (P.1.1, P.2.1) (Q.1.1, Q.2.1) * uxor (P.1.2, P.2.2) (Q.1.2, Q.2.2)

end BBPSSW.Distill


