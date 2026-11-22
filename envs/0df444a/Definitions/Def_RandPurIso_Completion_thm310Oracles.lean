-- Prove2me | Definitions.Def_RandPurIso_Completion_thm310Oracles
-- name    : RandPurIso_Completion_thm310Oracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:00.165122+00:00
-- url     : https://prove2.me/theorems/9d25dc2a-45d4-4111-b8f7-1a87a7a4bd2a
-- title:
--   The four oracles of Theorem 3.10
-- statement:
--   In the qubit model $A=\{0,1\}^a$, $A_{\mathrm{pure}}=\{0,1\}^p$, oracle $0$ is $M^{\Pi_1}$ ($\Pi_1$ on $A\otimes A_{\mathrm{pure}}$), oracle $1$ is $M^{\Pi_2}$ ($\Pi_2$ on $A$), oracles $2$ and $3$ are $\Phi^{\mathrm{ctrl}[V_1]}$ and $\Phi^{\mathrm{ctrl}[V_2]}$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 3.10, p. 19

import Mathlib
import Definitions.Def_RandPurIso_Completion_isoQuery
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- Register widths of the four oracles of Theorem 3.10 (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 19): `M^{Π1}`, `M^{Π2}`,
`Φ^{ctrl[V1]}`, `Φ^{ctrl[V2]}`. -/
def thm310Widths (a p : ℕ) : Fin 4 → ℕ
  | ⟨0, _⟩ => a + p + 1
  | ⟨1, _⟩ => a + 1
  | ⟨_ + 2, _⟩ => 1 + (a + p + 1)

/-- **The four oracles of Theorem 3.10** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 19), in the qubit model `A = {0,1}^a`,
`A_pure = {0,1}^p`: oracle 0 is `M^{Π1}` (`Π1` on `A ⊗ A_pure`), 1 is `M^{Π2}` (`Π2` on `A`),
2 is `Φ^{ctrl[V1]}`, 3 is `Φ^{ctrl[V2]}`. -/
noncomputable def thm310Oracles {a p : ℕ} (P1 : Matrix (Bits a × Bits p) (Bits a × Bits p) ℂ)
    (P2 : Matrix (Bits a) (Bits a) ℂ) (V1 V2 : Matrix (Bits a × Bits p) (Bits a) ℂ) :
    (j : Fin 4) → Matrix (Bits (thm310Widths a p j)) (Bits (thm310Widths a p j)) ℂ →
      Matrix (Bits (thm310Widths a p j)) (Bits (thm310Widths a p j)) ℂ
  | ⟨0, _⟩ => measQueryAP P1
  | ⟨1, _⟩ => measQueryA P2
  | ⟨2, _⟩ => ctrlIsoQuery V1
  | ⟨_ + 3, _⟩ => ctrlIsoQuery V2

end RandPurIso.Completion


