-- Prove2me | Definitions.Def_RandPurIso_Completion_cor42Oracles
-- name    : RandPurIso_Completion_cor42Oracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:07.004675+00:00
-- url     : https://prove2.me/theorems/65d5ed80-842e-436d-b669-e04f702ec2f7
-- title:
--   The four oracles of Corollary 4.2
-- statement:
--   In the qubit model $A_{\mathrm{in}}=A=\{0,1\}^a$, $A_{\mathrm{out}}=A\otimes A_{\mathrm{pure}}$, oracle $0$ is $M^{\Pi_1}$ ($\Pi_1$ on $A_{\mathrm{out}}$), oracle $1$ is $M^{\Pi_2}$ ($\Pi_2$ on $A_{\mathrm{in}}$), oracle $2$ the ordinary query $\Phi^{V_1}$ and oracle $3$ the controlled query $\Phi^{\mathrm{ctrl}[V_2]}$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Corollary 4.2, p. 28

import Mathlib
import Definitions.Def_RandPurIso_Completion_isoQuery
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- Register widths of the four oracles of Corollary 4.2 (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 28): `M^{Π1}`, `M^{Π2}`,
`Φ^{V1}`, `Φ^{ctrl[V2]}`. -/
def cor42Widths (a p : ℕ) : Fin 4 → ℕ
  | ⟨0, _⟩ => a + p + 1
  | ⟨1, _⟩ => a + 1
  | ⟨2, _⟩ => a + p + 1
  | ⟨_ + 3, _⟩ => 1 + (a + p + 1)

/-- **The four oracles of Corollary 4.2** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 28), qubit model `A_in = A = {0,1}^a`,
`A_out = A ⊗ A_pure`, `A_pure = {0,1}^p`: oracle 0 is `M^{Π1}` (`Π1` on `A_out`), 1 is `M^{Π2}` (`Π2`
on `A_in`), 2 is the ordinary query `Φ^{V1}`, 3 is the controlled query `Φ^{ctrl[V2]}`. -/
noncomputable def cor42Oracles {a p : ℕ} (P1 : Matrix (Bits a × Bits p) (Bits a × Bits p) ℂ)
    (P2 : Matrix (Bits a) (Bits a) ℂ) (V1 V2 : Matrix (Bits a × Bits p) (Bits a) ℂ) :
    (j : Fin 4) → Matrix (Bits (cor42Widths a p j)) (Bits (cor42Widths a p j)) ℂ →
      Matrix (Bits (cor42Widths a p j)) (Bits (cor42Widths a p j)) ℂ
  | ⟨0, _⟩ => measQueryAP P1
  | ⟨1, _⟩ => measQueryA P2
  | ⟨2, _⟩ => isoQuery V1
  | ⟨_ + 3, _⟩ => ctrlIsoQuery V2

end RandPurIso.Completion


