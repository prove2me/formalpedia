-- Prove2me | Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
-- name    : LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T13:56:56.054391+00:00
-- url     : https://prove2.me/theorems/23a65288-503f-4d8c-8b7e-562932568ea8
-- title:
--   Coordinates on the counterexample stabilizer
-- statement:
--   An explicit multiplicative equivalence from the subgroup $H$ in the Heisenberg example to $C_3\times D_6$, with the coordinate homomorphism and its bijectivity proof.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy.HeisenbergExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Diagonal and anti-diagonal base coordinates identify the stabilizer
of `(0, 1)` with `C₃ × S₃`, as stated in the manuscript. -/
def hCoordinates : C3 × S →* G where
  toFun z := match z.2 with
    | .r a => ⟨fun i => if i = 0 then 1 else if i = 1 then
        z.1 * Multiplicative.ofAdd a else z.1 * Multiplicative.ofAdd (-a), 1⟩
    | .sr a => ⟨fun i => if i = 0 then 1 else if i = 1 then
        z.1 * Multiplicative.ofAdd (-a) else z.1 * Multiplicative.ofAdd a, .sr 0⟩
  map_one' := by decide
  map_mul' := by decide

def hCoordinatesHom : C3 × S →* H :=
  hCoordinates.codRestrict H (by decide)

theorem hCoordinates_bijective : Function.Bijective hCoordinatesHom := by
  constructor
  · exact (by decide : ∀ x y, hCoordinatesHom x = hCoordinatesHom y → x = y)
  · exact (by decide : ∀ y, ∃ x, hCoordinatesHom x = y)

/-- The manuscript's identification of the order-18 subgroup. -/
noncomputable def hEquivProduct : H ≃* C3 × S :=
  (MulEquiv.ofBijective hCoordinatesHom hCoordinates_bijective).symm

end LocalConjugacy.HeisenbergExample

end LocalConjugacy.Proof

end


