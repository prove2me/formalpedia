-- Prove2me | Definitions.Def_PricingWithTips3DM_c2c769ccc443b1a929b3ced9
-- name    : PricingWithTips3DM_c2c769ccc443b1a929b3ced9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:50:08.729618+00:00
-- url     : https://prove2.me/theorems/b499ccd0-fe6f-4658-899c-39572cbc8027
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.MainTheorem
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_9fed7e8723f29399c5afd61d
import Definitions.Def_PricingWithTips3DM_3ad697468a6a29f83d4100a4
import Definitions.Def_PricingWithTips3DM_ec8ee304a04c4c3ad3171807
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Cook--Levin main theorem

This module closes the textbook semantic circuitization with the concrete
raw-input compiler.  The resulting explicit map is a genuine polynomial-time
many-one reduction, yielding NP-hardness and NP-completeness of the honest
serialized general-circuit satisfiability language.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- The concrete Cook--Levin map is a polynomial-time many-one reduction for
every normalized verifier witness. -/
theorem cookLevin_polyTimeReducible
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    PolyTimeReducible L GeneralCircuitSAT :=
  cookLevin_polyTimeReducible_of_computable W
    (cookLevinMap_polyTimeComputable W)

/-- **Cook--Levin theorem.** Every polynomially verifiable language reduces
in polynomial time to general Boolean-circuit satisfiability. -/
theorem cookLevin_theorem {Γ : Type} {L : Language Γ}
    (hL : PolyTimeVerifiable L) :
    PolyTimeReducible L GeneralCircuitSAT :=
  cookLevin_polyTimeReducible (VerifierWitness.ofPolyTimeVerifiable hL)

/-- General circuit satisfiability is NP-hard. -/
theorem generalCircuitSAT_npHard : NPHard GeneralCircuitSAT := by
  intro Γ L hL
  exact cookLevin_theorem hL

/-- General circuit satisfiability is NP-complete. -/
theorem generalCircuitSAT_npComplete : NPComplete GeneralCircuitSAT :=
  ⟨generalCircuitSAT_polyTimeVerifiable, generalCircuitSAT_npHard⟩

end

end CLRS.Chapter34.Turing.CookLevin


