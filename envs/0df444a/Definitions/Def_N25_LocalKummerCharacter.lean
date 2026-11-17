-- Prove2me | Definitions.Def_N25_LocalKummerCharacter
-- name    : N25_LocalKummerCharacter
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:22.422404+00:00
-- url     : https://prove2.me/theorems/9784aca5-a0fb-495a-a087-230dc33a9d09
-- title:
--   An order-five character from the mod-$25$ cyclotomic character
-- statement:
--   Defines the mod-$25$ cyclotomic character $χ_{25}:G_Q→(Z/25Z)^×$, an explicit order-five homomorphism $ψ̄:(Z/25Z)^×→(Z/71Z)^×$, and their composite $ψ=ψ̄∘χ_{25}$. This character supplies the one-dimensional subrepresentation in the $71$-torsion filtration.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalCarrier
noncomputable section
namespace N25
def galToRingEquiv :
    Gal →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) where
  toFun := fun σ => σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def chi25 : Gal →* (ZMod 25)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (IsAlgClosed.card_rootsOfUnity_eq
      (AlgebraicClosure ℚ) 25)).comp galToRingEquiv

def psiBarValue (u : (ZMod 25)ˣ) : (ZMod 71)ˣ :=
  match (u : ZMod 25).val with
  | 1 | 7 | 18 | 24 => 1
  | 2 | 11 | 14 | 23 => ZMod.unitOfCoprime 57 (by decide)
  | 3 | 4 | 21 | 22 => ZMod.unitOfCoprime 54 (by decide)
  | 6 | 8 | 17 | 19 => ZMod.unitOfCoprime 25 (by decide)
  | _ => ZMod.unitOfCoprime 5 (by decide)

def psiBar : (ZMod 25)ˣ →* (ZMod 71)ˣ where
  toFun := psiBarValue
  map_one' := by decide
  map_mul' := by decide

noncomputable def psi : Gal →* (ZMod 71)ˣ :=
  psiBar.comp chi25

end N25


