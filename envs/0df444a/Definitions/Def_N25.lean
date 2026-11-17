-- Prove2me | Definitions.Def_N25
-- name    : N25
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:42.14246+00:00
-- url     : https://prove2.me/theorems/c13388fc-c7af-4ba7-8593-f4a256f68be4
-- title:
--   The level-$25$ Jacobian, rational subgroup, and key endomorphism
-- statement:
--   The file defines the subgroup $$H_{25}=⟨7⟩=\{1,7,18,24\}⊂(ℤ/25ℤ)^×,$$ the corresponding modular Jacobian carrier $J$, the absolute Galois group, and the arithmetic fixed subgroup $M=J(ℚ)$. It also defines the diamond endomorphism $γ$ attached to $13$ and the endomorphism $$π=2·id+4γ+γ^2.$$ These are the basic group-theoretic objects for the cuspidal and Kummer endgame.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
set_option autoImplicit false
noncomputable section

namespace N25
/-- H = {1, 7, 24, 18}. -/
def H25 : Subgroup (ZMod 25)ˣ := Subgroup.zpowers (ZMod.unitOfCoprime 7 (by decide))
abbrev J : Type _ := ModularCurve.JH 25 H25
abbrev Gal : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ
/-- M = J(ℚ): the arithmetic-Galois fixed subgroup of the library carrier. -/
def M : AddSubgroup J := FixedPoints.addSubgroup Gal J
def gamma : J →+ J := ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))
def piEnd : J →+ J := 2 • AddMonoidHom.id J + 4 • gamma + gamma.comp gamma
end N25


