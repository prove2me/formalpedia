-- Prove2me | Definitions.Def_RPLib_S4_CDPack44
-- name    : RPLib_S4_CDPack44
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:38:05.846902+00:00
-- url     : https://prove2.me/theorems/6dde5041-379a-4ecb-aa29-0c4c0c957a26
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 44 of 71
-- statement:
--   Part 44 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CoreB_Triv`: Core B, O2: the genus 0 case
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack37
import Definitions.Def_RPLib_S4_CDPack31
import Definitions.Def_RPLib_S4_CDPack24
import Definitions.Def_RPLib_S4_CDPack32c

/-!
# Curve-duality library package, part 44 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CoreB_Triv`: Core B, O2: the genus 0 case
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CoreB_Triv =====
section

/-!
# Core B, O2: the genus 0 case

* `degreeDataOfSubsingleton`: on a trivial group the constant degree `1` is degree data of genus `0`.
* `subsingleton_Pic0K_of_genus_zero`: for `g = 0` the group `Pic⁰(F / K)` is trivial.
* `subsingleton_PicBar0_of_genus_zero`: if `genusFK (kbar) (Fbar) = 0` then `PicBar0 Ω hk` is trivial.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg

/-- On a trivial group the constant degree `1` is degree data of genus `0`. -/
def degreeDataOfSubsingleton {A : Type*} [AddCommGroup A] [Subsingleton A] (π : Module.End ℤ A)
    (p : ℕ) : DegreeData π 0 p where
  deg _ := 1
  deg_one := rfl
  deg_mul _ _ := rfl
  deg_natCast n := by simp
  deg_poly _ _ := ⟨1, by simp, fun _ => by simp⟩
  deg_eq_zero_iff F := by
    constructor
    · intro h; exact absurd h one_ne_zero
    · intro h; exact (h (Set.toFinite _)).elim
  deg_eq_card_ker F _ := by
    have : Subsingleton (LinearMap.ker (aeval π F)) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact (Nat.card_eq_one_iff_unique.2 ⟨this, ⟨0⟩⟩).symm

theorem degreeDataOfSubsingleton_deg {A : Type*} [AddCommGroup A] [Subsingleton A]
    (π : Module.End ℤ A) (p : ℕ) (F : ℤ[X]) : (degreeDataOfSubsingleton π p).deg F = 1 := rfl

section Pic0K

open RamanujanPetersson.JacComplete RamanujanPetersson.RR

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem subsingleton_Pic0K_of_genus_zero (hg : genusFK K F = 0) : Subsingleton (Pic0K K F) := by
  refine ⟨fun a b => ?_⟩
  have h0 : ∀ z : Pic0K K F, z = 0 := fun z => by
    obtain ⟨x, hx⟩ := z
    obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hD : D.deg = 0 := (mem_Pic0K K F).1 hx
    exact Subtype.ext (clsK_eq_zero_of_genus_zero hg hD)
  rw [h0 a, h0 b]

end Pic0K

section PicBar0

open RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem subsingleton_PicBar0_of_genus_zero (hg : genusFK (kbar Fq Ω) (Fbar Fq F Ω) = 0) :
    Subsingleton (PicBar0 Ω hk) := by
  have := subsingleton_Pic0K_of_genus_zero hg
  exact (Psi0Equiv Fq F Ω hk).injective.subsingleton

end PicBar0

end RamanujanPetersson.CoreB

end


