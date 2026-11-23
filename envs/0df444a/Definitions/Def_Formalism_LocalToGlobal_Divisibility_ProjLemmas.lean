-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- name    : Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:23.297803+00:00
-- url     : https://prove2.me/theorems/4baa2773-9bf9-4de2-9135-1188ee80de25
-- title:
--   Proj Lemmas
-- statement:
--   Definitions and structural lemmas for Proj Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section Sub
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
end Sub
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
def actHom : G →* Matrix (Fin S.dim) (Fin S.dim) K where
  toFun := S.actMat r
  map_one' := by
    unfold actMat
    rw [map_one]
    exact LinearMap.toMatrix_one _
  map_mul' := by
    intro s t
    unfold actMat
    rw [map_mul]
    exact LinearMap.toMatrix_mul _ _ _
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
section Basic
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
end Roots
section Chars
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Chars
section Conj
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Conj
section Assemble
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
end Assemble
section Schur
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
end Schur
end Formalism.L2.DIV
namespace Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
def stdPair : K →ₗ⋆[K] K →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
    (by intro x y z; simp [add_mul])
    (by intro a x y; simp only [smul_eq_mul, star_mul', starRingEnd_apply, mul_assoc])
    (by intro x y z; simp [mul_add])
    (by intro a x y; simp [mul_left_comm])
@[simp] theorem stdPair_apply (x y : K) : stdPair K x y = star x * y := rfl
abbrev regCSD : CSD K where
  Cl := G
  V := K
  ιV := Unit
  bV := Basis.singleton Unit K
  pair := stdPair K
  Gam := fun _ => Unit
  ρ := fun _ => 1
  Nab := fun _ => 1
  Del := fun _ => 1
theorem mem_regForms (f : G → K) : f ∈ (regCSD K G).Forms := by
  intro c γ
  rfl
def regAct : Representation K G (regCSD K G).Forms where
  toFun t := LinearMap.codRestrict _
    ((LinearMap.funLeft K K (fun c : G => c * t)) ∘ₗ (regCSD K G).Forms.subtype)
    (fun f => mem_regForms K G _)
  map_one' := by
    apply LinearMap.ext; intro f; apply Subtype.ext; funext c
    exact congrArg f.1 (mul_one (c : G))
  map_mul' := by
    intro s t
    apply LinearMap.ext; intro f; apply Subtype.ext; funext c
    exact congrArg f.1 (mul_assoc (c : G) s t).symm
def aug : MonoidAlgebra K G →ₐ[K] K := MonoidAlgebra.lift K K G (1 : G →* K)
end Formalism.L2.DIV.Test


