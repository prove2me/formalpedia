-- Prove2me | Definitions.Def_QEC_Coding_ChainComplex_Homotopy
-- name    : QEC_Coding_ChainComplex_Homotopy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:55:32.951944+00:00
-- url     : https://prove2.me/theorems/144ace26-9245-4b80-b3ee-64c6afc47639
-- title:
--   Homotopy
-- statement:
--   Definitions and structural lemmas for Homotopy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Homotopy.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding
universe u v w z
variable {F : Type u} [Field F]
variable {A0 A1 A2 : Type v}
variable {B0 B1 B2 : Type w}
variable {C0 C1 C2 : Type z}
variable [AddCommGroup A0] [Module F A0]
variable [AddCommGroup A1] [Module F A1]
variable [AddCommGroup A2] [Module F A2]
variable [AddCommGroup B0] [Module F B0]
variable [AddCommGroup B1] [Module F B1]
variable [AddCommGroup B2] [Module F B2]
variable [AddCommGroup C0] [Module F C0]
variable [AddCommGroup C1] [Module F C1]
variable [AddCommGroup C2] [Module F C2]
structure ThreeTermChainMap
    (A : ChainComplexData F A0 A1 A2)
    (B : ChainComplexData F B0 B1 B2) where
  map0 : A0 →ₗ[F] B0
  map1 : A1 →ₗ[F] B1
  map2 : A2 →ₗ[F] B2
  commutes_boundary1 : B.boundary1.comp map1 = map0.comp A.boundary1
  commutes_boundary2 : B.boundary2.comp map2 = map1.comp A.boundary2
namespace ThreeTermChainMap
variable {A : ChainComplexData F A0 A1 A2}
variable {B : ChainComplexData F B0 B1 B2}
variable {C : ChainComplexData F C0 C1 C2}
def id (A : ChainComplexData F A0 A1 A2) : ThreeTermChainMap A A where
  map0 := LinearMap.id
  map1 := LinearMap.id
  map2 := LinearMap.id
  commutes_boundary1 := by ext; rfl
  commutes_boundary2 := by ext; rfl
def comp (g : ThreeTermChainMap B C) (f : ThreeTermChainMap A B) :
    ThreeTermChainMap A C where
  map0 := g.map0.comp f.map0
  map1 := g.map1.comp f.map1
  map2 := g.map2.comp f.map2
  commutes_boundary1 := by
    ext x
    change C.boundary1 (g.map1 (f.map1 x)) =
      g.map0 (f.map0 (A.boundary1 x))
    calc
      C.boundary1 (g.map1 (f.map1 x)) =
          g.map0 (B.boundary1 (f.map1 x)) := by
        exact LinearMap.congr_fun g.commutes_boundary1 (f.map1 x)
      _ = g.map0 (f.map0 (A.boundary1 x)) := by
        congr 1
        exact LinearMap.congr_fun f.commutes_boundary1 x
  commutes_boundary2 := by
    ext x
    change C.boundary2 (g.map2 (f.map2 x)) =
      g.map1 (f.map1 (A.boundary2 x))
    calc
      C.boundary2 (g.map2 (f.map2 x)) =
          g.map1 (B.boundary2 (f.map2 x)) := by
        exact LinearMap.congr_fun g.commutes_boundary2 (f.map2 x)
      _ = g.map1 (f.map1 (A.boundary2 x)) := by
        congr 1
        exact LinearMap.congr_fun f.commutes_boundary2 x
@[simp]
theorem id_map0 (A : ChainComplexData F A0 A1 A2) : (id A).map0 = LinearMap.id := rfl
@[simp]
theorem id_map1 (A : ChainComplexData F A0 A1 A2) : (id A).map1 = LinearMap.id := rfl
@[simp]
theorem id_map2 (A : ChainComplexData F A0 A1 A2) : (id A).map2 = LinearMap.id := rfl
@[simp]
theorem comp_map0 (g : ThreeTermChainMap B C) (f : ThreeTermChainMap A B) :
    (g.comp f).map0 = g.map0.comp f.map0 := rfl
@[simp]
theorem comp_map1 (g : ThreeTermChainMap B C) (f : ThreeTermChainMap A B) :
    (g.comp f).map1 = g.map1.comp f.map1 := rfl
@[simp]
theorem comp_map2 (g : ThreeTermChainMap B C) (f : ThreeTermChainMap A B) :
    (g.comp f).map2 = g.map2.comp f.map2 := rfl
end ThreeTermChainMap
structure ThreeTermChainHomotopy
    {A : ChainComplexData F A0 A1 A2}
    {B : ChainComplexData F B0 B1 B2}
    (f g : ThreeTermChainMap A B) where
  homotopy0 : A0 →ₗ[F] B1
  homotopy1 : A1 →ₗ[F] B2
  degree0 : f.map0 - g.map0 = B.boundary1.comp homotopy0
  degree1 : f.map1 - g.map1 =
    homotopy0.comp A.boundary1 + B.boundary2.comp homotopy1
  degree2 : f.map2 - g.map2 = homotopy1.comp A.boundary2
structure ThreeTermChainHomotopyEquiv
    (A : ChainComplexData F A0 A1 A2)
    (B : ChainComplexData F B0 B1 B2) where
  forward : ThreeTermChainMap A B
  inverse : ThreeTermChainMap B A
  inverse_forward : ThreeTermChainHomotopy
    (inverse.comp forward) (ThreeTermChainMap.id A)
  forward_inverse : ThreeTermChainHomotopy
    (forward.comp inverse) (ThreeTermChainMap.id B)
namespace ThreeTermChainMap
variable [Fintype F]
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {A0 A2 : Type (max u v)} [AddCommGroup A0] [Module F A0]
  [AddCommGroup A2] [Module F A2]
variable {B0 B2 : Type (max u w)} [AddCommGroup B0] [Module F B0]
  [AddCommGroup B2] [Module F B2]
variable {A : ChainComplexData F A0 (Word F ι) A2}
variable {B : ChainComplexData F B0 (Word F κ) B2}
noncomputable def mapMiddleCycle (f : ThreeTermChainMap A B) :
    A.middleCycleCode.carrier →ₗ[F] B.middleCycleCode.carrier where
  toFun x := by
    refine ⟨f.map1 x.1, ?_⟩
    rw [B.mem_middleCycleCode_iff]
    have h := LinearMap.congr_fun f.commutes_boundary1 x.1
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      (A.mem_middleCycleCode_iff x.1).mp x.2, map_zero] at h
    exact h
  map_add' x y := by apply Subtype.ext; exact f.map1.map_add x.1 y.1
  map_smul' coefficient x := by
    apply Subtype.ext
    exact f.map1.map_smul coefficient x.1
noncomputable def mapCycleToMiddleHomology (f : ThreeTermChainMap A B) :
    A.middleCycleCode.carrier →ₗ[F] B.middleHomology :=
  B.middleBoundaryInCycles.mkQ.comp f.mapMiddleCycle
theorem middleBoundaryInCycles_le_ker_mapCycleToMiddleHomology
    (f : ThreeTermChainMap A B) :
    A.middleBoundaryInCycles ≤ LinearMap.ker f.mapCycleToMiddleHomology := by
  intro x hx
  change B.middleBoundaryInCycles.mkQ (f.mapMiddleCycle x) = 0
  change f.mapMiddleCycle x ∈ LinearMap.ker B.middleBoundaryInCycles.mkQ
  rw [Submodule.ker_mkQ]
  change f.map1 x.1 ∈ B.middleBoundaryCode.carrier
  change x.1 ∈ A.middleBoundaryCode.carrier at hx
  rcases (A.mem_middleBoundaryCode_iff x.1).mp hx with ⟨a2, ha2⟩
  apply (B.mem_middleBoundaryCode_iff (f.map1 x.1)).mpr
  refine ⟨f.map2 a2, ?_⟩
  have h := LinearMap.congr_fun f.commutes_boundary2 a2
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ha2] at h
  exact h
noncomputable def inducedMiddleHomology (f : ThreeTermChainMap A B) :
    A.middleHomology →ₗ[F] B.middleHomology :=
  A.middleBoundaryInCycles.liftQ f.mapCycleToMiddleHomology
    f.middleBoundaryInCycles_le_ker_mapCycleToMiddleHomology
@[simp]
theorem inducedMiddleHomology_mk (f : ThreeTermChainMap A B)
    (x : A.middleCycleCode.carrier) :
    f.inducedMiddleHomology (A.middleBoundaryInCycles.mkQ x) =
      B.middleBoundaryInCycles.mkQ (f.mapMiddleCycle x) := rfl
theorem inducedMiddleHomology_id
    (A : ChainComplexData F A0 (Word F ι) A2) :
    (ThreeTermChainMap.id A).inducedMiddleHomology = LinearMap.id := by
  apply LinearMap.ext
  intro xClass
  obtain ⟨x, rfl⟩ := A.middleBoundaryInCycles.mkQ_surjective xClass
  rfl
section Composition
variable {ρ : Type z} [Fintype ρ]
variable {C0 C2 : Type (max u z)} [AddCommGroup C0] [Module F C0]
  [AddCommGroup C2] [Module F C2]
variable {C : ChainComplexData F C0 (Word F ρ) C2}
theorem inducedMiddleHomology_comp
    (g : ThreeTermChainMap B C) (f : ThreeTermChainMap A B) :
    (g.comp f).inducedMiddleHomology =
      g.inducedMiddleHomology.comp f.inducedMiddleHomology := by
  apply LinearMap.ext
  intro xClass
  obtain ⟨x, rfl⟩ := A.middleBoundaryInCycles.mkQ_surjective xClass
  rfl
end Composition
end ThreeTermChainMap
namespace ThreeTermChainHomotopy
variable [Fintype F]
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {A0 A2 : Type (max u v)} [AddCommGroup A0] [Module F A0]
  [AddCommGroup A2] [Module F A2]
variable {B0 B2 : Type (max u w)} [AddCommGroup B0] [Module F B0]
  [AddCommGroup B2] [Module F B2]
variable {A : ChainComplexData F A0 (Word F ι) A2}
variable {B : ChainComplexData F B0 (Word F κ) B2}
theorem inducedMiddleHomology_eq
    {f g : ThreeTermChainMap A B}
    (h : ThreeTermChainHomotopy f g) :
    f.inducedMiddleHomology = g.inducedMiddleHomology := by
  apply LinearMap.ext
  intro xClass
  obtain ⟨x, rfl⟩ := A.middleBoundaryInCycles.mkQ_surjective xClass
  rw [f.inducedMiddleHomology_mk, g.inducedMiddleHomology_mk]
  apply (Submodule.Quotient.eq B.middleBoundaryInCycles).mpr
  change f.map1 x.1 - g.map1 x.1 ∈ B.middleBoundaryCode.carrier
  have hDegree := LinearMap.congr_fun h.degree1 x.1
  have hxCycle : A.boundary1 x.1 = 0 :=
    (A.mem_middleCycleCode_iff x.1).mp x.2
  simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, hxCycle, map_zero, zero_add] at hDegree
  rw [hDegree]
  exact (B.mem_middleBoundaryCode_iff _).mpr ⟨h.homotopy1 x.1, rfl⟩
end ThreeTermChainHomotopy
namespace ThreeTermChainHomotopyEquiv
variable [Fintype F]
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {A0 A2 : Type (max u v)} [AddCommGroup A0] [Module F A0]
  [AddCommGroup A2] [Module F A2]
variable {B0 B2 : Type (max u w)} [AddCommGroup B0] [Module F B0]
  [AddCommGroup B2] [Module F B2]
variable {A : ChainComplexData F A0 (Word F ι) A2}
variable {B : ChainComplexData F B0 (Word F κ) B2}
noncomputable def inducedMiddleHomologyEquiv
    (e : ThreeTermChainHomotopyEquiv A B) :
    A.middleHomology ≃ₗ[F] B.middleHomology where
  toFun := e.forward.inducedMiddleHomology
  invFun := e.inverse.inducedMiddleHomology
  map_add' x y := e.forward.inducedMiddleHomology.map_add x y
  map_smul' coefficient x :=
    e.forward.inducedMiddleHomology.map_smul coefficient x
  left_inv x := by
    have hHomotopy := e.inverse_forward.inducedMiddleHomology_eq
    have hComp := ThreeTermChainMap.inducedMiddleHomology_comp
      e.inverse e.forward
    have hId := ThreeTermChainMap.inducedMiddleHomology_id A
    calc
      e.inverse.inducedMiddleHomology
          (e.forward.inducedMiddleHomology x) =
          (e.inverse.inducedMiddleHomology.comp
            e.forward.inducedMiddleHomology) x := rfl
      _ = (e.inverse.comp e.forward).inducedMiddleHomology x := by
        rw [← hComp]
      _ = (ThreeTermChainMap.id A).inducedMiddleHomology x := by
        rw [hHomotopy]
      _ = x := by rw [hId]; rfl
  right_inv x := by
    have hHomotopy := e.forward_inverse.inducedMiddleHomology_eq
    have hComp := ThreeTermChainMap.inducedMiddleHomology_comp
      e.forward e.inverse
    have hId := ThreeTermChainMap.inducedMiddleHomology_id B
    calc
      e.forward.inducedMiddleHomology
          (e.inverse.inducedMiddleHomology x) =
          (e.forward.inducedMiddleHomology.comp
            e.inverse.inducedMiddleHomology) x := rfl
      _ = (e.forward.comp e.inverse).inducedMiddleHomology x := by
        rw [← hComp]
      _ = (ThreeTermChainMap.id B).inducedMiddleHomology x := by
        rw [hHomotopy]
      _ = x := by rw [hId]; rfl
end ThreeTermChainHomotopyEquiv
end QEC.Coding


