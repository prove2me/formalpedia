-- Prove2me | Definitions.Def_FreeGroupFactorProof18
-- name    : FreeGroupFactorProof18
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T02:52:45.509081+00:00
-- url     : https://prove2.me/theorems/1206864b-7159-4dbb-9761-fa06942edf26
-- title:
--   Free group factors: supporting development, part 18
-- statement:
--   Part 18 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof17

set_option linter.all false

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45 u_46 u_47 u_48
universe u_49

open Filter Topology

namespace FreeFock
open Filter Topology
open scoped ENNReal
variable {α : Type u_6} [DecidableEq α]

end FreeFock
open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace CyclicSpectral
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
end CyclicSpectral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

namespace CyclicSpectral

section
open MeasureTheory
variable {H : Type u_19} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory Filter
variable {H : Type u_20} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Filter
variable {H : Type u_21} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end CyclicSpectral
namespace FreeFock

section
open MeasureTheory
variable {α : Type u_22} [DecidableEq α]

end
open MeasureTheory
variable {α : Type u_23} [DecidableEq α]

end FreeFock
open Filter Topology
open scoped ENNReal

namespace FreeFock

section
open Filter Topology Set MeasureTheory
variable {α : Type u_25} [DecidableEq α]

end
section
open Set
variable {α : Type u_26} [DecidableEq α]

end

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_28} [DecidableEq α]

end
section
open scoped ComplexConjugate
variable {α : Type u_29} [DecidableEq α]

end
section
variable {α : Type u_30} [DecidableEq α]

end
variable {α : Type u_31} [DecidableEq α]

end FreeFock
section

variable {A : Type u_32} [NormedRing A] [NormedAlgebra ℂ A]

end
namespace FreeFock

section
variable {α : Type u_33} [DecidableEq α]

end
variable {α : Type u_34} [DecidableEq α]

end FreeFock

section
variable {α : Type u_35}

end
section
variable {α : Type u_36} {G : Type u_37} [Group G]

end
namespace FreeFock
variable {α : Type u_38} [DecidableEq α]

def haarOperatorRepresentation : FreeGroup α →* Operator α :=
  (gaussianAlgebra α).subtype.toMonoidHom.comp
    ((unitary (gaussianAlgebra α)).subtype.comp haarRepresentation)

 theorem haarProduct_eq_prod (L : List (α×ℤ)) :
    haarProduct L = (((L.map (fun p => (spectralHaar p.1)^p.2)).prod : unitary (gaussianAlgebra α)) : gaussianAlgebra α) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rcases p with ⟨i,k⟩
    change ((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) * haarProduct L = _
    change ((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) * haarProduct L =
      (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) * _
    exact congrArg (fun x : Operator α =>
      (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)*x) ih

 theorem haarRepresentation_run_moment (R : List ((α×Bool)×ℕ))
    (hpos : ∀p∈R,0<p.2) (hred : adjacentDistinct (R.map (fun p => p.1.1))) (hne : R≠[]) :
    vacuumTrace (haarOperatorRepresentation (FreeGroup.mk (expandSignedRuns R)))=0 := by
  change vacuumTrace (((FreeGroup.lift (spectralHaar (α := α)) (FreeGroup.mk (expandSignedRuns R)) : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)=0
  rw [lift_expandSignedRuns,← haarProduct_eq_prod]
  apply spectralHaar_mixed_moment
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact signedExponent_ne_zero _ _ (hpos q hq)
  · have he : ∀ L : List α, colorsReduced L=adjacentDistinct L := by
      intro L
      induction L with
      | nil => rfl
      | cons i L ih =>
        simp only [colorsReduced,adjacentDistinct,ih]
        try (cases L <;> rfl)
    rw [he]
    simpa only [signedRunBlocks,List.map_map,Function.comp_def] using hred
  · simpa [signedRunBlocks] using hne

 theorem haarRepresentation_moment (g : FreeGroup α) :
    vacuumTrace (haarOperatorRepresentation g)=if g=1 then 1 else 0 := by
  classical
  by_cases hg : g=1
  · subst g
    simp only [map_one,ite_true,vacuumTrace_one]
  · rw [ite_eq_right hg]
    obtain ⟨R,hR,hpos,hred⟩ := reduced_signed_runs g.toWord FreeGroup.isReduced_toWord
    have hne : R≠[] := by
      intro he
      have hn : g.toWord=[] := by simpa only [he,expandSignedRuns,List.flatMap_nil] using hR
      apply hg
      rw [← FreeGroup.mk_toWord (x := g),hn]
      rfl
    rw [← FreeGroup.mk_toWord (x := g),hR]
    exact haarRepresentation_run_moment R hpos hred hne

end FreeFock

namespace CyclicUnitary
open scoped ENNReal
variable {G : Type u_42} {E : Type u_43} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (ρ : G →* (E →L[ℂ] E)) (hstar : ∀ g,star (ρ g)=ρ g⁻¹) (ξ : E)

omit [DecidableEq G] in
include hstar in

theorem adjoin_range_span :
    (StarAlgebra.adjoin ℂ (Set.range ρ)).toSubalgebra.toSubmodule=
      Submodule.span ℂ (Set.range ρ) := by
  rw [StarAlgebra.adjoin_eq_span]
  have hs : star (Set.range ρ)=Set.range ρ := by
    ext T
    change (star T∈Set.range ρ) ↔ T∈Set.range ρ
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨g⁻¹,?_⟩
      rw [← hstar,hg,star_star]
    · rintro ⟨g,rfl⟩
      exact ⟨g⁻¹,(hstar g).symm⟩
  rw [hs,Set.union_self]
  let M : Submonoid (E →L[ℂ] E) :=
    { carrier := Set.range ρ
      one_mem' := ⟨1,map_one ρ⟩
      mul_mem' := by
        rintro _ _ ⟨g,rfl⟩ ⟨h,rfl⟩
        exact ⟨g*h,map_mul ρ g h⟩ }
  change Submodule.span ℂ ((Submonoid.closure (M : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))=_
  rw [Submonoid.closure_eq]
  rfl

def orbitSpan : Submodule ℂ E := Submodule.span ℂ (Set.range (fun g => ρ g ξ))

omit [DecidableEq G] in
include hstar in
theorem apply_mem_orbitSpan (T : (E →L[ℂ] E)) (hT : T∈StarAlgebra.adjoin ℂ (Set.range ρ)) :
    T ξ∈orbitSpan ρ ξ := by
  change T∈(StarAlgebra.adjoin ℂ (Set.range ρ)).toSubalgebra.toSubmodule at hT
  rw [adjoin_range_span ρ hstar] at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨g,rfl⟩ := hT
    exact Submodule.subset_span (Set.mem_range_self g)
  | zero => exact (orbitSpan ρ ξ).zero_mem
  | add T U _ _ hT hU => exact (orbitSpan ρ ξ).add_mem hT hU
  | smul c T _ hT => exact (orbitSpan ρ ξ).smul_mem c hT

include hstar in
theorem orbit_inner (htrace : ∀ g,inner ℂ ξ (ρ g ξ)=if g=1 then 1 else 0) (g h : G) :
    inner ℂ (ρ g ξ) (ρ h ξ)=if g=h then 1 else 0 := by
  classical
  calc
    _ = inner ℂ ξ (star (ρ g) (ρ h ξ)) :=
      (ContinuousLinearMap.adjoint_inner_right (ρ g) ξ (ρ h ξ)).symm
    _ = inner ℂ ξ (ρ (g⁻¹*h) ξ) := by rw [hstar,map_mul]; rfl
    _ = _ := by rw [htrace]; simp only [inv_mul_eq_one]

def basis (g : G) : lp (fun _ : G => ℂ) 2 := lp.single 2 g 1

omit [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
 theorem basis_inner (g h : G) :
    inner ℂ (basis g) (basis h)=if g=h then 1 else 0 := by
  simp [basis,lp.inner_single_left,lp.single_apply,Pi.single_apply]

omit [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
 theorem basis_total : (Submodule.span ℂ (Set.range (basis (G := G)))).topologicalClosure=⊤ := by
  let K := (Submodule.span ℂ (Set.range (basis (G := G)))).topologicalClosure
  apply top_unique
  intro η _
  apply (Submodule.span ℂ (Set.range (basis (G := G)))).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) η)
  filter_upwards [] with s
  apply K.sum_mem
  intro g _
  have he : lp.single (E := fun _ : G => ℂ) 2 g (η g)=(η g) • basis g := by
    ext h
    simp [basis,lp.single_apply,Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self g)))

def spatial (htrace : ∀ g,inner ℂ ξ (ρ g ξ)=if g=1 then 1 else 0)
    (htotal : (orbitSpan ρ ξ).topologicalClosure=⊤) :
    lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] E :=
  GramSpatial.spatial basis (fun g => ρ g ξ)
    (fun g h => (orbit_inner ρ hstar ξ htrace g h).trans (basis_inner g h).symm)
    basis_total htotal

end CyclicUnitary
namespace FreeFock
variable {α : Type u_44} [DecidableEq α]

 theorem haarOperatorRepresentation_star (g : FreeGroup α) :
    star (haarOperatorRepresentation g)=haarOperatorRepresentation g⁻¹ := by
  change star (((haarRepresentation g : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) =
    (((haarRepresentation g⁻¹ : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)
  rw [map_inv]
  rfl

 theorem haarOperatorRepresentation_of (i : α) :
    haarOperatorRepresentation (FreeGroup.of i)=spectralHaarOperator i := by
  change ((((FreeGroup.lift (spectralHaar (α := α))) (FreeGroup.of i) : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) = _
  rw [FreeGroup.lift_apply_of]
  rfl

 theorem haarGroup_cyclic_total :
    (CyclicUnitary.orbitSpan (haarOperatorRepresentation (α := α)) vacuum).topologicalClosure=⊤ := by
  apply top_unique
  rw [← spectralHaar_cyclic_total (α := α)]
  apply Submodule.topologicalClosure_mono
  rintro η ⟨T,hT,rfl⟩
  apply CyclicUnitary.apply_mem_orbitSpan haarOperatorRepresentation haarOperatorRepresentation_star
  apply StarAlgebra.adjoin_mono _ hT
  rintro _ ⟨i,rfl⟩
  exact ⟨FreeGroup.of i,haarOperatorRepresentation_of i⟩

def haarSpatial : lp (fun _ : FreeGroup α => ℂ) 2 ≃ₗᵢ[ℂ] Fock α :=
  CyclicUnitary.spatial haarOperatorRepresentation haarOperatorRepresentation_star vacuum
    haarRepresentation_moment haarGroup_cyclic_total

end FreeFock

section

variable {A : Type u_45} {B : Type u_46} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

end
open scoped ENNReal
variable {G : Type u_47} [Group G] [DecidableEq G]

namespace FreeFock
variable {α : Type u_48} [DecidableEq α]

end FreeFock

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

def subalgebraEqualityEquiv (M N : StarSubalgebra ℂ A) (he : M=N) : M ≃⋆ₐ[ℂ] N :=
  subalgebraEquiv M N (StarAlgEquiv.refl ℂ A) (fun a => by change a∈N ↔ a∈M;rw [he])

@[simp] theorem subalgebraEqualityEquiv_val (M N : StarSubalgebra ℂ A) (he : M=N) (x : M) :
    (subalgebraEqualityEquiv M N he x:A)=(x:A) := rfl

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

variable {A : Type u_6} {B : Type u_7} [CStarAlgebra A] [CStarAlgebra B]

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)] (p : M) (hp : IsStarProjection p)

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.FreeFock
open Amplification
variable {α : Type u_8} [DecidableEq α]

instance scalarGeneratedClosed : IsClosed (scalarSystem.generated scalarFlip : Set (Operator ScalarIndex)) :=
  Set.isClosed_centralizer _

def scalarTrace (T : scalarSystem.generated scalarFlip) : ℂ := vacuumTrace (T:Operator ScalarIndex)

end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_9} {B : Type u_10} [CStarAlgebra A] [CStarAlgebra B]
variable (p : A) (hp : IsStarProjection p) (q : Corner p hp) (hq : IsStarProjection q)

variable (τ : A → ℂ) (𝒯 : TopologicalSpace A)

def HasCornerScaling (t : ℝ) : Prop :=
  ∃ (p : A) (hp : IsStarProjection p) (e : A ≃⋆ₐ[ℂ] Corner p hp),
    τ p=(t:ℂ) ∧
    @Continuous _ _ 𝒯 (cornerTopology 𝒯 p hp) e ∧
    @Continuous _ _ (cornerTopology 𝒯 p hp) 𝒯 e.symm ∧
    ∀ x : A, τ (e x : A)=(t:ℂ)*τ x

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25

namespace FreeGroupFactorMain.Amplification
namespace OperatorSum
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Operator (E : Type u_6) [NormedAddCommGroup E] [InnerProductSpace ℂ E] := E →L[ℂ] E

end OperatorSum
end FreeGroupFactorMain.Amplification
namespace FreeGroupFactorMain.Amplification.OperatorSum

section
variable {E : Type u_16} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type u_17} {U : ι → Operator E}

end
variable {E : Type u_18} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_21} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def centralSupportSpace (A : StarSubalgebra ℂ (Operator E)) (p : Operator E) : Submodule ℂ E :=
  (Submodule.span ℂ {x | ∃ T ∈ A, ∃ y, x=T (p y)}).topologicalClosure

instance centralSupportSpace_complete (A : StarSubalgebra ℂ (Operator E)) (p : Operator E) :
    CompleteSpace (centralSupportSpace A p) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.Amplification.OperatorSum
variable {E : Type u_22} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
open OperatorSum
variable {E : Type u_23} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 variable {G : Type u_24} [Group G]

end
open scoped ENNReal
open OperatorSum

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section
namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

instance ambientClosed : IsClosed (ambientAlgebra (ι := ℕ) u v : Set (Operator ℕ)) :=
  Set.isClosed_centralizer _

variable (hu : u≠0) (hv' : v≠0) (hunit : u^2+v^2=1)
def ambientScalarIso : ambientAlgebra (ι := ℕ) u v ≃⋆ₐ[ℂ] scalarSystem.generated scalarFlip :=
  (subalgebraEqualityEquiv _ _ (ambient_generated_eq u v hu hv' hunit).symm).trans
    (ambientGaussianIso u v hu hv' hunit)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

namespace NormalTracialEquiv
variable {τA : A → ℂ} {τB : B → ℂ} {τC : C → ℂ}
variable {𝒯A : TopologicalSpace A} {𝒯B : TopologicalSpace B} {𝒯C : TopologicalSpace C}

end NormalTracialEquiv
end

open scoped ENNReal
variable {G : Type u_4} [Group G]

abbrev GroupCornerNormalIso (t : ℝ) (p : stabilization G) (hp : IsStarProjection p) :=
  NormalTracialEquiv (normalizedCornerTrace stabilizedTrace t p hp) canonicalTrace
    (cornerTopology (stabilizationTopology G) p hp) (groupUltraweakTopology G)

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1

namespace FreeGroupFactorMain.Interpolation
open Amplification
open scoped ENNReal

@[simp] theorem parameterModel_top : parameterModel ⊤=Model.infinity := by
  classical
  simp [parameterModel]

@[simp] theorem parameterModel_nat (n : ℕ) : parameterModel (n:ℝ≥0∞)=Model.integer n := by
  classical
  have hn : ∃k : ℕ,(n:ℝ≥0∞)=(k:ℝ≥0∞) := ⟨n,rfl⟩
  simp only [parameterModel,ENNReal.natCast_ne_top,ite_false,dite_eq_left hn]
  congr 1
  exact_mod_cast hn.choose_spec.symm

end FreeGroupFactorMain.Interpolation

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_1} [Group G]

variable [DecidableEq G]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.Interpolation
open Amplification
open scoped ENNReal

end FreeGroupFactorMain.Interpolation

end

end OAI
end


