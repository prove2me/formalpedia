-- Prove2me | Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientsData
-- name    : MazurTransfer_RepresentationDiscreteCoefficientsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T01:24:36.17523+00:00
-- url     : https://prove2.me/theorems/323a620a-ffcb-4e7e-a8a1-f5c67d84ea3a
-- title:
--   Original discrete representation coefficients and continuous H1 intertwiner maps
-- statement:
--   For a semiring k, group G, k-module V and representation rho, retain the original distinct wrapper Coefficient(rho), its multiplicative commutative group, rho-action and discrete topology. Original intertwiners from an existing multiplicative coefficient action give equivariant coefficient homomorphisms and induced maps on the presented continuous H1 and subgroup restrictions, with the original compatibility law. This does not assert continuity of an arbitrary representation action. All 43 original declaration types and 17 nonproof definition values are compared; the inductive layout, constructor and recursor reduction rules are compared separately. The 23 proof-valued types include the generated structure facts and original computation/compatibility laws. No extra owned theorem credit is assigned to them. Named downstream consumers are actual norm-character continuous H1 maps and their local restrictions.
-- source:
--   Original MazurTheorem RepresentationDiscreteCoefficients, Apache-2.0. Every original declaration body and structure is retained byte-for-byte; only imports are replaced by checked public coefficient-map data and the accepted restriction-compatibility theorem.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a representation specifies a distinct discrete coefficient
group, and actual intertwining maps induce coefficient homomorphisms from
an existing multiplicative action without replacing that action.
Named downstream consumer: continuous H1 maps for the actual norm-character
quotients and their local restrictions.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoefficientMapData
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyCoefficientMap_restriction_coefficientMap
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Group.TransferInstance

noncomputable section
namespace MazurTransfer.RepresentationDiscreteCoefficients
variable {k G V : Type} [Semiring k] [Group G] [AddCommGroup V] [Module k V]

@[ext] structure Coefficient (ρ : Representation k G V) where
  val : V

def coefficientEquiv (ρ : Representation k G V) : Coefficient ρ ≃ Multiplicative V where
  toFun x := Multiplicative.ofAdd x.val
  invFun x := ⟨x.toAdd⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance coefficientCommGroup (ρ : Representation k G V) : CommGroup (Coefficient ρ) :=
  (coefficientEquiv ρ).commGroup

instance coefficientAction (ρ : Representation k G V) : MulDistribMulAction G (Coefficient ρ) where
  smul g x := ⟨ρ g x.val⟩
  one_smul x := by
    apply Coefficient.ext
    exact LinearMap.congr_fun (map_one ρ) x.val
  mul_smul g h x := by
    apply Coefficient.ext
    exact LinearMap.congr_fun (map_mul ρ g h) x.val
  smul_one g := by
    apply Coefficient.ext
    exact map_zero (ρ g)
  smul_mul g x y := by
    apply Coefficient.ext
    exact map_add (ρ g) x.val y.val

instance coefficientTopology (ρ : Representation k G V) : TopologicalSpace (Coefficient ρ) := ⊥
instance coefficientDiscrete (ρ : Representation k G V) : DiscreteTopology (Coefficient ρ) := ⟨rfl⟩
instance coefficientTopologicalGroup (ρ : Representation k G V) : IsTopologicalGroup (Coefficient ρ) :=
  inferInstance

theorem coefficient_val_smul (ρ : Representation k G V) (g : G) (x : Coefficient ρ) :
    (g • x).val = ρ g x.val := rfl

theorem coefficient_val_pow (ρ : Representation k G V) (x : Coefficient ρ) (n : ℕ) :
    (x ^ n).val = n • x.val := rfl

variable {M : Type} [CommGroup M] [MulDistribMulAction G M]
  [Module k (Additive M)]
variable (ρ : Representation k G (Additive M)) (τ : Representation k G V)
variable (f : Representation.IntertwiningMap ρ τ)

def fromIntertwining : M →* Coefficient τ where
  toFun m := ⟨f (Additive.ofMul m)⟩
  map_one' := Coefficient.ext (map_zero f)
  map_mul' m n := Coefficient.ext (map_add f (Additive.ofMul m) (Additive.ofMul n))

theorem fromIntertwining_equivariant
    (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m))
    (g : G) (m : M) : fromIntertwining ρ τ f (g • m) = g • fromIntertwining ρ τ f m := by
  apply Coefficient.ext
  change f (Additive.ofMul (g • m)) = τ g (f (Additive.ofMul m))
  rw [← hρ]
  exact Representation.IntertwiningMap.isIntertwining ρ τ f g (Additive.ofMul m)

theorem fromIntertwining_surjective (hf : Function.Surjective f) :
    Function.Surjective (fromIntertwining ρ τ f) := by
  intro y
  obtain ⟨m, hm⟩ := hf y.val
  exact ⟨m.toMul, Coefficient.ext hm⟩

variable [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M]

def mapH1 (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m)) :
    ContinuousFirstCohomologyPresentation.H1 G M →+
      ContinuousFirstCohomologyPresentation.H1 G (Coefficient τ) :=
  ContinuousFirstCohomologyCoefficientMap.coefficientMap G M (Coefficient τ)
    (fromIntertwining ρ τ f) (fromIntertwining_equivariant ρ τ f hρ) continuous_of_discreteTopology

def localMapH1 (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m))
    (S : Subgroup G) :
    ContinuousFirstCohomologyPresentation.H1 S M →+
      ContinuousFirstCohomologyPresentation.H1 S (Coefficient τ) :=
  ContinuousFirstCohomologyCoefficientMap.coefficientMap S M (Coefficient τ)
    (fromIntertwining ρ τ f) (fun s m => fromIntertwining_equivariant ρ τ f hρ s.val m)
    continuous_of_discreteTopology

theorem restriction_mapH1
    (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m))
    (S : Subgroup G) (x : ContinuousFirstCohomologyPresentation.H1 G M) :
    ContinuousFirstCohomologySubgroupRestriction.restriction G (Coefficient τ) S (mapH1 ρ τ f hρ x) =
      localMapH1 ρ τ f hρ S (ContinuousFirstCohomologySubgroupRestriction.restriction G M S x) :=
  ContinuousFirstCohomologyCoefficientMap.restriction_coefficientMap G M (Coefficient τ)
    (fromIntertwining ρ τ f) (fromIntertwining_equivariant ρ τ f hρ)
    continuous_of_discreteTopology S x

end MazurTransfer.RepresentationDiscreteCoefficients
#print axioms MazurTransfer.RepresentationDiscreteCoefficients.fromIntertwining_equivariant
#print axioms MazurTransfer.RepresentationDiscreteCoefficients.mapH1


