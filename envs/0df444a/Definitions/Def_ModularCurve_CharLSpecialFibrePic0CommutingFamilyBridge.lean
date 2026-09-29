-- Prove2me | Definitions.Def_ModularCurve_CharLSpecialFibrePic0CommutingFamilyBridge
-- name    : ModularCurve_CharLSpecialFibrePic0CommutingFamilyBridge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/041258c3-2fde-5922-b24e-5eddc4f3285c
-- title:
--   Commuting Hecke families matching the special-fibre Hecke operator
-- statement:
--   Throughout, $K$ is an algebraically closed field of characteristic a prime $\ell$, $N\ge 1$, and the degree-zero divisor class group $\mathrm{Pic}^0$ is taken for the field $\mathtt{modularFunctionFieldC}\,K\,N$ generated over $K$ inside $K$-Laurent series by the $q$-expansions of $j$ and of $j(q^N)$, assumed to satisfy the project's curve axioms `IsCurveOver` (principal divisors, residue fields finite over $K$, free rank-one module of Kähler differentials); $\mathtt{data}$ is modular polynomial data at $\ell$ and $\mathtt{hKr}$ a Kronecker congruence for it, these being the inputs from which the two endomorphisms $\mathtt{heckeFibreGeomLevelPic0OfIsCurveOver}$ (the special-fibre Hecke operator at $\ell$) and $\mathtt{frobeniusPushforwardGeomLevelPic0OfIsCurveOver}$ (Frobenius pushforward) of $\mathrm{Pic}^0$ are built. The predicate `Pic0SpecialFibreCommutingFamilyMatch` says of a `CommutingHeckeFamily` on $\mathrm{Pic}^0$ — a family $T_q$ of pairwise commuting $\mathbb{Z}$-linear endomorphisms indexed by the primes — that its member at $\ell$ equals, as a $\mathbb{Z}$-linear map, the special-fibre Hecke operator; an equivalent pointwise form is recorded.
--
--   The remaining results discharge the two obligations of the special-fibre headline from such a family. For the $\mathbb{T} = \mathbb{Z}[X_q]_q$-module structure on $\mathrm{Pic}^0$ induced by the family (the generator $X_q$ acting as $T_q$), matching implies `SpecialFibreHeckeModuleMatch`, and hence `SpecialFibreRelation`: $F(F y) - X_\ell\cdot F y + \ell y = 0$ for all $y$, with $F$ the Frobenius pushforward. The same relation is also given in the shape required by the `relation` field of `SpecializationWitnessData`, with $T_\ell$ written directly instead of through the module action. Finally, both conclusions are stated uniformly in the level: given a family of curve structures for all levels $M$ and, for each $M$, a commuting Hecke family matching at $\ell$, the relation holds at every level.
--
--   **Relation to Mathlib.** Mathlib has no Hecke action on divisor class groups of function fields; `CommutingHeckeFamily`, the polynomial Hecke algebra `HeckeAlg` and `SpecialFibreRelation` are the project's own notions, the induced module structure being obtained from Mathlib's `Module.compHom`.
--
--   **Where it is used.** The Eichler–Shimura relation in characteristic $\ell$ is what makes the Galois representations attached to Hecke eigenclasses have Frobenius characteristic polynomial $X^2 - T_\ell X + \ell$ at good primes; these bridges reduce the verification of that relation on the degree-zero divisor class group of the modular function field to exhibiting a single commuting family of Hecke operators whose member at $\ell$ is the geometric one, and package the outcome both as the special-fibre relation and as the relation required by a specialization witness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_CharLSpecialFibrePic0CommutingFamilyBridge.lean

import Definitions.Def_ModularCurve_CharLSpecialFibrePic0ForallMBridge
import Definitions.Def_ModularCurve_SpecializationWitness

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1200000

noncomputable section
open AlgebraicCurve

namespace ModularCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def Pic0SpecialFibreCommutingFamilyMatch
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N))) : Prop :=
  fam.T ⟨ℓ, hℓ.out⟩
    = (heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr).toIntLinearMap

theorem pic0SpecialFibreCommutingFamilyMatch_iff
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N))) :
    Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam
      ↔ ∀ x, fam.T ⟨ℓ, hℓ.out⟩ x
          = heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr x := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext x; exact h x

theorem specialFibreHeckeModuleMatch_of_commutingFamily
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)))
    (hfam : Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam) :
    SpecialFibreHeckeModuleMatch K N data hKr fam.module := by
  intro x
  rw [fam.module_heckeGen_smul ⟨ℓ, hℓ.out⟩ x, hfam]
  rfl

theorem specialFibreRelation_pic0_level_of_commutingFamily
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)))
    (hfam : Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam) :
    letI := fam.module
    SpecialFibreRelation (Pic0 K (modularFunctionFieldC K N)) ℓ hℓ.out
      (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr) :=
  specialFibreRelation_pic0_level_of_isCurveOver_of_match K N data hKr fam.module
    (specialFibreHeckeModuleMatch_of_commutingFamily K N data hKr fam hfam)

theorem specializationWitnessData_relation_of_commutingFamily
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)))
    (hfam : Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam)
    (y : Pic0 K (modularFunctionFieldC K N)) :
    frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr
        (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr y)
      - fam.T ⟨ℓ, hℓ.out⟩ (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr y)
      + ℓ • y = 0 := by
  rw [(pic0SpecialFibreCommutingFamilyMatch_iff K N data hKr fam).mp hfam,
    ← natCast_zsmul]
  exact eichlerShimura_special_fibre_pic0_level_of_isCurveOver K N data hKr y

variable (hcofam : IsCurveOverModularFunctionFieldCFamily K)

theorem forall_specialFibreRelation_pic0_of_commutingFamily_family
    (famfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K M)))
    (hfamfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      Pic0SpecialFibreCommutingFamilyMatch K M data hKr (famfam M)) :
    ∀ (M : ℕ) [NeZero M],
      letI := hcofam M; letI := (famfam M).module
      SpecialFibreRelation (Pic0 K (modularFunctionFieldC K M)) ℓ (Fact.out)
        (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr) := by
  intro M _
  letI := hcofam M
  exact specialFibreRelation_pic0_level_of_commutingFamily K M data hKr
    (famfam M) (hfamfam M)

theorem forall_specializationWitnessData_relation_of_commutingFamily_family
    (famfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K M)))
    (hfamfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      Pic0SpecialFibreCommutingFamilyMatch K M data hKr (famfam M)) :
    ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      ∀ y : Pic0 K (modularFunctionFieldC K M),
        frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr
            (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr y)
          - (famfam M).T ⟨ℓ, hℓ.out⟩
              (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr y)
          + ℓ • y = 0 := by
  intro M _
  letI := hcofam M
  exact specializationWitnessData_relation_of_commutingFamily K M data hKr
    (famfam M) (hfamfam M)

end ModularCurve


