-- Prove2me | Definitions.Def_LocalConjugacy_Proof_CocycleActions
-- name    : LocalConjugacy_Proof_CocycleActions
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:39:37.272298+00:00
-- url     : https://prove2.me/theorems/5cd71c24-8740-48ec-8344-2a7654cab589
-- title:
--   Actions on cocycles and cohomology classes
-- statement:
--   Coefficient translation of cocycles, the orbit describing a cohomology class, and the induced twisting action on a class. Structural compatibility proofs make these actual group actions.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

@[ext] theorem Cocycle.ext {K : Subgroup J} {f g : Cocycle (N := N) K}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Left coefficient action on cocycles. Its orbits are cohomology classes. -/
def coboundaryCocycle {K : Subgroup J} (f : Cocycle (N := N) K) (n : N) :
    Cocycle (N := N) K where
  toFun x := n * f.toFun x * ((x : J) • n⁻¹)
  continuous_toFun := (continuous_const.mul f.continuous_toFun).mul
    (continuous_subtype_val.smul continuous_const)
  map_mul x y := by
    rw [f.map_mul]
    simp only [Subgroup.coe_mul, smul_mul', smul_smul, smul_inv']
    group

@[instance_reducible] def coefficientAction (K : Subgroup J) : MulAction N (Cocycle (N := N) K) where
  smul n f := coboundaryCocycle f n
  one_smul f := by
    apply Cocycle.ext
    intro x
    change 1 * f.toFun x * ((x : J) • (1 : N)⁻¹) = f.toFun x
    simp
  mul_smul n m f := by
    apply Cocycle.ext
    intro x
    change (n * m) * f.toFun x * ((x : J) • (n * m)⁻¹) =
      n * (m * f.toFun x * ((x : J) • m⁻¹)) * ((x : J) • n⁻¹)
    simp only [mul_inv_rev, smul_mul']
    group

def CohomologyClass {K : Subgroup J} (f : Cocycle (N := N) K) :=
  {g : Cocycle (N := N) K // Cohomologous f g}

theorem orbit_eq_cohomologyClass {K : Subgroup J} (f : Cocycle (N := N) K) :
    @MulAction.orbit N (Cocycle (N := N) K) (coefficientAction K).toSMul f =
      {g | Cohomologous f g} := by
  letI := coefficientAction (N := N) K
  ext g
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n⁻¹, fun x => ?_⟩
    have he := congrArg (fun c : Cocycle (N := N) K => c.toFun x) hn
    change n * f.toFun x * ((x : J) • n⁻¹) = g.toFun x at he
    simpa only [inv_inv] using he.symm
  · rintro ⟨n, hn⟩
    refine ⟨n⁻¹, ?_⟩
    apply Cocycle.ext
    intro x
    change n⁻¹ * f.toFun x * ((x : J) • (n⁻¹)⁻¹) = g.toFun x
    simpa only [inv_inv] using (hn x).symm

instance finite_cohomologyClass [Finite N] {K : Subgroup J} (f : Cocycle (N := N) K) :
    Finite (CohomologyClass f) := by
  letI := coefficientAction (N := N) K
  letI : Finite (MulAction.orbit N f) := Finite.of_surjective
    (fun n : N => (⟨n • f, ⟨n, rfl⟩⟩ : MulAction.orbit N f))
    (by rintro ⟨g, n, hn⟩; exact ⟨n, Subtype.ext hn⟩)
  have he := orbit_eq_cohomologyClass f
  exact Finite.of_equiv (MulAction.orbit N f) (Equiv.setCongr he)



theorem twist_one {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) :
    twistCocycle f 1 = f := by
  ext x
  simp only [twistCocycle, conjugateDomain, inv_one, one_mul, mul_one, one_smul]
  rfl

theorem twist_mul {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) (j k : J) :
    twistCocycle f (j * k) = twistCocycle (twistCocycle f k) j := by
  apply Cocycle.ext
  intro x
  change (j * k) • f.toFun ⟨(j * k)⁻¹ * x * (j * k), _⟩ =
    j • (k • f.toFun ⟨k⁻¹ * (j⁻¹ * x * j) * k, _⟩)
  simp only [mul_inv_rev, mul_smul, mul_assoc]

@[instance_reducible] def classAction {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K)
    (Q : Subgroup J) (hinv : InvariantUnder Q K f) : MulAction Q (CohomologyClass f) where
  smul q g := ⟨twistCocycle g.val q, by
    have hq : Cohomologous f (twistCocycle f q) := by
      obtain ⟨n, hn⟩ := hinv q q.property
      exact ⟨n, fun x => hn x x.property (conjugateDomain K q x).property⟩
    exact cohomologous_trans hq (twist_cohomologous g.property q)⟩
  one_smul g := Subtype.ext (twist_one g.val)
  mul_smul q r g := Subtype.ext (twist_mul g.val q r)





end LocalConjugacy

end LocalConjugacy.Proof

end


