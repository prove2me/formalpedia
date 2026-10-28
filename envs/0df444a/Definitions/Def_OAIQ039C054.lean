-- Prove2me | Definitions.Def_OAIQ039C054
-- name    : OAIQ039C054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:20.902644+00:00
-- url     : https://prove2.me/theorems/15f7689b-2338-4206-b0fc-1b6c88838839
-- title:
--   Definitions bundle OAIQ039C054 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 9 definitions, 1 inductive type or structure, 3 instances and 17 theorems. The definitions and types are `OAI.Kadison.CentralSpectral.Spectrum`, `OAI.Kadison.ConcreteCorner.vonNeumann`, `OAI.Kadison.Decomposable.fieldAlgebra`, `OAI.Kadison.DihedralCorner.compressCorner`, `OAI.Kadison.DihedralCorner.cosineAlgebra`, `OAI.Kadison.DihedralCorner.cosineSpace`, `OAI.Kadison.DihedralCorner.positiveCosines`, `OAI.Kadison.MatrixTower.Stage`, `OAI.Kadison.NormalGNS.trace`, `OAI.Kadison.halfCornerTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AbelianGNSSpectral`, `Commutator_ConcreteCornerVonNeumann`, `Commutator_DihedralFejer`, `Commutator_FieldAlgebra`, `Commutator_FieldNormClosure`, `Commutator_HankelAlgebra`, `Commutator_MatrixTower`, `Commutator_StandardTrace`, `Commutator_StarField`.
--
--   **Imports.** It imports the bundles `OAIQ039C042`, `OAIQ039C043`, `OAIQ039C044` and `OAIQ039C045` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C059`, `OAIQ039C060`, `OAIQ039C061`, `OAIQ039C062`, `OAIQ039C064` and `OAIQ039C065`; the statements `OAI.Kadison.CentralSpectral.central_indicators`, `OAI.Kadison.CentralSpectral.conjugate_center`, `OAI.Kadison.CentralSpectral.exists_stable_center_spectral_model`, `OAI.Kadison.CentralSpectral.indicator_in_scalar_spectral_range`, `OAI.Kadison.CentralSpectral.scalar_conjugate`, `OAI.Kadison.CentralSpectral.scalar_indicator_commutes`, `OAI.Kadison.CentralSpectral.stable_model_bound`, `OAI.Kadison.CentralSpectral.stable_model_center`, `OAI.Kadison.ConcreteCorner.vonNeumann_range`, `OAI.Kadison.MatrixTower.exists_irreducible_stage_tower`, `OAI.Kadison.MatrixTower.scalar_of_commutes`, `OAI.Kadison.MatrixTower.small_of_stages` and `OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages`; the proofs of `OAI.Kadison.CentralSpectral.central_indicators`, `OAI.Kadison.CentralSpectral.conjugate_center`, `OAI.Kadison.CentralSpectral.indicator_in_scalar_spectral_range`, `OAI.Kadison.CentralSpectral.scalar_conjugate`, `OAI.Kadison.CentralSpectral.scalar_indicator_commutes`, `OAI.Kadison.CentralSpectral.separable_uniform_bound`, `OAI.Kadison.CentralSpectral.stable_model_bound`, `OAI.Kadison.CentralSpectral.stable_model_center`, `OAI.Kadison.ConcreteCorner.vonNeumann_range`, `OAI.Kadison.CornerTransport.finite_small_corner_bound`, `OAI.Kadison.FinitePatching.exists_all_unitary_tests`, `OAI.Kadison.FinitePatching.exists_countable_unitary_tests`, `OAI.Kadison.FinitePatching.exists_finite_word_patch`, `OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests`, `OAI.Kadison.FreeBlocks.normal_free_original_bound`, `OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner`, `OAI.Kadison.MatrixTower.scalar_of_commutes`, `OAI.Kadison.MatrixTower.small_of_stages`, `OAI.Kadison.NormalRepresentation.exists_stable_gns_model`, `OAI.Kadison.OperatorAmplification.matrixInclusion_commutes`, `OAI.Kadison.SeparableTest.seminorm_bound` and `OAI.Kadison.exists_separable_cstar_bicommutant`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C042
import Definitions.Def_OAIQ039C043
import Definitions.Def_OAIQ039C044
import Definitions.Def_OAIQ039C045

section
-- module Solutions.OAIQ039_CM.Commutator_ConcreteCornerVonNeumann
attribute [-instance] _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConcreteCorner

open MatrixCornerHilbert ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

variable {M} {p : Algebra M} (hp : IsStarProjection p)

variable (R : H →L[ℂ] H) (hR : R∈M.commutant)

lemma restrictCommutant_centralizer : restrictCommutant hp R hR ∈
    Set.centralizer (Set.range (representation hp)) := by
  rintro _ ⟨a,rfl⟩
  ext x
  exact congrArg (fun T : H →L[ℂ] H => T (x:H))
    (VonNeumannAlgebra.mem_commutant_iff.mp hR
      ((a:Algebra M):H →L[ℂ] H) (a:Algebra M).property)

include hR in
lemma lift_commutes {T : Space hp →L[ℂ] Space hp}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (representation hp)))) :
    R*lift hp T=lift hp T*R := by
  have he := hT _ (restrictCommutant_centralizer hp R hR)
  ext x
  change R (T (project hp x):H)=(T (project hp (R x)):H)
  rw [project_commutant hp R hR]
  exact congrArg (fun F : Space hp →L[ℂ] Space hp => (F (project hp x):H)) he

lemma lift_mem {T : Space hp →L[ℂ] Space hp}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (representation hp)))) :
    lift hp T∈M := by
  rw [← SetLike.mem_coe,←M.centralizer_centralizer]
  intro R hR
  exact lift_commutes hp R (VonNeumannAlgebra.mem_commutant_iff.mpr hR) hT

lemma corner_bicommutant :
    Set.centralizer (Set.centralizer (Set.range (representation hp)))=
      Set.range (representation hp) := by
  apply Set.Subset.antisymm
  · intro T hT
    let a : Algebra M := ⟨lift hp T,lift_mem hp hT⟩
    let b : Corner hp := ⟨a,Subtype.ext (lift_left hp T),Subtype.ext (lift_right hp T)⟩
    refine ⟨b,?_⟩
    ext x
    change (T (project hp (x:H)):H)=(T x:H)
    rw [project_fixed]
  · intro T hT R hR
    exact (hR T hT).symm

def vonNeumann : VonNeumannAlgebra (Space hp) where
  toStarSubalgebra := (representation hp).range
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.range (representation hp))) =
      Set.range (representation hp)
    exact corner_bicommutant hp

end Kadison.ConcreteCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StandardTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

def trace : (τ.GNS →L[ℂ] τ.GNS) →ₚ[ℂ] ℂ := VectorFunctional.functional (vacuum τ)

@[simp] lemma trace_gns (a : M) : trace M τ (τ.gnsStarAlgHom a)=τ a := by
  change inner ℂ (vacuum τ) (τ.gnsStarAlgHom a (vacuum τ))=τ a
  rw [left_vacuum]
  exact inner_vacuum_algebraVector τ a

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTower
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixTower

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Stage (M : VonNeumannAlgebra H) where
  I : Type
  finite : Fintype I
  dec : DecidableEq I
  nonempty : Nonempty I
  hom : Matrix I I ℂ →⋆ₐ[ℂ] M

attribute [instance] Stage.finite Stage.dec Stage.nonempty

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AbelianGNSSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory

open scoped Topology ComplexOrder

namespace Kadison.CentralSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

instance centerCommCStar : CommCStarAlgebra (CentralCorner.center M) where
  mul_comm a b := Subtype.ext (((CentralCorner.mem_center M a).mp a.property).2 b
    (((CentralCorner.mem_center M b).mp b.property).1)).symm

abbrev Spectrum := WeakDual.characterSpace ℂ (CentralCorner.center M)

instance spectrumMeasurable : MeasurableSpace (Spectrum M) := borel (Spectrum M)

instance spectrumBorel : BorelSpace (Spectrum M) := ⟨rfl⟩

end Kadison.CentralSpectral

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

variable (hr : MulAut.conj d u=u⁻¹)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2 : ℂ) • (1+(d : A)))

@[simp] lemma cosine_star (n : ℤ) : star (cosine u hp n)=cosine u hp (-n) := by
  apply Subtype.ext
  change star (p*wave u n*p)=p*wave u (-n)*p
  simp only [star_mul, hp.isSelfAdjoint.star_eq, wave_star, mul_assoc]

variable (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include hr hpform hdp in
lemma cosine_mul (n m : ℤ) : cosine u hp n*cosine u hp m =
    (1/2 : ℂ) • (cosine u hp (n+m)+cosine u hp (n-m)) := by
  apply Subtype.ext
  change (p*wave u n*p)*(p*wave u m*p)=
    (1/2 : ℂ) •(p*wave u (n+m)*p+p*wave u (n-m)*p)
  calc
    _ = p*wave u n*(p*p)*wave u m*p := by noncomm_ring
    _ = p*wave u n*p*wave u m*p := by rw [hp.isIdempotentElem.eq]
    _ = (1/2 : ℂ) •(p*wave u n*wave u m*p+p*wave u n*(d : A)*wave u m*p) := by
      conv_lhs => arg 1; arg 1; arg 2; rw [hpform]
      simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, mul_assoc]
    _ = (1/2 : ℂ) •(p*wave u (n+m)*p+p*wave u (n-m)*p) := by
      rw [wave_add, sub_eq_add_neg, wave_add]
      apply congrArg ((1/2 : ℂ) • ·)
      apply congrArg₂ (·+·)
      · noncomm_ring
      · calc
          p*wave u n*(d : A)*wave u m*p = p*wave u n*((d : A)*wave u m)*p := by noncomm_ring
          _ = p*wave u n*(wave u (-m)*(d : A))*p := by rw [reflection_wave u d hr m]
          _ = p*(wave u n*wave u (-m))*p := by
            simp only [mul_assoc, hdp]

end Kadison.DihedralCorner

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

def cosineSpace : Submodule ℂ (Corner hp) := Submodule.span ℂ (Set.range (cosine u hp))

lemma cosine_mem (n : ℤ) : cosine u hp n∈cosineSpace u hp :=
  Submodule.subset_span ⟨n,rfl⟩

include hr hpform hdp in
lemma cosineSpace_mul {a b : Corner hp} (ha : a∈cosineSpace u hp) (hb : b∈cosineSpace u hp) :
    a*b∈cosineSpace u hp := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨m,rfl⟩ := hb
      rw [cosine_mul u d hr hp hpform hdp]
      exact (cosineSpace u hp).smul_mem _ ((cosineSpace u hp).add_mem
        (cosine_mem u hp _) (cosine_mem u hp _))
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (cosineSpace u hp).add_mem hb hc
    | smul z b _ hb => simpa only [mul_smul_comm] using (cosineSpace u hp).smul_mem z hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (cosineSpace u hp).add_mem ha hc
  | smul z a _ ha => simpa only [smul_mul_assoc] using (cosineSpace u hp).smul_mem z ha

lemma cosineSpace_star {a : Corner hp} (ha : a∈cosineSpace u hp) : star a∈cosineSpace u hp := by
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨n,rfl⟩ := ha; simpa using cosine_mem u hp (-n)
  | zero => simp
  | add a b _ _ ha hb => simpa only [star_add] using (cosineSpace u hp).add_mem ha hb
  | smul z a _ ha => simpa only [star_smul] using (cosineSpace u hp).smul_mem (star z) ha

def cosineAlgebra : StarSubalgebra ℂ (Corner hp) where
  __ : Subalgebra ℂ (Corner hp) :=
    { __ := cosineSpace u hp
      one_mem' := by simpa using cosine_mem u hp 0
      mul_mem' := cosineSpace_mul u d hr hp hpform hdp
      algebraMap_mem' := fun z => by
        change algebraMap ℂ (Corner hp) z∈cosineSpace u hp
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (cosineSpace u hp).smul_mem z (by simpa using cosine_mem u hp 0) }
  star_mem' := cosineSpace_star u hp

def positiveCosines : Set (Corner hp) := Set.range (fun n : ℕ => cosine u hp (n+1))

end Kadison.DihedralCorner

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

def halfCornerTrace (τ : A →ₗ[ℂ] ℂ) : Corner hp →ₗ[ℂ] ℂ :=
  (2 : ℂ) • τ.comp (cornerSubalgebra hp).toSubmodule.subtype

@[simp] lemma halfCornerTrace_apply (τ : A →ₗ[ℂ] ℂ) (a : Corner hp) :
    halfCornerTrace hp τ a=2*τ (a : A) := rfl

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DihedralFejer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.DihedralCorner

open FreeMoments FejerTest

variable {A : Type*} [CStarAlgebra A]

variable {p : A} (hp : IsStarProjection p)

def compressCorner : A →ₗ[ℂ] Corner hp where
  toFun a := ⟨p*a*p,by constructor <;> simp only [mul_assoc,←mul_assoc p p,hp.isIdempotentElem.eq]⟩
  map_add' a b := by
    apply Subtype.ext
    change p*(a+b)*p=p*a*p+p*b*p
    rw [mul_add,add_mul]
  map_smul' z a := by
    apply Subtype.ext
    change p*(z • a)*p=z • (p*a*p)
    simp only [mul_smul_comm,smul_mul_assoc]

@[simp] lemma compressCorner_coe (a : A) : ((compressCorner hp a:Corner hp):A)=p*a*p := rfl

@[simp] lemma compressCorner_one : compressCorner hp 1=1 := by
  apply Subtype.ext
  change p*1*p=p
  rw [mul_one,hp.isIdempotentElem.eq]

@[simp] lemma compressCorner_wave (u : unitary A) (n : ℤ) :
    compressCorner hp (wave u n)=cosine u hp n := rfl

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StarField
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma operator_adjoint (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    operator μ (fun a => (T a).adjoint) (adjoint_measurable μ T hm hb)
      (adjoint_field_bound μ T hb)=(operator μ T hm hb).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae μ (fun a => (T a).adjoint) (adjoint_measurable μ T hm hb)
    (adjoint_field_bound μ T hb) f,operator_ae μ T hm hb g] with a ha ht
  rw [ha,ht,ContinuousLinearMap.adjoint_inner_left]

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FieldAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma fieldMember_star (Q : Ω → VonNeumannAlgebra H)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A) :
    FieldMember μ Q (star A) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  refine ⟨(fun a => (T a).adjoint),adjoint_measurable μ T hT hb,b,
    adjoint_field_bound μ T hb,hb0,(operator_adjoint μ T hT hb).symm,?_⟩
  filter_upwards [hTm] with a ha
  exact (Q a).star_mem' ha

def fieldAlgebra (Q : Ω → VonNeumannAlgebra H) :
    StarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  carrier := FieldMember μ Q
  zero_mem' := fieldMember_zero μ Q
  one_mem' := fieldMember_one μ Q
  add_mem' := fieldMember_add μ Q
  mul_mem' := fieldMember_mul μ Q
  algebraMap_mem' z := by
    change FieldMember μ Q (algebraMap ℂ _ z)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      fieldMember_smul μ Q z (fieldMember_one μ Q)
  star_mem' := fieldMember_star μ Q

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FieldNormClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma fieldAlgebra_isClosed (Q : Ω → VonNeumannAlgebra H) :
    IsClosed (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := by
  apply isClosed_of_closure_subset
  intro A hA
  have hcomm (s : Set Ω) (hs : MeasurableSet s) : Commute A (indicatorOperator μ s hs) := by
    apply closure_minimal (t:={B : Lp H 2 μ →L[ℂ] Lp H 2 μ |
      B*indicatorOperator μ s hs=indicatorOperator μ s hs*B}) ?_
      (isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)) hA
    intro B hB
    exact fieldMember_commutes_indicator μ Q hB s hs
  obtain ⟨T,hm,hb,he⟩ := exists_field_of_commutes_indicator μ A hcomm
  have hseq (n : ℕ) : ∃ B : Lp H 2 μ →L[ℂ] Lp H 2 μ,
      B∈fieldAlgebra μ Q ∧ ‖B-A‖<1/((n:ℝ)+1) := by
    obtain ⟨B,hB,hd⟩ := Metric.mem_closure_iff.mp hA (1/((n:ℝ)+1)) (by positivity)
    exact ⟨B,hB,by simpa only [dist_eq_norm,norm_sub_rev] using hd⟩
  choose B hB hdist using hseq
  have hBn (n : ℕ) : ‖B n‖≤‖A‖+1 := by
    have heps : 1/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have hnorm := norm_sub_le (B n-A) (-A)
    have hn : ‖B n‖≤‖B n-A‖+‖A‖ := by simpa using hnorm
    linarith [hdist n]
  have hfields (n : ℕ) := fieldMember_tight μ Q (hB n) (by positivity : 0≤‖A‖+1) (hBn n)
  choose S hS hSb hSe hSm using hfields
  have hlimB : Tendsto B atTop (𝓝 A) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [dist_eq_norm]
    apply (hdist n).trans_le
    exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)).trans hN.le
  have hlim (f : Lp H 2 μ) : Tendsto
      (fun n => operator μ (S n) (hS n) (hSb n) f) atTop
      (𝓝 (operator μ T hm hb f)) := by
    have hh : Tendsto (fun n => B n f) atTop (𝓝 (A f)) :=
      (ContinuousLinearMap.apply ℂ (Lp H 2 μ) f).continuous.tendsto A |>.comp hlimB
    simpa only [←hSe,←he] using hh
  exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,
    mem_ae_of_bounded_strong_limit μ Q T hm hb S hS (by positivity) hSb hSm hlim⟩

end Kadison.Decomposable

end

end
end

end OAI
end


