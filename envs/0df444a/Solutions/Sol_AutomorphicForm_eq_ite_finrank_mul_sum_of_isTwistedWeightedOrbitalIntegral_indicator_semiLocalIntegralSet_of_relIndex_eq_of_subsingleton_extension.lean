-- Prove2me | solution 1 for AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/eb9fbe31-6bd5-5858-8b3e-f000acb719c8

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_weight_eq_ite_finrank_mul_sum_of_relIndex_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure TopologicalSpace Function NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mInertEvalGlue

open AutomorphicForm

section Setup

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem liesOver_of_extension (w : v.Extension (𝓞 L)) : w.1.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have h := congrArg HeightOneSpectrum.asIdeal w.2
  exact h.symm

theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨⟨Q, hQmax.isPrime, hQ⟩, ?_⟩⟩
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact hQover.over.symm

def w₀ : v.Extension (𝓞 L) := Classical.choice (nonempty_extension K L v)

def e₁ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v)
    (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v)

theorem e₁_tmul (l : L) (x : v.adicCompletion K) (w : v.Extension (𝓞 L)) :
    e₁ K L v (l ⊗ₜ x) w = algebraMap L (w.1.adicCompletion L) l * algebraMap (v.adicCompletion K) _ x := rfl

theorem mem_semiLocalIntegers_iff (x : L ⊗[K] v.adicCompletion K) :
    x ∈ semiLocalIntegers K L v ↔ ∀ w : v.Extension (𝓞 L), e₁ K L v x w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  rfl

variable (hinert : Subsingleton (v.Extension (𝓞 L)))
include hinert

def Φ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (w₀ K L v).1.adicCompletion L :=
  AlgEquiv.ofBijective
    ((Pi.evalAlgHom (v.adicCompletion K) (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) (w₀ K L v)).comp
      (e₁ K L v).toAlgHom) (by
    constructor
    · intro x y hxy
      apply (e₁ K L v).injective
      funext w'
      have hw' : w' = w₀ K L v := Subsingleton.elim _ _
      subst hw'
      exact hxy
    · intro t
      obtain ⟨f, hf⟩ := Function.surjective_eval
        (β := fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) (w₀ K L v) t
      refine ⟨(e₁ K L v).symm f, ?_⟩
      change e₁ K L v ((e₁ K L v).symm f) (w₀ K L v) = t
      rw [AlgEquiv.apply_symm_apply]
      exact hf)

theorem Φ_apply (x : L ⊗[K] v.adicCompletion K) : Φ K L v hinert x = e₁ K L v x (w₀ K L v) := rfl

theorem Φ_tmul (l : L) (x : v.adicCompletion K) :
    Φ K L v hinert (l ⊗ₜ x) =
      algebraMap L ((w₀ K L v).1.adicCompletion L) l * algebraMap (v.adicCompletion K) _ x := by
  rw [Φ_apply, e₁_tmul]

theorem Φ_one_tmul (x : v.adicCompletion K) :
    Φ K L v hinert ((1 : L) ⊗ₜ x) = algebraMap (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) x := by
  rw [Φ_tmul, map_one, one_mul]

theorem Φ_tmul_one (l : L) :
    Φ K L v hinert (l ⊗ₜ (1 : v.adicCompletion K)) = algebraMap L ((w₀ K L v).1.adicCompletion L) l := by
  rw [Φ_tmul, map_one, mul_one]

theorem mem_semiLocalIntegers_iff_Φ (x : L ⊗[K] v.adicCompletion K) :
    x ∈ semiLocalIntegers K L v ↔ Φ K L v hinert x ∈ (w₀ K L v).1.adicCompletionIntegers L := by
  rw [mem_semiLocalIntegers_iff, Φ_apply]
  constructor
  · intro h; exact h _
  · intro h w
    have hw : w = w₀ K L v := Subsingleton.elim _ _
    subst hw
    exact h

theorem semiLocalPlaceComponent_val (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (p q : Fin 2) :
    ((semiLocalPlaceComponent K L v (w₀ K L v) g : GL (Fin 2) ((w₀ K L v).1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) _) p q = Φ K L v hinert ((g : Matrix (Fin 2) (Fin 2) _) p q) := rfl

variable (σ : L ≃ₐ[K] L)

omit hinert in
theorem sigmaTensor_tmul (l : L) (x : v.adicCompletion K) :
    sigmaTensor K L (v.adicCompletion K) σ (l ⊗ₜ x) = σ l ⊗ₜ x := rfl

def sigmaEquiv : (L ⊗[K] v.adicCompletion K) ≃+* (L ⊗[K] v.adicCompletion K) :=
  (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv

def θ : (w₀ K L v).1.adicCompletion L ≃ₐ[v.adicCompletion K] (w₀ K L v).1.adicCompletion L :=
  { ((Φ K L v hinert).symm.toRingEquiv.trans (sigmaEquiv K L v σ)).trans (Φ K L v hinert).toRingEquiv with
    commutes' := fun x => by
      change Φ K L v hinert (sigmaTensor K L (v.adicCompletion K) σ
        ((Φ K L v hinert).symm (algebraMap (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) x))) = _
      rw [← Φ_one_tmul K L v hinert x, AlgEquiv.symm_apply_apply, sigmaTensor_tmul, map_one, Φ_one_tmul] }

theorem θ_Φ (x : L ⊗[K] v.adicCompletion K) :
    θ K L v hinert σ (Φ K L v hinert x) = Φ K L v hinert (sigmaTensor K L (v.adicCompletion K) σ x) := by
  change Φ K L v hinert (sigmaTensor K L (v.adicCompletion K) σ
    ((Φ K L v hinert).symm (Φ K L v hinert x))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem θ_pow_Φ_iterate (i : ℕ) (x : L ⊗[K] v.adicCompletion K) :
    (θ K L v hinert σ ^ i) (Φ K L v hinert x) =
      Φ K L v hinert ((⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] x) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, θ_Φ, Function.iterate_succ_apply']

theorem θ_pow_Φ_tmul (i : ℕ) (l : L) (x : v.adicCompletion K) :
    (θ K L v hinert σ ^ i) (Φ K L v hinert (l ⊗ₜ x)) = Φ K L v hinert ((σ ^ i) l ⊗ₜ x) := by
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ, AlgEquiv.mul_apply, θ_Φ, sigmaTensor_tmul, ih, pow_succ, AlgEquiv.mul_apply]

theorem θ_algebraMap (l : L) :
    θ K L v hinert σ (algebraMap L ((w₀ K L v).1.adicCompletion L) l) =
      algebraMap L ((w₀ K L v).1.adicCompletion L) (σ l) := by
  rw [← Φ_tmul_one K L v hinert l, θ_Φ, sigmaTensor_tmul, Φ_tmul_one]

variable (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

omit hinert in
include hv in
theorem ramificationIdx_w₀ :
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) (w₀ K L v).1).asIdeal (w₀ K L v).1.asIdeal = 1 :=
  hv _ (w₀ K L v).2

include hv in

theorem finrank_completion :
    Module.finrank (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) = Module.finrank K L := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have hsum := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  rw [Finset.sum_eq_single (w₀ K L v) (fun w' _ hw' => absurd (Subsingleton.elim _ _) hw')
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  rw [← HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L (w₀ K L v)]
  exact hsum

variable (hprime : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
include hprime hσ

theorem θ_pow_finrank : θ K L v hinert σ ^ Module.finrank K L = 1 := by
  obtain ⟨-, hord, -⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (Φ K L v hinert).surjective y
  rw [AlgEquiv.one_apply]
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul l x => rw [θ_pow_Φ_tmul, ← hord, pow_orderOf_eq_one, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem θ_ne_one : θ K L v hinert σ ≠ 1 := by
  intro h
  apply hσ
  refine AlgEquiv.ext fun l => ?_
  have h1 := θ_algebraMap K L v hinert σ l
  rw [h, AlgEquiv.one_apply] at h1
  exact ((algebraMap L ((w₀ K L v).1.adicCompletion L)).injective h1).symm

theorem orderOf_θ : orderOf (θ K L v hinert σ) = Module.finrank K L := by
  haveI : Fact (Module.finrank K L).Prime := ⟨hprime⟩
  exact orderOf_eq_prime (θ_pow_finrank K L v hinert σ hprime hσ) (θ_ne_one K L v hinert σ hprime hσ)

end Setup

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

abbrev sigmaUnits : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ :=
  Units.map (sigmaTensor K L A σ).toMonoidHom

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    sigmaGL K L A σ (diagUnits2 x y) = diagUnits2 (sigmaUnits K L A σ x) (sigmaUnits K L A σ y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change sigmaTensor K L A σ ((diagUnits2 x y : GL (Fin 2) (L ⊗[K] A)) i j) = _
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] A)ˣ) :
    (⇑(sigmaGL K L A σ))^[i] (diagUnits2 x y) =
      diagUnits2 ((⇑(sigmaUnits K L A σ))^[i] x) ((⇑(sigmaUnits K L A σ))^[i] y) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
        Function.iterate_succ_apply']

theorem diagUnits2_mul (x y x' y' : (L ⊗[K] A)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_one : (diagUnits2 1 1 : GL (Fin 2) (L ⊗[K] A)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem list_prod_map_diagUnits2 (n : ℕ) (f g : ℕ → (L ⊗[K] A)ˣ) :
    ((List.range n).map fun i => diagUnits2 (f i) (g i)).prod =
      diagUnits2 (∏ i ∈ Finset.range n, f i) (∏ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simp [diagUnits2_one]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_singleton,
        diagUnits2_mul, Finset.prod_range_succ, Finset.prod_range_succ]

def unitNorm (u : (L ⊗[K] A)ˣ) : (L ⊗[K] A)ˣ :=
  ∏ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaUnits K L A σ))^[i] u

theorem normString_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    normString K L A σ (diagUnits2 x y) = diagUnits2 (unitNorm K L A σ x) (unitNorm K L A σ y) := by
  unfold normString unitNorm
  rw [show ((List.range (Module.finrank K L)).map fun i =>
        (⇑(sigmaGL K L A σ))^[i] (diagUnits2 x y)) =
      (List.range (Module.finrank K L)).map fun i =>
        diagUnits2 ((⇑(sigmaUnits K L A σ))^[i] x) ((⇑(sigmaUnits K L A σ))^[i] y) from
      List.map_congr_left fun i _ => sigmaGL_iterate_diagUnits2 K L A σ i x y,
    list_prod_map_diagUnits2]

theorem coe_iterate_sigmaUnits (i : ℕ) (u : (L ⊗[K] A)ˣ) :
    (((⇑(sigmaUnits K L A σ))^[i] u : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      (⇑(sigmaTensor K L A σ))^[i] (u : L ⊗[K] A) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl

theorem coe_unitNorm (u : (L ⊗[K] A)ˣ) :
    ((unitNorm K L A σ u : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      ∏ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaTensor K L A σ))^[i] (u : L ⊗[K] A) := by
  unfold unitNorm
  rw [Units.coe_prod]
  exact Finset.prod_congr rfl fun i _ => coe_iterate_sigmaUnits K L A σ i u

theorem toTensorGL_diagUnits2 (a b : Aˣ) :
    toTensorGL K L A (diagUnits2 a b) =
      diagUnits2 (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toMonoidHom a)
        (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toMonoidHom b) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ((diagUnits2 a b : GL (Fin 2) A) i j) = _
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem diagUnits2_injective {x y x' y' : (L ⊗[K] A)ˣ} (h : diagUnits2 x y = diagUnits2 x' y') :
    x = x' ∧ y = y' := by
  have h00 := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) h
  have h11 := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h11
  exact ⟨Units.ext h00, Units.ext h11⟩

theorem prod_iterate_sigmaTensor_eq (α β : (L ⊗[K] A)ˣ) (a b : Aˣ)
    (hN : normString K L A σ (diagUnits2 α β) = toTensorGL K L A (diagUnits2 a b)) :
    (∏ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaTensor K L A σ))^[i] (α : L ⊗[K] A)) =
        (1 : L) ⊗ₜ[K] (a : A) ∧
      (∏ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaTensor K L A σ))^[i] (β : L ⊗[K] A)) =
        (1 : L) ⊗ₜ[K] (b : A) := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2] at hN
  obtain ⟨hα, hβ⟩ := diagUnits2_injective K L A hN
  constructor
  · rw [← coe_unitNorm, hα]; rfl
  · rw [← coe_unitNorm, hβ]; rfl

end NormString

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel AutomorphicForm.isTopologicalRing_tensor
  AutomorphicForm.localGLBorel

section Topology

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem borelSpace_GL : BorelSpace (GL (Fin 2) R) := ⟨rfl⟩

theorem borelSpace_centralizer (γ : GL (Fin 2) R) :
    BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))) := ⟨rfl⟩

theorem t2Space_GL [T2Space R] : T2Space (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology R] :
    SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space R] [LocallyCompactSpace R] :
    LocallyCompactSpace (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → R))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

attribute [local instance] borelSpace_GL borelSpace_centralizer t2Space_GL secondCountableTopology_GL
  locallyCompactSpace_GL

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L)

theorem borelSpace_twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩

theorem t2Space_tensor' [T2Space A] : T2Space (L ⊗[K] A) := t2Space_tensor K L A

theorem locallyCompactSpace_tensor' [T2Space A] [LocallyCompactSpace A] : LocallyCompactSpace (L ⊗[K] A) :=
  locallyCompactSpace_tensor K L A

end TensorTopology

attribute [local instance] borelSpace_twistedCentralizer t2Space_tensor' locallyCompactSpace_tensor'

section GLPhi

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L))) (σ : L ≃ₐ[K] L)

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val (w₀ K L v))

theorem continuous_Φ : Continuous (Φ K L v hinert) := by
  haveI : ContinuousAdd (L ⊗[K] Kv) := IsModuleTopology.toContinuousAdd Kv _
  exact IsModuleTopology.continuous_of_linearMap (Φ K L v hinert).toLinearEquiv.toLinearMap

theorem continuous_Φ_symm : Continuous (Φ K L v hinert).symm := by
  exact IsModuleTopology.continuous_of_linearMap (Φ K L v hinert).symm.toLinearEquiv.toLinearMap

def matPhi : Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv) ≃ₜ* Matrix (Fin 2) (Fin 2) Lw :=
  { (Φ K L v hinert).toRingEquiv.mapMatrix.toMulEquiv with
    continuous_toFun := by
      refine continuous_pi fun p => continuous_pi fun q => ?_
      exact (continuous_Φ K L v hinert).comp ((continuous_apply q).comp (continuous_apply p))
    continuous_invFun := by
      refine continuous_pi fun p => continuous_pi fun q => ?_
      exact (continuous_Φ_symm K L v hinert).comp ((continuous_apply q).comp (continuous_apply p)) }

def glPhi : GL (Fin 2) (L ⊗[K] Kv) ≃ₜ* GL (Fin 2) Lw :=
  Units.mapContinuousMulEquiv (matPhi K L v hinert)

theorem glPhi_val (g : GL (Fin 2) (L ⊗[K] Kv)) (p q : Fin 2) :
    ((glPhi K L v hinert g : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) p q =
      Φ K L v hinert ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv)) p q) := rfl

theorem glPhi_symm_val (g : GL (Fin 2) Lw) (p q : Fin 2) :
    (((glPhi K L v hinert).symm g : GL (Fin 2) (L ⊗[K] Kv)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv)) p q =
      (Φ K L v hinert).symm ((g : Matrix (Fin 2) (Fin 2) Lw) p q) := rfl

abbrev thetaGL : GL (Fin 2) Lw →* GL (Fin 2) Lw :=
  Matrix.GeneralLinearGroup.map (θ K L v hinert σ).toAlgHom.toRingHom

theorem glPhi_sigmaGL (g : GL (Fin 2) (L ⊗[K] Kv)) :
    glPhi K L v hinert (sigmaGL K L Kv σ g) = thetaGL K L v hinert σ (glPhi K L v hinert g) := by
  ext p q
  rw [glPhi_val, Matrix.GeneralLinearGroup.map_apply, glPhi_val]
  change Φ K L v hinert (sigmaTensor K L Kv σ ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv)) p q)) = _
  rw [← θ_Φ]
  rfl

theorem glPhi_toTensorGL (γ : GL (Fin 2) Kv) :
    glPhi K L v hinert (toTensorGL K L Kv γ) =
      Matrix.GeneralLinearGroup.map (algebraMap Kv Lw) γ := by
  ext p q
  rw [glPhi_val, Matrix.GeneralLinearGroup.map_apply]
  change Φ K L v hinert ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) Kv) p q)) = _
  rw [Φ_one_tmul]

theorem glPhi_comp_toTensorGL :
    (glPhi K L v hinert).toMonoidHom.comp (toTensorGL K L Kv) =
      Matrix.GeneralLinearGroup.map (algebraMap Kv Lw) :=
  MonoidHom.ext fun γ => glPhi_toTensorGL K L v hinert γ

theorem semiLocalPlaceComponent_eq (g : GL (Fin 2) (L ⊗[K] Kv)) :
    semiLocalPlaceComponent K L v (w₀ K L v) g = glPhi K L v hinert g := by
  ext p q
  rfl

theorem mem_semiLocalIntegralSet_iff (g : GL (Fin 2) (L ⊗[K] Kv)) :
    g ∈ semiLocalIntegralSet K L v ↔ glPhi K L v hinert g ∈ localIntegralSet L (w₀ K L v).1 := by
  rw [semiLocalIntegralSet, mem_integralUnitsSet, mem_localIntegralSet, ← map_inv]
  simp only [glPhi_val]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p q => (mem_semiLocalIntegers_iff_Φ K L v hinert _).1 (h1 p q),
      fun p q => (mem_semiLocalIntegers_iff_Φ K L v hinert _).1 (h2 p q)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p q => (mem_semiLocalIntegers_iff_Φ K L v hinert _).2 (h1 p q),
      fun p q => (mem_semiLocalIntegers_iff_Φ K L v hinert _).2 (h2 p q)⟩

theorem semiLocalWeight_eq (g : GL (Fin 2) (L ⊗[K] Kv)) :
    semiLocalWeight K L v g = LocalWeight.weight (glPhi K L v hinert g) := by
  haveI : Unique (v.Extension (𝓞 L)) := ⟨⟨w₀ K L v⟩, fun w => Subsingleton.elim _ _⟩
  unfold semiLocalWeight
  rw [finsum_unique]
  have hdef : (default : v.Extension (𝓞 L)) = w₀ K L v := Subsingleton.elim _ _
  rw [hdef, semiLocalPlaceComponent_eq K L v hinert]

scoped instance : (localHaar L (w₀ K L v).1).IsHaarMeasure := isHaarMeasure_localHaar L (w₀ K L v).1

scoped instance : (semiLocalHaar K L v).IsHaarMeasure := isHaarMeasure_semiLocalHaar K L v

theorem map_glPhi_semiLocalHaar :
    Measure.map (glPhi K L v hinert) (semiLocalHaar K L v) = localHaar L (w₀ K L v).1 := by
  haveI h1 : (Measure.map (glPhi K L v hinert) (semiLocalHaar K L v)).IsHaarMeasure :=
    (glPhi K L v hinert).isHaarMeasure_map (semiLocalHaar K L v)
  have hK₁ : Measure.map (glPhi K L v hinert) (semiLocalHaar K L v) (localIntegralCompacts L (w₀ K L v).1) = 1 := by
    have hme : Measurable (glPhi K L v hinert : GL (Fin 2) (L ⊗[K] Kv) → GL (Fin 2) Lw) :=
      (glPhi K L v hinert).continuous.measurable
    rw [Measure.map_apply hme (localIntegralCompacts L (w₀ K L v).1).isCompact.measurableSet]
    have hpre : (glPhi K L v hinert) ⁻¹' (localIntegralCompacts L (w₀ K L v).1 : Set (GL (Fin 2) Lw)) =
        semiLocalIntegralSet K L v := by
      ext g
      rw [Set.mem_preimage, coe_localIntegralCompacts]
      exact (mem_semiLocalIntegralSet_iff K L v hinert g).symm
    rw [hpre, semiLocalHaar_semiLocalIntegralSet]
  have hK₂ : localHaar L (w₀ K L v).1 (localIntegralCompacts L (w₀ K L v).1) = 1 :=
    localHaar_localIntegralSet L (w₀ K L v).1
  rw [haarMeasure_unique (Measure.map (glPhi K L v hinert) (semiLocalHaar K L v)) (localIntegralCompacts L (w₀ K L v).1),
    haarMeasure_unique (localHaar L (w₀ K L v).1) (localIntegralCompacts L (w₀ K L v).1), hK₁, hK₂]

variable (α β : (L ⊗[K] HeightOneSpectrum.adicCompletion K v)ˣ)

theorem glPhi_diagUnits2 :
    glPhi K L v hinert (diagUnits2 α β) =
      diagUnits2 (Units.map (Φ K L v hinert).toRingEquiv.toRingHom.toMonoidHom α)
        (Units.map (Φ K L v hinert).toRingEquiv.toRingHom.toMonoidHom β) := by
  ext p q
  rw [glPhi_val]
  fin_cases p <;> fin_cases q <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem sigmaCentralizer_eq_map :
    sigmaCentralizer (thetaGL K L v hinert σ) (glPhi K L v hinert (diagUnits2 α β)) =
      (twistedCentralizer K L Kv σ (diagUnits2 α β)).map (glPhi K L v hinert).toMonoidHom := by
  ext t'
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨(glPhi K L v hinert).symm t', ?_, (glPhi K L v hinert).apply_symm_apply t'⟩
    rw [twistedCentralizer, mem_sigmaCentralizer_iff]
    apply (glPhi K L v hinert).injective
    rw [map_mul, map_mul, map_inv, glPhi_sigmaGL, ContinuousMulEquiv.apply_symm_apply]
    exact h
  · rintro ⟨t, ht, rfl⟩
    rw [twistedCentralizer, mem_sigmaCentralizer_iff] at ht
    have h := congrArg (glPhi K L v hinert) ht
    rw [map_mul, map_mul, map_inv, glPhi_sigmaGL] at h
    exact h

end GLPhi

section TorusTransport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L)))

def torusEquivE (T' : Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (TE : Subgroup (GL (Fin 2) ((w₀ K L v).1.adicCompletion L)))
    (h : TE = T'.map (glPhi K L v hinert).toMonoidHom) : T' ≃ₜ* TE :=
  { toFun := fun t => ⟨glPhi K L v hinert (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (SetLike.ext_iff.1 h _).2 (Subgroup.mem_map_of_mem (glPhi K L v hinert).toMonoidHom t.2)⟩
    invFun := fun t' => ⟨(glPhi K L v hinert).symm (t' : GL (Fin 2) ((w₀ K L v).1.adicCompletion L)),
      Exists.elim (Subgroup.mem_map.1 ((SetLike.ext_iff.1 h _).1 t'.2)) fun t ht =>
        ht.2 ▸ ((glPhi K L v hinert).symm_apply_apply t).symm ▸ ht.1⟩
    left_inv := fun t => Subtype.ext ((glPhi K L v hinert).symm_apply_apply _)
    right_inv := fun t' => Subtype.ext ((glPhi K L v hinert).apply_symm_apply _)
    map_mul' := fun s t => Subtype.ext (map_mul (glPhi K L v hinert) _ _)
    continuous_toFun := Continuous.subtype_mk ((glPhi K L v hinert).continuous.comp continuous_subtype_val) _
    continuous_invFun :=
      Continuous.subtype_mk ((glPhi K L v hinert).symm.continuous.comp continuous_subtype_val) _ }

theorem torusEquivE_apply_val (T' : Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (TE : Subgroup (GL (Fin 2) ((w₀ K L v).1.adicCompletion L)))
    (h : TE = T'.map (glPhi K L v hinert).toMonoidHom) (t : T') :
    ((torusEquivE K L v hinert T' TE h t : TE) : GL (Fin 2) ((w₀ K L v).1.adicCompletion L)) =
      glPhi K L v hinert (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  rfl

end TorusTransport

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L))) (σ : L ≃ₐ[K] L)
  (hprime : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
  (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val (w₀ K L v))

theorem relIndex_comap_comap {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G' →+ G)
    (hf : Function.Surjective f) (H K' : AddSubgroup G) :
    (H.comap f).relIndex (K'.comap f) = H.relIndex K' := by
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf]

include hinert in

theorem O_eq_comap :
    (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup =
      ((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
        (Φ K L v hinert).toAlgHom.toRingHom.toAddMonoidHom := by
  ext x
  exact mem_semiLocalIntegers_iff_Φ K L v hinert x

include hinert in
theorem Λ_eq_comap (c : L ⊗[K] Kv) :
    ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
        ((sigmaTensor K L Kv σ).toAddMonoidHom - AddMonoidHom.mulLeft c)) =
      ((((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
          ((θ K L v hinert σ).toAlgHom.toRingHom.toAddMonoidHom -
            AddMonoidHom.mulLeft (Φ K L v hinert c))).comap
        (Φ K L v hinert).toAlgHom.toRingHom.toAddMonoidHom) := by
  ext x
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, AddSubgroup.mem_comap]
  change sigmaTensor K L Kv σ x - c * x ∈ semiLocalIntegers K L v ↔
    θ K L v hinert σ (Φ K L v hinert x) - Φ K L v hinert c * Φ K L v hinert x ∈ (w₀ K L v).1.adicCompletionIntegers L
  rw [mem_semiLocalIntegers_iff_Φ K L v hinert, map_sub, map_mul, θ_Φ]

include hinert in
theorem B_eq_comap (ϖ : Kv) (s : ℕ) :
    ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
        (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s)))) =
      ((((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
          (AddMonoidHom.mulLeft (algebraMap Kv Lw (ϖ ^ s)))).comap
        (Φ K L v hinert).toAlgHom.toRingHom.toAddMonoidHom) := by
  ext x
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, AddSubgroup.mem_comap]
  change ((1 : L) ⊗ₜ[K] (ϖ ^ s)) * x ∈ semiLocalIntegers K L v ↔
    algebraMap Kv Lw (ϖ ^ s) * Φ K L v hinert x ∈ (w₀ K L v).1.adicCompletionIntegers L
  rw [mem_semiLocalIntegers_iff_Φ K L v hinert, map_mul, Φ_one_tmul]

set_option maxHeartbeats 16000000 in
include hinert hprime hσ hv in
theorem main (a b : Kvˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : Kv) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (L ⊗[K] Kv)ˣ)
    (hN : normString K L Kv σ (diagUnits2 α β) = toTensorGL K L Kv (diagUnits2 a b))
    (hT : twistedCentralizer K L Kv σ (diagUnits2 α β) =
      (localCentralizer K v (diagUnits2 a b)).map (toTensorGL K L Kv))
    (hidx : ‖(a : Kv)‖ = 1 → ‖(b : Kv)‖ = 1 →
      ∀ ϖ : Kv, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.relIndex
            (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L)
                    v).range.toSubring.toAddSubgroup.comap
                ((sigmaTensor K L Kv σ).toAddMonoidHom -
                  AddMonoidHom.mulLeft ((β * α⁻¹ : (L ⊗[K] Kv)ˣ) : L ⊗[K] Kv))) ⊓
              ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L)
                    v).range.toSubring.toAddSubgroup.comap
                (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s m.toNat)
    (τ' : Measure (twistedCentralizer K L Kv σ (diagUnits2 α β))) [τ'.IsHaarMeasure]
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] Kv)) ∈ semiLocalIntegralSet K L v} = 1)
    (J' : ℂ)
    (hJ' : IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) J') :
    J' = if ‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1 then
        (Module.finrank K L : ℂ) *
          (((2 * Real.log (Ideal.absNorm v.asIdeal) *
              ∑ s ∈ Finset.range (m.toNat + 1),
                (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                  (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0 := by

  set Ψ := glPhi K L v hinert with hΨ
  set α' : Lwˣ := Units.map (Φ K L v hinert).toRingEquiv.toRingHom.toMonoidHom α with hα'
  set β' : Lwˣ := Units.map (Φ K L v hinert).toRingEquiv.toRingHom.toMonoidHom β with hβ'
  have hδ'eq : Ψ (diagUnits2 α β) = diagUnits2 α' β' := glPhi_diagUnits2 K L v hinert α β
  have hdeg := finrank_completion K L v hinert hv
  have hw := ramificationIdx_w₀ K L v hv
  have hθord : orderOf (θ K L v hinert σ) = Module.finrank Kv Lw := by
    rw [hdeg]; exact orderOf_θ K L v hinert σ hprime hσ

  obtain ⟨hNa, hNb⟩ := prod_iterate_sigmaTensor_eq K L Kv σ α β a b hN
  have hNα : ∏ i ∈ Finset.range (Module.finrank Kv Lw), ((θ K L v hinert σ) ^ i) (α' : Lw) = algebraMap Kv Lw a := by
    rw [hdeg]
    change ∏ i ∈ Finset.range (Module.finrank K L), (θ K L v hinert σ ^ i) (Φ K L v hinert (α : L ⊗[K] Kv)) = _
    simp_rw [θ_pow_Φ_iterate]
    rw [← map_prod, hNa, Φ_one_tmul]
  have hNβ : ∏ i ∈ Finset.range (Module.finrank Kv Lw), ((θ K L v hinert σ) ^ i) (β' : Lw) = algebraMap Kv Lw b := by
    rw [hdeg]
    change ∏ i ∈ Finset.range (Module.finrank K L), (θ K L v hinert σ ^ i) (Φ K L v hinert (β : L ⊗[K] Kv)) = _
    simp_rw [θ_pow_Φ_iterate]
    rw [← map_prod, hNb, Φ_one_tmul]

  set TE := sigmaCentralizer (thetaGL K L v hinert σ) (diagUnits2 α' β') with hTEdef
  have hTEmap : TE = (twistedCentralizer K L Kv σ (diagUnits2 α β)).map Ψ.toMonoidHom := by
    rw [hTEdef, ← hδ'eq, hΨ, sigmaCentralizer_eq_map]
  have hTE : TE = (localCentralizer K v (diagUnits2 a b)).map (Matrix.GeneralLinearGroup.map (algebraMap Kv Lw)) := by
    rw [hTEmap]
    change (twistedCentralizer K L Kv σ (diagUnits2 α β)).map (glPhi K L v hinert).toMonoidHom = _
    rw [hT, Subgroup.map_map, glPhi_comp_toTensorGL]

  letI : MeasurableSpace TE := borel _
  haveI : BorelSpace TE := ⟨rfl⟩
  set eT := torusEquivE K L v hinert (twistedCentralizer K L Kv σ (diagUnits2 α β)) TE hTEmap with heTdef
  have heT_val : ∀ t : (twistedCentralizer K L Kv σ (diagUnits2 α β)), ((eT t : TE) : GL (Fin 2) Lw) = Ψ (t : GL (Fin 2) (L ⊗[K] Kv)) := fun t => rfl
  set τE : Measure TE := Measure.map eT τ' with hτEdef
  haveI hτE : τE.IsHaarMeasure := eT.isHaarMeasure_map τ'
  have hτE1 : τE {t | (t : GL (Fin 2) Lw) ∈ localIntegralSet L (w₀ K L v).1} = 1 := by
    have hmeas : MeasurableSet {t : TE | (t : GL (Fin 2) Lw) ∈ localIntegralSet L (w₀ K L v).1} :=
      (isOpen_localIntegralSet L (w₀ K L v).1).measurableSet.preimage continuous_subtype_val.measurable
    have hme : Measurable (eT : (twistedCentralizer K L Kv σ (diagUnits2 α β)) → TE) := eT.continuous.measurable
    rw [hτEdef, Measure.map_apply hme hmeas, ← hτ'1]
    congr 1
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, heT_val]
    exact (mem_semiLocalIntegralSet_iff K L v hinert _).symm

  have hidxE : ‖(a : Kv)‖ = 1 → ‖(b : Kv)‖ = 1 → ∀ ϖ : Kv, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
      ((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.relIndex
          ((((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
              ((θ K L v hinert σ).toAlgHom.toRingHom.toAddMonoidHom -
                AddMonoidHom.mulLeft ((β' * α'⁻¹ : Lwˣ) : Lw))) ⊓
            (((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
              (AddMonoidHom.mulLeft (algebraMap Kv Lw (ϖ ^ s))))) =
        Ideal.absNorm v.asIdeal ^ min s m.toNat := by
    intro ha hb ϖ hϖ s
    have h := hidx ha hb ϖ hϖ s
    have hc : ((β' * α'⁻¹ : Lwˣ) : Lw) = Φ K L v hinert ((β * α⁻¹ : (L ⊗[K] Kv)ˣ) : L ⊗[K] Kv) := by
      rw [hα', hβ', ← map_inv, ← map_mul]; rfl
    rw [Λ_eq_comap K L v hinert σ, B_eq_comap K L v hinert, O_eq_comap K L v hinert, ← AddSubgroup.comap_inf,
      relIndex_comap_comap _ (Φ K L v hinert).surjective, ← hc] at h
    exact h

  obtain ⟨w', ⟨hw'0, hw'm, hw'c, hw'sec⟩, rfl⟩ := hJ'
  set sE : GL (Fin 2) Lw → ℝ := fun y => w' (Ψ.symm y) with hsE
  have hsE0 : ∀ y, 0 ≤ sE y := fun y => hw'0 _
  have hsEm : Measurable sE := hw'm.comp Ψ.symm.continuous.measurable
  have hsEc : HasCompactSupport sE := by
    refine HasCompactSupport.intro (hw'c.image Ψ.continuous) fun y hy => ?_
    by_contra hne
    apply hy
    exact ⟨Ψ.symm y, subset_tsupport _ (Function.mem_support.2 hne), Ψ.apply_symm_apply y⟩
  have hconj : ∀ x : GL (Fin 2) (L ⊗[K] Kv),
      Ψ (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x) =
        (Ψ x)⁻¹ * diagUnits2 α' β' * thetaGL K L v hinert σ (Ψ x) := by
    intro x
    rw [map_mul, map_mul, map_inv, hδ'eq, hΨ, glPhi_sigmaGL]
  have hsupp : ∀ x : GL (Fin 2) (L ⊗[K] Kv),
      x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x ∈ semiLocalIntegralSet K L v ↔
        (Ψ x)⁻¹ * diagUnits2 α' β' * thetaGL K L v hinert σ (Ψ x) ∈ localIntegralSet L (w₀ K L v).1 := by
    intro x
    rw [mem_semiLocalIntegralSet_iff K L v hinert, ← hΨ, hconj]
  have hsE1 : ∀ y : GL (Fin 2) Lw,
      y⁻¹ * diagUnits2 α' β' * Matrix.GeneralLinearGroup.map (θ K L v hinert σ).toAlgHom.toRingHom y ∈
          localIntegralSet L (w₀ K L v).1 →
        ∫ t : TE, sE ((t : GL (Fin 2) Lw) * y) ∂τE = 1 := by
    intro y hy
    set x := Ψ.symm y with hx
    have hΨx : Ψ x = y := Ψ.apply_symm_apply y
    have hx' : x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x ∈ semiLocalIntegralSet K L v := by
      rw [hsupp, hΨx]; exact hy
    have hne : (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
        (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x) ≠ 0 := by
      rw [Set.indicator_of_mem hx']; exact one_ne_zero
    have hsec := hw'sec x hne
    have htr : ∀ t : (twistedCentralizer K L Kv σ (diagUnits2 α β)), sE ((eT t : GL (Fin 2) Lw) * y) = w' ((t : GL (Fin 2) (L ⊗[K] Kv)) * x) := by
      intro t
      rw [hsE, heT_val]
      simp only []
      congr 1
      apply Ψ.injective
      rw [Ψ.apply_symm_apply, map_mul, hΨx]
    have h := integral_map_equiv (μ := τ') eT.toHomeomorph.toMeasurableEquiv
      (fun t' : TE => sE ((t' : GL (Fin 2) Lw) * y))
    change ∫ t', sE ((t' : GL (Fin 2) Lw) * y) ∂(Measure.map (eT.toHomeomorph.toMeasurableEquiv) τ') = 1
    rw [h]
    change ∫ t : (twistedCentralizer K L Kv σ (diagUnits2 α β)), sE ((eT t : GL (Fin 2) Lw) * y) ∂τ' = 1
    simp_rw [htr]
    exact hsec

  have hE := AutomorphicForm.integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_weight_eq_ite_finrank_mul_sum_of_relIndex_eq
    K L v (w₀ K L v) hw (θ K L v hinert σ) hθord a b hab m hm α' β' hNα hNβ hTE hidxE
    τE hτE hτE1 sE hsE0 hsEm hsEc hsE1

  set FE : GL (Fin 2) Lw → ℂ := fun y =>
    (localIntegralSet L (w₀ K L v).1).indicator (fun _ => (1 : ℂ))
        (y⁻¹ * diagUnits2 α' β' * Matrix.GeneralLinearGroup.map (θ K L v hinert σ).toAlgHom.toRingHom y) *
      ((LocalWeight.weight y : ℝ) : ℂ) * (sE y : ℂ) with hFE
  have hint : (fun x : GL (Fin 2) (L ⊗[K] Kv) =>
      (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x) *
        (semiLocalWeight K L v x : ℂ) * (w' x : ℂ)) = fun x => FE (Ψ x) := by
    funext x
    simp only [hFE]
    congr 2
    · have hiff := hsupp x
      by_cases hx : x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x ∈ semiLocalIntegralSet K L v
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.1 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.2 h))]
    · rw [semiLocalWeight_eq K L v hinert]
    · rw [hsE]
      simp only []
      rw [Ψ.symm_apply_apply]
  have htrans : ∫ x, FE (Ψ x) ∂(semiLocalHaar K L v) = ∫ y, FE y ∂(localHaar L (w₀ K L v).1) := by
    rw [← map_glPhi_semiLocalHaar K L v hinert, ← hΨ]
    exact (integral_map_equiv Ψ.toHomeomorph.toMeasurableEquiv FE).symm
  change ∫ x, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x) *
      (semiLocalWeight K L v x : ℂ) * (w' x : ℂ) ∂(semiLocalHaar K L v) = _
  rw [hint, htrans, hFE, hE, hdeg]

end Main

end P2mInertEvalGlue
p2m_reactivate "P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension.P2mInertEvalGlue"

end
p2m_reactivate "P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension.P2mInertEvalGlue"

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L)))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (hT : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (AutomorphicForm.toTensorGL K L (v.adicCompletion K)))
    (hidx : ‖(a : v.adicCompletion K)‖ = 1 → ‖(b : v.adicCompletion K)‖ = 1 →
      ∀ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.relIndex
            (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L)
                    v).range.toSubring.toAddSubgroup.comap
                ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toAddMonoidHom -
                  AddMonoidHom.mulLeft
                    ((β * α⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))) ⊓
              ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L)
                    v).range.toSubring.toAddSubgroup.comap
                (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s m.toNat)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (J' : ℂ)
    (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) J') :
    J' = if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (Module.finrank K L : ℂ) *
          (((2 * Real.log (Ideal.absNorm v.asIdeal) *
              ∑ s ∈ Finset.range (m.toNat + 1),
                (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                  (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0 := by
  haveI := hτ'
  exact P2mInertEvalGlue.main K L v hinert σ hprime hσ hv a b hab m hm α β hN hT hidx τ' hτ'1 J' hJ'

end S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension
end P2MW
export P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension (solution)
