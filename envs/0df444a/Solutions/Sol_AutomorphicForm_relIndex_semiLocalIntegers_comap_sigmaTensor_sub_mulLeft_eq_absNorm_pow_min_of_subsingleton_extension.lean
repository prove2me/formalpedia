-- Prove2me | solution 1 for AutomorphicForm.relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e256edda-2445-58ff-bc14-47f0aa1682f5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mInertIndex

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

open scoped TensorProduct.RightActions in

def e₁ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v)
    (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v)

open scoped TensorProduct.RightActions in
theorem e₁_tmul (l : L) (x : v.adicCompletion K) (w : v.Extension (𝓞 L)) :
    e₁ K L v (l ⊗ₜ x) w = algebraMap L (w.1.adicCompletion L) l * algebraMap (v.adicCompletion K) _ x := rfl

open scoped TensorProduct.RightActions in
theorem mem_semiLocalIntegers_iff (x : L ⊗[K] v.adicCompletion K) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), e₁ K L v x w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  rfl

variable (hinert : Subsingleton (v.Extension (𝓞 L)))
include hinert

open scoped TensorProduct.RightActions in

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

open scoped TensorProduct.RightActions in
theorem Φ_apply (x : L ⊗[K] v.adicCompletion K) : Φ K L v hinert x = e₁ K L v x (w₀ K L v) := rfl

open scoped TensorProduct.RightActions in
theorem Φ_tmul (l : L) (x : v.adicCompletion K) :
    Φ K L v hinert (l ⊗ₜ x) =
      algebraMap L ((w₀ K L v).1.adicCompletion L) l * algebraMap (v.adicCompletion K) _ x := by
  rw [Φ_apply, e₁_tmul]

open scoped TensorProduct.RightActions in
theorem Φ_one_tmul (x : v.adicCompletion K) :
    Φ K L v hinert ((1 : L) ⊗ₜ x) = algebraMap (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) x := by
  rw [Φ_tmul, map_one, one_mul]

open scoped TensorProduct.RightActions in
theorem Φ_tmul_one (l : L) :
    Φ K L v hinert (l ⊗ₜ (1 : v.adicCompletion K)) = algebraMap L ((w₀ K L v).1.adicCompletion L) l := by
  rw [Φ_tmul, map_one, mul_one]

open scoped TensorProduct.RightActions in

theorem mem_semiLocalIntegers_iff_Φ (x : L ⊗[K] v.adicCompletion K) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ Φ K L v hinert x ∈ (w₀ K L v).1.adicCompletionIntegers L := by
  rw [mem_semiLocalIntegers_iff, Φ_apply]
  constructor
  · intro h; exact h _
  · intro h w
    have hw : w = w₀ K L v := Subsingleton.elim _ _
    subst hw
    exact h

end Setup

section Theta

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L))) (σ : L ≃ₐ[K] L)

open scoped TensorProduct.RightActions in

def sigmaEquiv : (L ⊗[K] v.adicCompletion K) ≃+* (L ⊗[K] v.adicCompletion K) :=
  (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv

open scoped TensorProduct.RightActions in
theorem sigmaEquiv_apply (x : L ⊗[K] v.adicCompletion K) :
    sigmaEquiv K L v σ x = AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x := rfl

open scoped TensorProduct.RightActions in
theorem sigmaTensor_tmul (l : L) (x : v.adicCompletion K) :
    AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (l ⊗ₜ x) = σ l ⊗ₜ x := rfl

include hinert

open scoped TensorProduct.RightActions in

def θ : (w₀ K L v).1.adicCompletion L ≃ₐ[v.adicCompletion K] (w₀ K L v).1.adicCompletion L :=
  { ((Φ K L v hinert).symm.toRingEquiv.trans (sigmaEquiv K L v σ)).trans (Φ K L v hinert).toRingEquiv with
    commutes' := fun x => by
      change Φ K L v hinert (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ
        ((Φ K L v hinert).symm (algebraMap (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) x))) = _
      rw [← Φ_one_tmul K L v hinert x, AlgEquiv.symm_apply_apply, sigmaTensor_tmul, map_one, Φ_one_tmul] }

open scoped TensorProduct.RightActions in
theorem θ_Φ (x : L ⊗[K] v.adicCompletion K) :
    θ K L v hinert σ (Φ K L v hinert x) = Φ K L v hinert (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x) := by
  change Φ K L v hinert (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ
    ((Φ K L v hinert).symm (Φ K L v hinert x))) = _
  rw [AlgEquiv.symm_apply_apply]

open scoped TensorProduct.RightActions in
theorem θ_pow_Φ_iterate (i : ℕ) (x : L ⊗[K] v.adicCompletion K) :
    (θ K L v hinert σ ^ i) (Φ K L v hinert x) =
      Φ K L v hinert ((⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] x) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, θ_Φ, Function.iterate_succ_apply']

open scoped TensorProduct.RightActions in
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

end Theta

section Degree

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L)))
  (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
include hv

theorem ramificationIdx_w₀ :
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) (w₀ K L v).1).asIdeal (w₀ K L v).1.asIdeal = 1 :=
  hv _ (w₀ K L v).2

include hinert in

theorem finrank_completion :
    Module.finrank (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) = Module.finrank K L := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have hsum := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  rw [Finset.sum_eq_single (w₀ K L v) (fun w' _ hw' => absurd (Subsingleton.elim _ _) hw')
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  rw [← HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L (w₀ K L v)]
  exact hsum

end Degree

section Order

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L)))
  (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
include hinert hprime hσ

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
  exact orderOf_eq_prime (θ_pow_finrank K L v hinert hprime σ hσ) (θ_ne_one K L v hinert hprime σ hσ)

end Order

section Inertia

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L)))
  (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
  (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
include hinert hprime hσ hv

attribute [local instance] Ideal.Quotient.field

omit hinert in

theorem exists_smul_sub_notMem : ∃ b : 𝓞 L, σ • b - b ∉ (w₀ K L v).1.asIdeal := by
  obtain ⟨hgal, -, -⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  haveI := hgal
  haveI := liesOver_of_extension K L v (w₀ K L v)
  haveI : (w₀ K L v).1.asIdeal.IsMaximal := (w₀ K L v).1.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal (w₀ K L v).1.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (w₀ K L v).1.asIdeal (L ≃ₐ[K] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal (w₀ K L v).1.asIdeal v.ne_bot] at hcard
  have he : Ideal.ramificationIdx' v.asIdeal (w₀ K L v).1.asIdeal = 1 := by
    have := ramificationIdx_w₀ K L v hv
    rwa [(w₀ K L v).2] at this
  rw [he] at hcard
  have hbot : Ideal.inertia (L ≃ₐ[K] L) (w₀ K L v).1.asIdeal = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  by_contra hall
  push Not at hall
  have hmem : σ ∈ Ideal.inertia (L ≃ₐ[K] L) (w₀ K L v).1.asIdeal := fun b => hall b
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hσ hmem

theorem exists_res : ∃ y : (w₀ K L v).1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ K L v hinert σ y - y‖ = 1 := by
  obtain ⟨b, hb⟩ := exists_smul_sub_notMem K L v hprime σ hσ hv
  refine ⟨algebraMap L _ (b : L), ?_, ?_⟩
  · exact NumberField.FinitePlace.norm_le_one (K := L) (w₀ K L v).1 b
  · rw [θ_algebraMap, ← map_sub]
    have h := (NumberField.FinitePlace.norm_eq_one_iff_notMem (K := L) (w₀ K L v).1 (σ • b - b)).2 hb
    exact h

end Inertia

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (hinert : Subsingleton (v.Extension (𝓞 L))) (σ : L ≃ₐ[K] L)
  (c : L ⊗[K] v.adicCompletion K) (ϖ : v.adicCompletion K) (s : ℕ)
include hinert

open scoped TensorProduct.RightActions in

theorem O_eq_comap :
    (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup =
      ((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
        (Φ K L v hinert).toAlgHom.toRingHom.toAddMonoidHom := by
  ext x
  exact mem_semiLocalIntegers_iff_Φ K L v hinert x

open scoped TensorProduct.RightActions in
theorem Λ_eq_comap :
    ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
        ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toAddMonoidHom - AddMonoidHom.mulLeft c)) =
      ((((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
          ((θ K L v hinert σ).toAlgHom.toRingHom.toAddMonoidHom -
            AddMonoidHom.mulLeft (Φ K L v hinert c))).comap
        (Φ K L v hinert).toAlgHom.toRingHom.toAddMonoidHom) := by
  ext x
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, AddSubgroup.mem_comap]
  change AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x - c * x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
    θ K L v hinert σ (Φ K L v hinert x) - Φ K L v hinert c * Φ K L v hinert x ∈ (w₀ K L v).1.adicCompletionIntegers L
  rw [mem_semiLocalIntegers_iff_Φ K L v hinert, map_sub, map_mul, θ_Φ]

open scoped TensorProduct.RightActions in
theorem B_eq_comap :
    ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
        (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s)))) =
      ((((w₀ K L v).1.adicCompletionIntegers L).toAddSubgroup.comap
          (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) (ϖ ^ s)))).comap
        (Φ K L v hinert).toAlgHom.toRingHom.toAddMonoidHom) := by
  ext x
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, AddSubgroup.mem_comap]
  change ((1 : L) ⊗ₜ[K] (ϖ ^ s)) * x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
    algebraMap (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) (ϖ ^ s) * Φ K L v hinert x ∈
      (w₀ K L v).1.adicCompletionIntegers L
  rw [mem_semiLocalIntegers_iff_Φ K L v hinert, map_mul, Φ_one_tmul]

omit hinert in

theorem relIndex_comap_comap {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G' →+ G)
    (hf : Function.Surjective f) (H K' : AddSubgroup G) :
    (H.comap f).relIndex (K'.comap f) = H.relIndex K' := by
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf]

end Transport

open scoped TensorProduct.RightActions in
theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L)))
    (c : L ⊗[K] v.adicCompletion K) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank K L),
        (⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] c = (1 : L) ⊗ₜ[K] n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.relIndex
        (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toAddMonoidHom -
              AddMonoidHom.mulLeft c)) ⊓
          ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m := by
  have hdeg := finrank_completion K L v hinert hv

  have hw := ramificationIdx_w₀ K L v hv
  have hprime' : (Module.finrank (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L)).Prime := by
    rw [hdeg]; exact hprime
  have hθ : orderOf (θ K L v hinert σ) = Module.finrank (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L) := by
    rw [hdeg]; exact orderOf_θ K L v hinert hprime σ hσ
  have hres := exists_res K L v hinert hprime σ hσ hv
  have hc' : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) ((w₀ K L v).1.adicCompletion L)),
      (θ K L v hinert σ ^ i) (Φ K L v hinert c) = algebraMap (v.adicCompletion K) _ n := by
    rw [hdeg, ← Φ_one_tmul K L v hinert n, ← hc, map_prod]
    exact Finset.prod_congr rfl fun i _ => θ_pow_Φ_iterate K L v hinert σ i c
  have hloc :=
    IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
      K L v (w₀ K L v) hw hprime' (θ K L v hinert σ) hθ hres (Φ K L v hinert c) n hn m hm hc' ϖ hϖ s

  rw [Λ_eq_comap K L v hinert σ c, B_eq_comap K L v hinert ϖ s, O_eq_comap K L v hinert, ← AddSubgroup.comap_inf,
    relIndex_comap_comap _ (Φ K L v hinert).surjective]
  exact hloc

end P2mInertIndex

end

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L)))
    (c : L ⊗[K] v.adicCompletion K) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank K L),
        (⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] c = (1 : L) ⊗ₜ[K] n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.relIndex
        (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toAddMonoidHom -
              AddMonoidHom.mulLeft c)) ⊓
          ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m :=
  P2mInertIndex.main K L hprime σ hσ v hv hinert c n hn m hm hc ϖ hϖ s

end S_AutomorphicForm_relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension
end P2MW
export P2MW.S_AutomorphicForm_relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension (solution)
