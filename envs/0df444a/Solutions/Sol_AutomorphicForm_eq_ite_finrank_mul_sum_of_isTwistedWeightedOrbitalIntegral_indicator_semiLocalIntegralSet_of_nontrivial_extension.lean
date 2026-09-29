-- Prove2me | solution 1 for AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fc0028ab-550c-5cb5-86fc-80d362bba452

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
import Theorems.Thm_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
import Theorems.Thm_AutomorphicForm_integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure TopologicalSpace Function NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mCTSplitGlue

open AutomorphicForm AutomorphicForm.SplitPlace

section Embedding

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem liesOver_of_extension (w : v.Extension (𝓞 L)) : w.1.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have h := congrArg HeightOneSpectrum.asIdeal w.2
  exact h.symm

theorem finrank_adicCompletion_eq_one_of_nontrivial [IsGalois K L]
    (hdeg : (Module.finrank K L).Prime) (hnt : Nontrivial (v.Extension (𝓞 L)))
    (w : v.Extension (𝓞 L)) :
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  classical
  have hpb : v.asIdeal ≠ ⊥ := v.ne_bot
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have key := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 L) (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at key
  obtain ⟨w₁, w₂, hne⟩ := hnt
  haveI := liesOver_of_extension K L v w₁
  haveI := liesOver_of_extension K L v w₂
  have hmem₁ : w₁.1.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) := ⟨w₁.1.isPrime, inferInstance⟩
  have hmem₂ : w₂.1.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) := ⟨w₂.1.isPrime, inferInstance⟩
  have hne' : w₁.1.asIdeal ≠ w₂.1.asIdeal := by
    intro h
    exact hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hfin : (v.asIdeal.primesOver (𝓞 L)).Finite := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)
  have hg : 1 < (v.asIdeal.primesOver (𝓞 L)).ncard :=
    (Set.one_lt_ncard hfin).2 ⟨_, hmem₁, _, hmem₂, hne'⟩
  have hdvd : (v.asIdeal.primesOver (𝓞 L)).ncard ∣ Module.finrank K L := ⟨_, key.symm⟩
  have hgp : (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
    rcases (Nat.dvd_prime hdeg).1 hdvd with h | h
    · exact absurd h hg.ne'
    · exact h
  have hef : v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) = 1 := by
    have h2 : Module.finrank K L * (v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L)) =
        Module.finrank K L * 1 := by rw [mul_one]; conv_rhs => rw [← key]; rw [hgp]
    exact Nat.eq_of_mul_eq_mul_left hdeg.pos h2
  haveI := liesOver_of_extension K L v w
  haveI : w.1.asIdeal.IsPrime := w.1.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal (L ≃ₐ[K] L)] at hef
  haveI := w.1.isMaximal
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.1.asIdeal hpb,
    ← Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.1.asIdeal] at hef
  rw [← HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w]
  exact hef

def iota (w : v.Extension (𝓞 L))
    (h1 : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1) :
    v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L :=
  AlgEquiv.ofBijective (Algebra.ofId (v.adicCompletion K) (w.1.adicCompletion L)) (by
    refine ⟨(algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective, fun y => ?_⟩
    have hbt : (⊥ : Subalgebra (v.adicCompletion K) (w.1.adicCompletion L)) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one h1
    have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion K) (w.1.adicCompletion L)) := by
      rw [hbt]; exact Algebra.mem_top
    obtain ⟨z, hz⟩ := Algebra.mem_bot.1 hy
    exact ⟨z, hz⟩)

theorem iota_apply (w : v.Extension (𝓞 L)) (h1) (z : v.adicCompletion K) :
    iota K L v w h1 z = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) z := rfl

theorem algebraMap_algebraMap_eq (w : v.Extension (𝓞 L)) (k : K) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (algebraMap K (v.adicCompletion K) k) =
      algebraMap K (w.1.adicCompletion L) k := by
  rw [IsScalarTower.algebraMap_apply K L (w.1.adicCompletion L)]
  rw [RingHom.algebraMap_toAlgebra]
  change (HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w)
    (((WithVal.equiv (v.valuation K)).symm k : WithVal (v.valuation K)) : v.adicCompletion K) = _
  rw [HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
  rfl

def embed (w : v.Extension (𝓞 L))
    (h1 : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1) :
    L →ₐ[K] v.adicCompletion K where
  toFun l := (iota K L v w h1).symm (algebraMap L (w.1.adicCompletion L) l)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]
  commutes' k := by
    apply (iota K L v w h1).injective
    rw [AlgEquiv.apply_symm_apply, iota_apply, algebraMap_algebraMap_eq,
      IsScalarTower.algebraMap_apply K L (w.1.adicCompletion L)]

theorem nonempty_algHom_of_nontrivial [IsGalois K L] (hdeg : (Module.finrank K L).Prime)
    (hnt : Nontrivial (v.Extension (𝓞 L))) : Nonempty (L →ₐ[K] v.adicCompletion K) := by
  haveI := hnt
  let w : v.Extension (𝓞 L) := Classical.arbitrary _
  exact ⟨embed K L v w (finrank_adicCompletion_eq_one_of_nontrivial K L v hdeg hnt w)⟩

end Embedding

section PsiKv

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def psiA : (L ⊗[K] A) →ₐ[A] (Fin (Module.finrank K L) → A) :=
  { (psi K L A σ ι).toRingHom with
    commutes' := fun a => by
      change psi K L A σ ι (algebraMap A (L ⊗[K] A) a) = _
      have h : algebraMap A (L ⊗[K] A) a = (1 : L) ⊗ₜ[K] a := rfl
      rw [h, psi_one_tmul]
      rfl }

@[scoped simp] theorem psiA_apply (z : L ⊗[K] A) : psiA A σ ι z = psi K L A σ ι z := rfl

def psiAEquiv : (L ⊗[K] A) ≃ₐ[A] (Fin (Module.finrank K L) → A) :=
  AlgEquiv.ofBijective (psiA A σ ι) (psi_bijective A σ ι hdeg hσ)

@[scoped simp] theorem psiAEquiv_apply (z : L ⊗[K] A) : psiAEquiv A σ ι hdeg hσ z = psi K L A σ ι z := rfl

theorem glMap_eval_psiAEquiv (g : GL (Fin 2) (L ⊗[K] A)) (i : Fin (Module.finrank K L)) :
    Matrix.GeneralLinearGroup.map
        ((Pi.evalAlgHom A (fun _ : Fin (Module.finrank K L) => A) i).comp
          (psiAEquiv A σ ι hdeg hσ).toAlgHom).toRingHom g =
      psiGL A σ ι hdeg hσ g i := by
  ext p q
  rfl

theorem coords_eq_psiGL (g : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)) :
    coords A σ ι hdeg hσ g j = psiGL A σ ι hdeg hσ g (Fin.cast (finrank_eq_succ K L).symm j) := rfl

end PsiKv

section IntegersWeights

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] v.adicCompletion K)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem coords_inv_apply (g : GL (Fin 2) (L ⊗[K] Kv)) (j : Fin (Module.finrank K L - 1 + 1)) :
    (coords Kv σ ι hdeg hσ g j)⁻¹ = coords Kv σ ι hdeg hσ g⁻¹ j := by
  rw [map_inv]; rfl

theorem mem_semiLocalIntegralSet_iff (g : GL (Fin 2) (L ⊗[K] Kv)) :
    g ∈ semiLocalIntegralSet K L v ↔
      ∀ j : Fin (Module.finrank K L - 1 + 1), coords Kv σ ι hdeg hσ g j ∈ localIntegralSet K v := by
  have hS := (AutomorphicForm.mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
    K L v (Fin (Module.finrank K L)) (psiAEquiv Kv σ ι hdeg hσ)).1
  simp only [psiAEquiv_apply] at hS
  rw [semiLocalIntegralSet, mem_integralUnitsSet]
  simp only [mem_localIntegralSet, coords_inv_apply, coords_apply_val]
  constructor
  · rintro ⟨h1, h2⟩ j
    exact ⟨fun p q => (hS _).1 (h1 p q) _, fun p q => (hS _).1 (h2 p q) _⟩
  · intro h
    refine ⟨fun p q => (hS _).2 fun i => ?_, fun p q => (hS _).2 fun i => ?_⟩
    · simpa using (h (Fin.cast (finrank_eq_succ K L) i)).1 p q
    · simpa using (h (Fin.cast (finrank_eq_succ K L) i)).2 p q

theorem mem_semiLocalIntegralSet_iff_mem_pi (g : GL (Fin 2) (L ⊗[K] Kv)) :
    g ∈ semiLocalIntegralSet K L v ↔
      coords Kv σ ι hdeg hσ g ∈ Set.pi Set.univ (fun _ : Fin (Module.finrank K L - 1 + 1) => localIntegralSet K v) := by
  rw [mem_semiLocalIntegralSet_iff K L v σ ι hdeg hσ, Set.mem_univ_pi]

theorem semiLocalWeight_eq_sum (g : GL (Fin 2) (L ⊗[K] Kv)) :
    semiLocalWeight K L v g = ∑ j : Fin (Module.finrank K L - 1 + 1), LocalWeight.weight (coords Kv σ ι hdeg hσ g j) := by
  have hS := (AutomorphicForm.mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
    K L v (Fin (Module.finrank K L)) (psiAEquiv Kv σ ι hdeg hσ)).2 g
  rw [hS]
  simp only [glMap_eval_psiAEquiv]
  exact (Fintype.sum_equiv (finCongr (finrank_eq_succ K L)) _ _ fun i => rfl)

end IntegersWeights

section Shift

variable {G : Type*} [Group G] {m : ℕ}

def shift (m : ℕ) : (Fin m → G) ≃* (Fin m → G) where
  toEquiv := Equiv.arrowCongr (finRotate m) (Equiv.refl G) |>.symm
  map_mul' _ _ := rfl

@[scoped simp] theorem shift_apply (t : Fin m → G) (i : Fin m) : shift m t i = t (finRotate m i) := rfl

theorem shift_iterate_apply (k : ℕ) (t : Fin m → G) (i : Fin m) :
    ((shift m : (Fin m → G) → Fin m → G)^[k]) t i = t (((finRotate m : Fin m → Fin m)^[k]) i) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, shift_apply, Function.iterate_succ_apply' (finRotate m)]

theorem val_finRotate : ∀ {m : ℕ} (i : Fin m), ((finRotate m i : Fin m) : ℕ) = ((i : ℕ) + 1) % m
  | 0, i => i.elim0
  | m + 1, i => by
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 i.2) with h | h
      · have hi : i = ⟨(i : ℕ), i.2⟩ := rfl
        rw [hi, finRotate_of_lt h]
        simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]
      · have hi : i = Fin.last m := Fin.ext h
        subst hi
        rw [finRotate_last]
        simp

theorem val_finRotate_iterate (k : ℕ) (i : Fin m) :
    ((((finRotate m : Fin m → Fin m)^[k]) i : Fin m) : ℕ) = ((i : ℕ) + k) % m := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.2]
  | succ k ih =>
      rw [Function.iterate_succ_apply', val_finRotate, ih, Nat.mod_add_mod, Nat.add_assoc]

theorem finRotate_iterate_zero {m : ℕ} (k : ℕ) (hk : k < m + 1) :
    ((finRotate (m + 1) : Fin (m + 1) → Fin (m + 1))^[k]) 0 = ⟨k, hk⟩ := by
  apply Fin.ext
  rw [val_finRotate_iterate]
  simp [Nat.mod_eq_of_lt hk]

theorem finRotate_cast {a b : ℕ} (h : a = b) (j : Fin b) :
    finRotate a (Fin.cast h.symm j) = Fin.cast h.symm (finRotate b j) := by
  subst h; rfl

theorem prod_map_shift_iterate_apply_zero (D : Fin (m + 1) → G) :
    ((List.range (m + 1)).map fun k => ((shift (m + 1) : (Fin (m + 1) → G) → _)^[k]) D).prod 0 =
      listProd D := by
  have heval : ((List.range (m + 1)).map fun k => ((shift (m + 1) : (Fin (m + 1) → G) → _)^[k]) D).prod 0 =
      Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0
        (((List.range (m + 1)).map fun k => ((shift (m + 1) : (Fin (m + 1) → G) → _)^[k]) D).prod) := rfl
  rw [heval, map_list_prod, List.map_map]
  unfold listProd
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_ofFn]
    simp only [Function.comp_apply, Pi.evalMonoidHom_apply, shift_iterate_apply, List.getElem_range]
    have hi : i < m + 1 := by simpa using h1
    rw [finRotate_iterate_zero i hi]

end Shift

section Dictionary

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

theorem pow_mod_apply {k : ℕ} (hℓ : σ ^ Module.finrank K L = 1) (x : L) :
    (σ ^ (k % Module.finrank K L)) x = (σ ^ k) x := by
  conv_rhs => rw [← Nat.mod_add_div k (Module.finrank K L), pow_add, pow_mul, hℓ, one_pow, mul_one]

theorem psi_sigmaTensor (hℓ : σ ^ Module.finrank K L = 1) (z : L ⊗[K] A)
    (i : Fin (Module.finrank K L)) :
    psi K L A σ ι (sigmaTensor K L A σ z) i = psi K L A σ ι z (finRotate _ i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      have hs : sigmaTensor K L A σ (x ⊗ₜ[K] b) = σ x ⊗ₜ[K] b := rfl
      rw [hs, psi_tmul, psi_tmul, val_finRotate, pow_mod_apply σ hℓ, pow_succ, AlgEquiv.mul_apply]
  | add z w hz hw => simp [map_add, hz, hw]

theorem coords_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    coords A σ ι hdeg hσ (sigmaGL K L A σ g) = shift _ (coords A σ ι hdeg hσ g) := by
  funext j
  ext p q
  rw [shift_apply, coords_apply_val, coords_apply_val, ← finRotate_cast (finrank_eq_succ K L)]
  exact psi_sigmaTensor A σ ι (pow_finrank_eq_one hdeg σ hσ) _ _

theorem coords_toTensorGL (γ : GL (Fin 2) A) :
    coords A σ ι hdeg hσ (toTensorGL K L A γ) = fun _ => γ := by
  funext j
  ext p q
  rw [coords_apply_val]
  change psi K L A σ ι ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) p q)) _ = _
  rw [psi_tmul, map_one, map_one, one_mul]

theorem coords_twistedConj_apply (x δ : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)) :
    coords A σ ι hdeg hσ (x⁻¹ * δ * sigmaGL K L A σ x) j =
      (coords A σ ι hdeg hσ x j)⁻¹ * coords A σ ι hdeg hσ δ j * coords A σ ι hdeg hσ x (finRotate _ j) := by
  rw [map_mul, map_mul, map_inv, coords_sigmaGL]
  rfl

theorem coords_sigmaGL_iterate (k : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    coords A σ ι hdeg hσ (((sigmaGL K L A σ : _ → _))^[k] g) =
      ((shift (Module.finrank K L - 1 + 1) : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → _)^[k])
        (coords A σ ι hdeg hσ g) :=
  Function.Semiconj.iterate_right (f := coords A σ ι hdeg hσ) (fun x => coords_sigmaGL A σ ι hdeg hσ x) k g

theorem coords_normString_zero (δ : GL (Fin 2) (L ⊗[K] A)) :
    coords A σ ι hdeg hσ (normString K L A σ δ) 0 = listProd (coords A σ ι hdeg hσ δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  have hfun : ((coords A σ ι hdeg hσ : GL (Fin 2) (L ⊗[K] A) → _) ∘ fun i => (⇑(sigmaGL K L A σ))^[i] δ) =
      fun k => ((shift (Module.finrank K L - 1 + 1) :
        (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → _)^[k]) (coords A σ ι hdeg hσ δ) := by
    funext k
    exact coords_sigmaGL_iterate A σ ι hdeg hσ k δ
  rw [hfun]
  have hrange : List.range (Module.finrank K L) = List.range (Module.finrank K L - 1 + 1) :=
    congrArg List.range (finrank_eq_succ K L)
  rw [hrange]
  exact prod_map_shift_iterate_apply_zero _

end Dictionary

section Diagonal

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def unitCoord (u : (L ⊗[K] A)ˣ) (j : Fin (Module.finrank K L - 1 + 1)) : Aˣ :=
  Units.map ((Pi.evalRingHom (fun _ : Fin (Module.finrank K L) => A)
    (Fin.cast (finrank_eq_succ K L).symm j)).comp (psi K L A σ ι).toRingHom).toMonoidHom u

@[scoped simp] theorem val_unitCoord (u : (L ⊗[K] A)ˣ) (j : Fin (Module.finrank K L - 1 + 1)) :
    ((unitCoord A σ ι u j : Aˣ) : A) = psi K L A σ ι (u : L ⊗[K] A) (Fin.cast (finrank_eq_succ K L).symm j) := rfl

theorem coords_diagUnits2 (α β : (L ⊗[K] A)ˣ) (j : Fin (Module.finrank K L - 1 + 1)) :
    coords A σ ι hdeg hσ (diagUnits2 α β) j = diagUnits2 (unitCoord A σ ι α j) (unitCoord A σ ι β j) := by
  ext p q
  rw [coords_apply_val]
  fin_cases p <;> fin_cases q <;> simp [diagUnits2, map_zero]

omit [FiniteDimensional K L] in
theorem diagUnits2_mul (a₁ b₁ a₂ b₂ : Aˣ) :
    diagUnits2 a₁ b₁ * diagUnits2 a₂ b₂ = diagUnits2 (a₁ * a₂) (b₁ * b₂) := by
  ext i j
  push_cast
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2, Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [FiniteDimensional K L] in

def diagHom : Aˣ × Aˣ →* GL (Fin 2) A where
  toFun p := diagUnits2 p.1 p.2
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagUnits2]
  map_mul' p q := (diagUnits2_mul A p.1 p.2 q.1 q.2).symm

omit [FiniteDimensional K L] in
theorem listProd_diagUnits2 {m : ℕ} (a b : Fin m → Aˣ) :
    listProd (fun j => diagUnits2 (a j) (b j)) = diagUnits2 (∏ j, a j) (∏ j, b j) := by
  have h : (fun j => diagUnits2 (a j) (b j)) = diagHom A ∘ (fun j => (a j, b j)) := rfl
  unfold listProd
  rw [h, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn]
  have hp : (∏ j, (a j, b j)) = (∏ j, a j, ∏ j, b j) := Prod.ext (Prod.fst_prod) (Prod.snd_prod)
  rw [hp]
  rfl

omit [FiniteDimensional K L] in
theorem diagUnits2_injective {a₁ b₁ a₂ b₂ : Aˣ} (h : diagUnits2 a₁ b₁ = diagUnits2 a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have h' := congrArg (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A)) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at h'
  constructor
  · apply Units.ext
    have := congrFun (congrFun h' 0) 0
    simpa using this
  · apply Units.ext
    have := congrFun (congrFun h' 1) 1
    simpa using this

include hdeg hσ in

theorem prod_unitCoord_eq (a b : Aˣ) (α β : (L ⊗[K] A)ˣ)
    (hN : normString K L A σ (diagUnits2 α β) = toTensorGL K L A (diagUnits2 a b)) :
    (∏ j, unitCoord A σ ι α j) = a ∧ (∏ j, unitCoord A σ ι β j) = b := by
  have h0 := congrFun (congrArg (coords A σ ι hdeg hσ) hN) 0
  rw [coords_toTensorGL, coords_normString_zero] at h0
  have hfun : coords A σ ι hdeg hσ (diagUnits2 α β) =
      fun j => diagUnits2 (unitCoord A σ ι α j) (unitCoord A σ ι β j) :=
    funext (coords_diagUnits2 A σ ι hdeg hσ α β)
  rw [hfun, listProd_diagUnits2] at h0
  exact diagUnits2_injective A h0

end Diagonal

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel AutomorphicForm.isTopologicalRing_tensor

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

variable {K L} in
theorem secondCountableTopology_tensor [SecondCountableTopology A] : SecondCountableTopology (L ⊗[K] A) := by
  haveI : ContinuousAdd (L ⊗[K] A) := IsModuleTopology.toContinuousAdd A _
  let b := aBasis K L A
  let e : (L ⊗[K] A) ≃ₗ[A] (Fin (Module.finrank K L) → A) := b.equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (Fin (Module.finrank K L) → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  exact eh.secondCountableTopology

end TensorTopology

attribute [local instance] borelSpace_twistedCentralizer t2Space_tensor' locallyCompactSpace_tensor'
  secondCountableTopology_tensor

section Coords

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A) (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def matPsi :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] A) ≃ₜ* (Fin (Module.finrank K L) → Matrix (Fin 2) (Fin 2) A) :=
  { ((psiEquiv A σ ι hdeg hσ).toRingEquiv.mapMatrix.trans
      (Matrix.piRingEquiv (β := fun _ : Fin (Module.finrank K L) => A) (n := Fin 2))).toMulEquiv with
    continuous_toFun := by
      refine continuous_pi fun i => continuous_pi fun p => continuous_pi fun q => ?_
      exact (continuous_apply i).comp ((continuous_psi A σ ι).comp
        ((continuous_apply q).comp (continuous_apply p)))
    continuous_invFun := by
      refine continuous_pi fun p => continuous_pi fun q => ?_
      refine (continuous_psiEquiv_symm A σ ι hdeg hσ).comp ?_
      exact continuous_pi fun i => (continuous_apply q).comp ((continuous_apply p).comp (continuous_apply i)) }

def psiGLₜ : GL (Fin 2) (L ⊗[K] A) ≃ₜ* (Fin (Module.finrank K L) → GL (Fin 2) A) :=
  (Units.mapContinuousMulEquiv (matPsi A σ ι hdeg hσ)).trans ContinuousMulEquiv.piUnits

theorem psiGLₜ_apply (g : GL (Fin 2) (L ⊗[K] A)) : psiGLₜ A σ ι hdeg hσ g = psiGL A σ ι hdeg hσ g := by
  funext i; ext p q; rfl

def reindexₜ : (Fin (Module.finrank K L) → GL (Fin 2) A) ≃ₜ* (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  { reindex K L (GL (Fin 2) A) with
    continuous_toFun := continuous_pi fun j => continuous_apply _
    continuous_invFun := continuous_pi fun i => continuous_apply _ }

def coordsₜ : GL (Fin 2) (L ⊗[K] A) ≃ₜ* (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  (psiGLₜ A σ ι hdeg hσ).trans (reindexₜ A)

theorem coordsₜ_apply (g : GL (Fin 2) (L ⊗[K] A)) : coordsₜ A σ ι hdeg hσ g = coords A σ ι hdeg hσ g := by
  funext j
  change reindex K L (GL (Fin 2) A) (psiGLₜ A σ ι hdeg hσ g) j = _
  rw [psiGLₜ_apply]
  rfl

theorem coordsₜ_eq : ((coordsₜ A σ ι hdeg hσ) : GL (Fin 2) (L ⊗[K] A) → _) = coords A σ ι hdeg hσ :=
  funext (coordsₜ_apply A σ ι hdeg hσ)

theorem continuous_coords : Continuous (coords A σ ι hdeg hσ) := by
  rw [← coordsₜ_eq]; exact (coordsₜ A σ ι hdeg hσ).continuous

theorem coordsₜ_symm_eq :
    ((coordsₜ A σ ι hdeg hσ).symm : _ → GL (Fin 2) (L ⊗[K] A)) = (coords A σ ι hdeg hσ).symm := by
  funext t
  apply (coords A σ ι hdeg hσ).injective
  rw [MulEquiv.apply_symm_apply, ← coordsₜ_apply, ContinuousMulEquiv.apply_symm_apply]

theorem continuous_coords_symm : Continuous (coords A σ ι hdeg hσ).symm := by
  rw [← coordsₜ_symm_eq]; exact (coordsₜ A σ ι hdeg hσ).symm.continuous

def coordsHomeo : GL (Fin 2) (L ⊗[K] A) ≃ₜ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  { (coords A σ ι hdeg hσ).toEquiv with
    continuous_toFun := continuous_coords A σ ι hdeg hσ
    continuous_invFun := continuous_coords_symm A σ ι hdeg hσ }

@[scoped simp] theorem coordsHomeo_apply (g : GL (Fin 2) (L ⊗[K] A)) :
    coordsHomeo A σ ι hdeg hσ g = coords A σ ι hdeg hσ g := rfl

theorem toTensorGL_eq_symm_const (γ : GL (Fin 2) A) :
    toTensorGL K L A γ = (coords A σ ι hdeg hσ).symm (fun _ => γ) := by
  apply (coords A σ ι hdeg hσ).injective
  rw [MulEquiv.apply_symm_apply, coords_toTensorGL]

include σ ι hdeg hσ in
theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  have h : (toTensorGL K L A : GL (Fin 2) A → _) = fun γ => (coords A σ ι hdeg hσ).symm (fun _ => γ) :=
    funext (toTensorGL_eq_symm_const A σ ι hdeg hσ)
  rw [h]
  exact (continuous_coords_symm A σ ι hdeg hσ).comp (continuous_pi fun _ => continuous_id)

end Coords

section Place

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] v.adicCompletion K)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "n" => Module.finrank K L - 1

scoped instance : (localHaar K v).IsHaarMeasure := isHaarMeasure_localHaar K v

scoped instance : (semiLocalHaar K L v).IsHaarMeasure := isHaarMeasure_semiLocalHaar K L v

def piIntegralCompacts : PositiveCompacts (Fin (n + 1) → GL (Fin 2) Kv) where
  carrier := Set.pi Set.univ fun _ => localIntegralSet K v
  isCompact' := isCompact_univ_pi fun _ => isCompact_localIntegralSet K v
  interior_nonempty' := by
    rw [(isOpen_set_pi Set.finite_univ fun _ _ => isOpen_localIntegralSet K v).interior_eq]
    exact ⟨fun _ => 1, fun _ _ => one_mem_localIntegralSet K v⟩

theorem map_coords_semiLocalHaar :
    Measure.map (coords Kv σ ι hdeg hσ) (semiLocalHaar K L v) =
      Measure.pi (fun _ : Fin (n + 1) => localHaar K v) := by
  haveI h1 : (Measure.map (coords Kv σ ι hdeg hσ) (semiLocalHaar K L v)).IsHaarMeasure := by
    rw [← coordsₜ_eq]
    exact (coordsₜ Kv σ ι hdeg hσ).isHaarMeasure_map (semiLocalHaar K L v)
  haveI h2 : (Measure.pi (fun _ : Fin (n + 1) => localHaar K v)).IsHaarMeasure := inferInstance
  have hK₁ : Measure.map (coords Kv σ ι hdeg hσ) (semiLocalHaar K L v) (piIntegralCompacts K L v) = 1 := by
    rw [Measure.map_apply (continuous_coords Kv σ ι hdeg hσ).measurable
      (piIntegralCompacts K L v).isCompact.measurableSet]
    have hpre : (coords Kv σ ι hdeg hσ) ⁻¹' (piIntegralCompacts K L v : Set (Fin (n + 1) → GL (Fin 2) Kv)) =
        semiLocalIntegralSet K L v := by
      ext g
      rw [Set.mem_preimage]
      exact (mem_semiLocalIntegralSet_iff_mem_pi K L v σ ι hdeg hσ g).symm
    rw [hpre, semiLocalHaar_semiLocalIntegralSet]
  have hK₂ : Measure.pi (fun _ : Fin (n + 1) => localHaar K v) (piIntegralCompacts K L v) = 1 := by
    change Measure.pi (fun _ : Fin (n + 1) => localHaar K v) (Set.pi Set.univ fun _ => localIntegralSet K v) = 1
    rw [Measure.pi_pi]
    simp [localHaar_localIntegralSet]
  rw [haarMeasure_unique (Measure.map (coords Kv σ ι hdeg hσ) (semiLocalHaar K L v)) (piIntegralCompacts K L v),
    haarMeasure_unique (Measure.pi (fun _ : Fin (n + 1) => localHaar K v)) (piIntegralCompacts K L v), hK₁, hK₂]

variable (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) (α β : (L ⊗[K] HeightOneSpectrum.adicCompletion K v)ˣ)
  (hT : twistedCentralizer K L (HeightOneSpectrum.adicCompletion K v) σ (diagUnits2 α β) =
    (localCentralizer K v (diagUnits2 a b)).map (toTensorGL K L (HeightOneSpectrum.adicCompletion K v)))

def torusEquiv : localCentralizer K v (diagUnits2 a b) ≃ₜ* twistedCentralizer K L Kv σ (diagUnits2 α β) where
  toFun t := ⟨toTensorGL K L Kv (t : GL (Fin 2) Kv),
    (SetLike.ext_iff.1 hT _).2 (Subgroup.mem_map_of_mem (toTensorGL K L Kv) t.2)⟩
  invFun t' := ⟨coords Kv σ ι hdeg hσ (t' : GL (Fin 2) (L ⊗[K] Kv)) 0, by
    have ht' := (SetLike.ext_iff.1 hT _).1 t'.2
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.1 ht'
    rw [← hteq, coords_toTensorGL]
    exact ht⟩
  left_inv t := by
    apply Subtype.ext
    change coords Kv σ ι hdeg hσ (toTensorGL K L Kv (t : GL (Fin 2) Kv)) 0 = (t : GL (Fin 2) Kv)
    rw [coords_toTensorGL]
  right_inv t' := by
    apply Subtype.ext
    have ht' := (SetLike.ext_iff.1 hT _).1 t'.2
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.1 ht'
    change toTensorGL K L Kv (coords Kv σ ι hdeg hσ (t' : GL (Fin 2) (L ⊗[K] Kv)) 0) = (t' : GL (Fin 2) (L ⊗[K] Kv))
    rw [← hteq, coords_toTensorGL]
  map_mul' s t := by
    apply Subtype.ext
    change toTensorGL K L Kv ((s : GL (Fin 2) Kv) * (t : GL (Fin 2) Kv)) =
      toTensorGL K L Kv (s : GL (Fin 2) Kv) * toTensorGL K L Kv (t : GL (Fin 2) Kv)
    rw [map_mul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_toTensorGL Kv σ ι hdeg hσ).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 0).comp ((continuous_coords Kv σ ι hdeg hσ).comp continuous_subtype_val)

theorem torusEquiv_apply_val (t : localCentralizer K v (diagUnits2 a b)) :
    ((torusEquiv K L v σ ι hdeg hσ a b α β hT t : twistedCentralizer K L Kv σ (diagUnits2 α β)) :
      GL (Fin 2) (L ⊗[K] Kv)) = toTensorGL K L Kv (t : GL (Fin 2) Kv) := rfl

theorem torusEquiv_symm_apply_val (t' : twistedCentralizer K L Kv σ (diagUnits2 α β)) :
    (((torusEquiv K L v σ ι hdeg hσ a b α β hT).symm t' : localCentralizer K v (diagUnits2 a b)) : GL (Fin 2) Kv) =
      coords Kv σ ι hdeg hσ (t' : GL (Fin 2) (L ⊗[K] Kv)) 0 := rfl

theorem toTensorGL_torusEquiv_symm (t' : twistedCentralizer K L Kv σ (diagUnits2 α β)) :
    toTensorGL K L Kv (((torusEquiv K L v σ ι hdeg hσ a b α β hT).symm t' : localCentralizer K v (diagUnits2 a b)) :
      GL (Fin 2) Kv) = (t' : GL (Fin 2) (L ⊗[K] Kv)) :=
  congrArg Subtype.val ((torusEquiv K L v σ ι hdeg hσ a b α β hT).apply_symm_apply t')

def tau (τ' : Measure (twistedCentralizer K L Kv σ (diagUnits2 α β))) :
    Measure (localCentralizer K v (diagUnits2 a b)) :=
  Measure.map (torusEquiv K L v σ ι hdeg hσ a b α β hT).symm τ'

theorem isHaarMeasure_tau (τ' : Measure (twistedCentralizer K L Kv σ (diagUnits2 α β))) [τ'.IsHaarMeasure] :
    (tau K L v σ ι hdeg hσ a b α β hT τ').IsHaarMeasure :=
  (torusEquiv K L v σ ι hdeg hσ a b α β hT).symm.isHaarMeasure_map τ'

theorem tau_integral (τ' : Measure (twistedCentralizer K L Kv σ (diagUnits2 α β))) :
    tau K L v σ ι hdeg hσ a b α β hT τ' {t | (t : GL (Fin 2) Kv) ∈ localIntegralSet K v} =
      τ' {t' | (t' : GL (Fin 2) (L ⊗[K] Kv)) ∈ semiLocalIntegralSet K L v} := by
  unfold tau
  have hmeas : MeasurableSet {t : localCentralizer K v (diagUnits2 a b) | (t : GL (Fin 2) Kv) ∈ localIntegralSet K v} :=
    (isOpen_localIntegralSet K v).measurableSet.preimage continuous_subtype_val.measurable
  have hme : Measurable ((torusEquiv K L v σ ι hdeg hσ a b α β hT).symm :
      twistedCentralizer K L Kv σ (diagUnits2 α β) → localCentralizer K v (diagUnits2 a b)) :=
    (torusEquiv K L v σ ι hdeg hσ a b α β hT).symm.continuous.measurable
  rw [Measure.map_apply hme hmeas]
  congr 1
  ext t'
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [← toTensorGL_torusEquiv_symm K L v σ ι hdeg hσ a b α β hT t',
    mem_semiLocalIntegralSet_iff K L v σ ι hdeg hσ, coords_toTensorGL]
  simp

theorem integral_tau (τ' : Measure (twistedCentralizer K L Kv σ (diagUnits2 α β)))
    (F : twistedCentralizer K L Kv σ (diagUnits2 α β) → ℝ) :
    ∫ t, F (torusEquiv K L v σ ι hdeg hσ a b α β hT t) ∂(tau K L v σ ι hdeg hσ a b α β hT τ') = ∫ t', F t' ∂τ' := by
  unfold tau
  have h := integral_map_equiv (μ := τ') (torusEquiv K L v σ ι hdeg hσ a b α β hT).symm.toHomeomorph.toMeasurableEquiv
    (fun t => F (torusEquiv K L v σ ι hdeg hσ a b α β hT t))
  change ∫ t, F (torusEquiv K L v σ ι hdeg hσ a b α β hT t)
    ∂(Measure.map ((torusEquiv K L v σ ι hdeg hσ a b α β hT).symm.toHomeomorph.toMeasurableEquiv) τ') = _
  rw [h]
  congr 1
  funext t'
  congr 1
  exact (torusEquiv K L v σ ι hdeg hσ a b α β hT).apply_symm_apply t'

end Place

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] v.adicCompletion K)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "n" => Module.finrank K L - 1

include ι hdeg hσ in
theorem main (a b : Kvˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : Kv) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (L ⊗[K] Kv)ˣ)
    (hN : normString K L Kv σ (diagUnits2 α β) = toTensorGL K L Kv (diagUnits2 a b))
    (τ' : Measure (twistedCentralizer K L Kv σ (diagUnits2 α β))) [τ'.IsHaarMeasure]
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] Kv)) ∈ semiLocalIntegralSet K L v} = 1)
    (J' : ℂ)
    (hJ' : IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) J') :
    J' = (Module.finrank K L : ℂ) *
      (if ‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1 then
        (((2 * Real.log (Ideal.absNorm v.asIdeal) *
            ∑ s ∈ Finset.range (m.toNat + 1),
              (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0) := by

  have hT := AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
    K L hdeg σ hσ Kv a b hab α β hN
  set eT := torusEquiv K L v σ ι hdeg hσ a b α β hT with heT
  set τ : Measure (localCentralizer K v (diagUnits2 a b)) := tau K L v σ ι hdeg hσ a b α β hT τ' with hτdef
  haveI hτ : τ.IsHaarMeasure := isHaarMeasure_tau K L v σ ι hdeg hσ a b α β hT τ'
  have hτ1 : τ {t | (t : GL (Fin 2) Kv) ∈ localIntegralSet K v} = 1 := by
    rw [hτdef, tau_integral, hτ'1]

  set c : ℂ := (if ‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1 then
        (((2 * Real.log (Ideal.absNorm v.asIdeal) *
            ∑ s ∈ Finset.range (m.toNat + 1),
              (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0) with hc
  have hcK : ∀ J : ℂ, IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) J → J = c :=
    fun J hJ => AutomorphicForm.eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
      K v a b hab m hm τ hτ hτ1 J hJ

  set Ψ := coords Kv σ ι hdeg hσ with hΨ
  set D : Fin (n + 1) → GL (Fin 2) Kv := Ψ (diagUnits2 α β) with hD
  have hDj : ∀ j, D j = diagUnits2 (unitCoord Kv σ ι α j) (unitCoord Kv σ ι β j) :=
    fun j => coords_diagUnits2 Kv σ ι hdeg hσ α β j
  obtain ⟨hprodα, hprodβ⟩ := prod_unitCoord_eq Kv σ ι hdeg hσ a b α β hN

  obtain ⟨w', ⟨hw'0, hw'm, hw'c, hw'sec⟩, rfl⟩ := hJ'
  set s : (Fin (n + 1) → GL (Fin 2) Kv) → ℝ := fun X => w' (Ψ.symm X) with hs
  have hs0 : ∀ X, 0 ≤ s X := fun X => hw'0 _
  have hsm : Measurable s := hw'm.comp (continuous_coords_symm Kv σ ι hdeg hσ).measurable
  have hsc : HasCompactSupport s := hw'c.comp_homeomorph (coordsHomeo Kv σ ι hdeg hσ).symm

  have hsupp : ∀ x : GL (Fin 2) (L ⊗[K] Kv),
      (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x ∈ semiLocalIntegralSet K L v) ↔
        ∀ j, (Ψ x j)⁻¹ * diagUnits2 (unitCoord Kv σ ι α j) (unitCoord Kv σ ι β j) * Ψ x (finRotate (n + 1) j) ∈
          localIntegralSet K v := by
    intro x
    rw [mem_semiLocalIntegralSet_iff K L v σ ι hdeg hσ]
    refine forall_congr' fun j => ?_
    rw [← hΨ, coords_twistedConj_apply, ← hD, hDj]
  have hs1 : ∀ X : Fin (n + 1) → GL (Fin 2) Kv,
      (∀ j, (X j)⁻¹ * diagUnits2 (unitCoord Kv σ ι α j) (unitCoord Kv σ ι β j) * X (finRotate (n + 1) j) ∈
          localIntegralSet K v) →
        ∫ t : localCentralizer K v (diagUnits2 a b), s (fun j => ((t : GL (Fin 2) Kv)) * X j) ∂τ = 1 := by
    intro X hX
    set x := Ψ.symm X with hx
    have hΨx : Ψ x = X := Ψ.apply_symm_apply X
    have hx' : x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x ∈ semiLocalIntegralSet K L v := by
      rw [hsupp, hΨx]; exact hX
    have hne : (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
        (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x) ≠ 0 := by
      rw [Set.indicator_of_mem hx']; exact one_ne_zero
    have hsec := hw'sec x hne
    have htr : ∀ t : localCentralizer K v (diagUnits2 a b),
        s (fun j => ((t : GL (Fin 2) Kv)) * X j) = w' ((eT t : GL (Fin 2) (L ⊗[K] Kv)) * x) := by
      intro t
      rw [hs]
      simp only []
      congr 1
      apply Ψ.injective
      rw [Ψ.apply_symm_apply, map_mul, hΨx, heT, torusEquiv_apply_val, hΨ, coords_toTensorGL]
      rfl
    simp_rw [htr]
    rw [hτdef, integral_tau K L v σ ι hdeg hσ a b α β hT τ' (fun t' => w' ((t' : GL (Fin 2) (L ⊗[K] Kv)) * x))]
    exact hsec

  have hred := AutomorphicForm.integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq
    K v n a b hab (fun j => unitCoord Kv σ ι α j) (fun j => unitCoord Kv σ ι β j) hprodα hprodβ τ hτ c hcK
    (localHaar K v) (localHaar_localIntegralSet K v) s hs0 hsm hsc hs1

  set FP : (Fin (n + 1) → GL (Fin 2) Kv) → ℂ := fun X =>
    (Set.pi Set.univ fun _ : Fin (n + 1) => localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (fun j => (X j)⁻¹ * diagUnits2 (unitCoord Kv σ ι α j) (unitCoord Kv σ ι β j) * X (finRotate (n + 1) j)) *
      ((∑ j, LocalWeight.weight (X j) : ℝ) : ℂ) * (s X : ℂ) with hFP
  have hint : (fun x : GL (Fin 2) (L ⊗[K] Kv) =>
      (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x) *
        (semiLocalWeight K L v x : ℂ) * (w' x : ℂ)) = fun x => FP (Ψ x) := by
    funext x
    simp only [hFP]
    congr 2
    ·
      have hiff := hsupp x
      by_cases hx : x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x ∈ semiLocalIntegralSet K L v
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
        rw [Set.mem_univ_pi]
        exact hiff.1 hx
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        rw [Set.mem_univ_pi]
        exact fun h => hx (hiff.2 h)
    · rw [semiLocalWeight_eq_sum K L v σ ι hdeg hσ]
    · rw [hs]
      simp only []
      rw [Ψ.symm_apply_apply]
  have htrans : ∫ x, FP (Ψ x) ∂(semiLocalHaar K L v) =
      ∫ X, FP X ∂(Measure.pi fun _ : Fin (n + 1) => localHaar K v) := by
    rw [← map_coords_semiLocalHaar K L v σ ι hdeg hσ, hΨ, ← coordsₜ_eq]
    exact (integral_map_equiv (coordsₜ Kv σ ι hdeg hσ).toHomeomorph.toMeasurableEquiv FP).symm

  change ∫ x, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 α β * sigmaGL K L Kv σ x) *
      (semiLocalWeight K L v x : ℂ) * (w' x : ℂ) ∂(semiLocalHaar K L v) = _
  rw [hint, htrans, hFP, hred, ← finrank_eq_succ K L]

end Main

end P2mCTSplitGlue
p2m_reactivate "P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension.P2mCTSplitGlue"

end
p2m_reactivate "P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension.P2mCTSplitGlue"

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hsplit : Nontrivial (v.Extension (𝓞 L)))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
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
  obtain ⟨hgal, -, -⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  haveI := hgal
  obtain ⟨ι⟩ := P2mCTSplitGlue.nonempty_algHom_of_nontrivial K L v hprime hsplit
  haveI := hτ'
  have h := P2mCTSplitGlue.main K L v σ ι hprime hσ a b hab m hm α β hN τ' hτ'1 J' hJ'
  rw [h]
  split_ifs <;> simp

end S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension
end P2MW
export P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension (solution)
