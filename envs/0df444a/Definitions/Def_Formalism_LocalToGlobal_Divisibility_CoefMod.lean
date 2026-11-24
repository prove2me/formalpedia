-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
-- name    : Formalism_LocalToGlobal_Divisibility_CoefMod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:31.039486+00:00
-- url     : https://prove2.me/theorems/e68e10fb-3582-4331-aed9-107c71c7b819
-- title:
--   Coef Mod
-- statement:
--   Definitions and structural lemmas for Coef Mod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefMod.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Theorems.Thm_Formalism_GradedWeylDivisibility_blockActTensor
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSIdxFinite
import Theorems.Thm_Formalism_GradedWeylDivisibility_tensorBasis
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.L2.DIV
open Formalism.BasicNotions
section Fock
variable {K : Type} [Field K] [StarRing K] {σ : Type}
def mfact (m : σ →₀ ℕ) : ℕ := ∏ k ∈ m.support, (m k).factorial
def fockS (f g : MvPolynomial σ K) : K :=
  ∑ m ∈ f.support, star (f.coeff m) * g.coeff m * (mfact m : K)
theorem fockS_eq_sum (f g : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    fockS f g = ∑ m ∈ s, star (f.coeff m) * g.coeff m * (mfact m : K) := by
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [notMem_support_iff.mp hm]
  simp
def fockL : MvPolynomial σ K →ₗ⋆[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) fockS
    (by
      classical
      intro f f' g
      rw [fockS_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
        fockS_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
        fockS_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_add, star_add]; ring)
    (by
      intro c f g
      rw [fockS_eq_sum (c • f) g f.support (support_smul), fockS, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_smul, smul_eq_mul, star_mul', starRingEnd_apply]; ring)
    (by
      intro f g g'
      simp only [fockS, coeff_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [fockS, coeff_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)
end Fock
section Space
variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
abbrev Pol (K ι : Type) [Field K] (n : ℕ) : Type := MvPolynomial (ι × Fin n × Fin n) K
def ten (f : ι → MvPolynomial (Fin n × Fin n) K) : Pol K ι n := ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)
def VV (K : Type) [Field K] (lam : ι → DomWeight n) : Submodule K (Pol K ι n) :=
  Formalism.GradedWeylDivisibility.tensorLat K K fun τ => nablaSq K n (lam τ)
def detTwK (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : K := ∏ τ, detPow K n (g τ) (lam τ).detShift
def trAct (g : ι → GL (Fin n) K) : Pol K ι n →ₐ[K] Pol K ι n :=
  Formalism.GradedWeylDivisibility.blockAct K fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ
def actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : Pol K ι n →ₗ[K] Pol K ι n :=
  detTwK lam g • (trAct g).toLinearMap
theorem blockAct_comp (g h : ι → Matrix (Fin n) (Fin n) K) :
    (Formalism.GradedWeylDivisibility.blockAct K (n := n) g).comp (Formalism.GradedWeylDivisibility.blockAct K h) = Formalism.GradedWeylDivisibility.blockAct K fun τ => h τ * g τ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply]
  simp only [algebraMap_eq, Finset.mul_sum, Finset.sum_mul, ← C_mul]
  rw [Finset.sum_comm]
  simp [C_mul, mul_assoc]
theorem blockAct_one : Formalism.GradedWeylDivisibility.blockAct K (n := n) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [Formalism.GradedWeylDivisibility.blockAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.2.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
theorem trAct_mul (g h : ι → GL (Fin n) K) : trAct (g * h) = (trAct g).comp (trAct h) := by
  unfold trAct
  rw [blockAct_comp]
  congr 1
  funext τ
  simp [Matrix.transpose_mul]
theorem trAct_one : trAct (1 : ι → GL (Fin n) K) = AlgHom.id K _ := by
  unfold trAct
  rw [← blockAct_one]
  congr 1
  funext τ
  simp
theorem detTwK_mul (lam : ι → DomWeight n) (g h : ι → GL (Fin n) K) :
    detTwK lam (g * h) = detTwK lam g * detTwK lam h := by
  unfold detTwK
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp [detPow, mul_zpow]
theorem detTwK_one (lam : ι → DomWeight n) : detTwK lam (1 : ι → GL (Fin n) K) = 1 := by
  unfold detTwK
  refine Finset.prod_eq_one fun τ _ => ?_
  simp [detPow]
def rhoP (lam : ι → DomWeight n) : (ι → GL (Fin n) K) →* Module.End K (Pol K ι n) where
  toFun g := actP lam g
  map_one' := by
    apply LinearMap.ext
    intro F
    simp [actP, detTwK_one, trAct_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    simp only [actP, detTwK_mul, trAct_mul, Module.End.mul_apply, mul_comm (detTwK lam g), LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, map_smul, smul_smul]
theorem polyAction_mem_VV (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) {F : Pol K ι n} (hF : F ∈ VV K lam) :
    actP lam g F ∈ VV K lam := by
  have h := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n
      (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).2
    (fun τ => nablaSq K n (lam τ)) (fun τ => nablaSq K n (lam τ))
    (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF
  exact (VV K lam).smul_mem (detTwK lam g) h
def rhoK (lam : ι → DomWeight n) : (ι → GL (Fin n) K) →* Module.End K (VV K lam) where
  toFun g := (actP lam g).restrict fun _ hF => polyAction_mem_VV lam g hF
  map_one' := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    have := congrArg (fun φ => φ F.1) (rhoP lam).map_one
    simpa [rhoP] using this
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    have := congrArg (fun φ => φ F.1) ((rhoP lam).map_mul g h)
    simpa [rhoP] using this
variable [StarRing K]
def extNorm (K : Type) [Field K] [StarRing K] (lam : ι → DomWeight n) : K :=
  ∏ τ, fockS (extremal K n (lam τ)) (extremal K n (lam τ))
def gramTw (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) : K :=
  ∏ τ, (G τ).det ^ (lam τ).detShift
def pairP (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) :
    Pol K ι n →ₗ⋆[K] Pol K ι n →ₗ[K] K :=
  (gramTw lam G / extNorm K lam) •
    (fockL (K := K)).compl₂ (Formalism.GradedWeylDivisibility.blockAct K fun τ => (G τ)ᵀ).toLinearMap
def pairK (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) :
    VV K lam →ₗ⋆[K] VV K lam →ₗ[K] K :=
  (pairP lam G).domRestrict₁₂ (VV K lam) (VV K lam)
end Space
section Lattices
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
def toK (K : Type) [Field K] [NumberField K] (σ : Type) : MvPolynomial σ (𝓞 K) →ₗ[𝓞 K] MvPolynomial σ K :=
  (mapAlgHom (Algebra.ofId (𝓞 K) K)).toLinearMap
def nabStd (K : Type) [Field K] [NumberField K] (lam : ι → DomWeight n) : Submodule (𝓞 K) (Pol K ι n) :=
  Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K fun τ => (nablaSq (𝓞 K) n (lam τ)).map (toK K _)
def delStd (K : Type) [Field K] [NumberField K] (lam : ι → DomWeight n) : Submodule (𝓞 K) (Pol K ι n) :=
  Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K fun τ => (delSq (𝓞 K) n (lam τ)).map (toK K _)
def colLat (B : GL (Fin n) K) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range fun j : Fin n => fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j)
def IsBasisAt (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (B : GL (Fin n) K) : Prop :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B)
def transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Pol K ι n) :=
  ⨅ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) (_ : ∀ τ, IsBasisAt w (M τ) (B τ)),
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).comap ((actP lam B⁻¹).restrictScalars (𝓞 K))
def nabP (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Pol K ι n) :=
  transLat lam (nabStd K lam) M
def delP (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Pol K ι n) :=
  transLat lam (delStd K lam) M
def nabK (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (VV K lam) :=
  (nabP lam M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))
def delK (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (VV K lam) :=
  (delP lam M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))
def dualFr (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) where
  carrier := {φ | ∀ x ∈ M, φ ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)}
  add_mem' := by
    intro a b ha hb x hx
    rw [add_dotProduct]
    exact add_mem (ha x hx) (hb x hx)
  zero_mem' := by
    intro x _
    rw [zero_dotProduct]
    exact zero_mem _
  smul_mem' := by
    intro c a ha x hx
    rw [smul_dotProduct]
    exact Submodule.smul_mem _ c (ha x hx)
def hdualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    Submodule (𝓞 K) (Fin n → K) where
  carrier := {x | ∀ y ∈ M, star y ⬝ᵥ (G *ᵥ x) ∈ (1 : Submodule (𝓞 K) K)}
  add_mem' := by
    intro a b ha hb y hy
    rw [Matrix.mulVec_add, dotProduct_add]
    exact add_mem (ha y hy) (hb y hy)
  zero_mem' := by
    intro y _
    rw [Matrix.mulVec_zero, dotProduct_zero]
    exact zero_mem _
  smul_mem' := by
    intro c a ha y hy
    rw [Matrix.mulVec_smul, dotProduct_smul]
    exact Submodule.smul_mem _ c (ha y hy)
def gLat (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) :=
  M.map ((Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) K)).restrictScalars (𝓞 K))
end Lattices
section Basis
variable {ι : Type} [Fintype ι] {n : ℕ}
def ssB (K : Type) [Field K] (ν : Fin n → ℕ) : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) K :=
  (Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose
abbrev VVIdx (lam : ι → DomWeight n) : Type := ∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW
instance (lam : ι → DomWeight n) : Finite (VVIdx lam) :=
  haveI : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  Pi.finite
instance (lam : ι → DomWeight n) : Fintype (VVIdx lam) := Fintype.ofFinite _
def bVVfun (K : Type) [Field K] (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n :=
  ten fun τ => ssB K (lam τ).natW (i τ)
theorem bVVfun_spec (K : Type) [Field K] (lam : ι → DomWeight n) :
    LinearIndependent K (bVVfun K lam) ∧ Submodule.span K (Set.range (bVVfun K lam)) = VV K lam := by
  classical
  exact Formalism.GradedWeylDivisibility.tensorBasis K K ι n n (fun τ => Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW)
    (fun τ => nablaSq K n (lam τ)) (fun τ => ssB K (lam τ).natW)
    (fun τ => (Formalism.GradedWeylDivisibility.sSBasis K n n (lam τ).natW).choose_spec.1.1)
    (fun τ => (Formalism.GradedWeylDivisibility.sSBasis K n n (lam τ).natW).choose_spec.1.2.1)
def bVV (K : Type) [Field K] (lam : ι → DomWeight n) : Module.Basis (VVIdx lam) K (VV K lam) :=
  (Module.Basis.span (bVVfun_spec K lam).1).map (LinearEquiv.ofEq _ _ (bVVfun_spec K lam).2)
end Basis
section ESide
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)
def tauLat (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) ((fun (x : Fin n → E) (a : Fin n) => emb τ (x a)) '' (L : Set (Fin n → E)))
def embGL : GL (Fin n) E →* (ι → GL (Fin n) K) := MonoidHom.pi fun τ => Formalism.UG.bc (emb τ)
def invTrK : (ι → GL (Fin n) K) →* (ι → GL (Fin n) K) where
  toFun g τ := inside₂ K n (g τ)
  map_one' := by
    funext τ
    apply Units.ext
    simp [inside₂]
  map_mul' g h := by
    funext τ
    apply Units.ext
    simp [inside₂, Matrix.transpose_mul]
def gramK (J : Matrix (Fin n) (Fin n) E) : ι → Matrix (Fin n) (Fin n) K := fun τ => J.map (emb τ)
def gramKd (J : Matrix (Fin n) (Fin n) E) : ι → Matrix (Fin n) (Fin n) K := fun τ => ((J.map (emb τ))⁻¹)ᵀ
def rhoV (lam : ι → DomWeight n) : GL (Fin n) E →* Module.End K (VV K lam) := (rhoK lam).comp (embGL emb)
def pairV [StarRing K] (lam : ι → DomWeight n) (J : Matrix (Fin n) (Fin n) E) :
    VV K lam →ₗ⋆[K] VV K lam →ₗ[K] K := pairK lam (gramK emb J)
def nabAt (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (VV K lam) :=
  nabK lam fun τ => tauLat emb τ L
def delAt (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (VV K lam) :=
  delK lam fun τ => tauLat emb τ L
def rhoVr (lam : ι → DomWeight n) : GL (Fin n) E →* Module.End K (VV K lam) :=
  (rhoK lam).comp (invTrK.comp (embGL emb))
def pairVr [StarRing K] (lam : ι → DomWeight n) (J : Matrix (Fin n) (Fin n) E) :
    VV K lam →ₗ⋆[K] VV K lam →ₗ[K] K := pairK lam (gramKd emb J)
def nabAtr (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (VV K lam) :=
  nabK lam fun τ => dualFr (tauLat emb τ L)
def delAtr (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (VV K lam) :=
  delK lam fun τ => dualFr (tauLat emb τ L)
end ESide
end Formalism.L2.DIV


