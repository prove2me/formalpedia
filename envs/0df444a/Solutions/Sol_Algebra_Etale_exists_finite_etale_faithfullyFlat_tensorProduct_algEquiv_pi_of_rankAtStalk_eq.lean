-- Prove2me | solution 1 for Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/522363bf-b7c4-5499-8b1c-e6fa96985930

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace Algebra
p2m_export "Algebra" "Etale.of_isLocalizationAway TensorProduct.rid TensorProduct.lift_tmul mk algebraMap TensorProduct.lid TensorProduct.congr FormallyUnramified TensorProduct.lift TensorProduct.prodRight FiniteType Etale.comp Etale id TensorProduct.cancelBaseChange subsingleton commutes'"
namespace Etale
p2m_export "Algebra.Etale" "of_isLocalizationAway comp mk"
namespace SplitAux
p2m_open "Algebra.Etale Algebra"

section Diag

variable (S D : Type u) [CommRing S] [CommRing D] [Algebra S D]

noncomputable def mulHom : D ⊗[S] D →ₐ[D] D :=
  Algebra.TensorProduct.lift (AlgHom.id D D) (IsScalarTower.toAlgHom S D D) (fun x y => Commute.all x y)

@[scoped simp] theorem mulHom_tmul (x y : D) : mulHom S D (x ⊗ₜ y) = x * y := by
  simp [mulHom, Algebra.TensorProduct.lift_tmul]

theorem mulHom_surjective : Function.Surjective (mulHom S D) :=
  fun x => ⟨x ⊗ₜ 1, by rw [mulHom_tmul, mul_one]⟩

theorem ker_mulHom_eq : RingHom.ker (mulHom S D) = KaehlerDifferential.ideal S D := by
  ext x
  rw [RingHom.mem_ker, KaehlerDifferential.ideal, RingHom.mem_ker]
  constructor <;> intro h <;> exact h

variable {S D} in

noncomputable def splitHom (e : D ⊗[S] D) :
    D ⊗[S] D →ₐ[D] D × ((D ⊗[S] D) ⧸ Ideal.span {1 - e}) :=
  (mulHom S D).prod (Ideal.Quotient.mkₐ D (Ideal.span {1 - e}))

variable {S D} in
theorem splitHom_bijective {e : D ⊗[S] D} (he : IsIdempotentElem e)
    (hker : RingHom.ker (mulHom S D) = Ideal.span {e}) : Function.Bijective (splitHom e) := by
  have hme : mulHom S D e = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self e
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : mulHom S D x = 0 := congr_arg Prod.fst hx
    have h2 : Ideal.Quotient.mk (Ideal.span {1 - e}) x = 0 := congr_arg Prod.snd hx
    have hxI : x ∈ Ideal.span {e} := hker ▸ (RingHom.mem_ker.mpr h1)
    have hxJ : x ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.mp h2
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxI
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hxJ
    have h3 : x * e = 0 := by
      rw [← hb, mul_assoc, sub_mul, one_mul, he.eq, sub_self, mul_zero]
    have h4 : x * (1 - e) = 0 := by
      rw [← ha, mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]
    calc x = x * e + x * (1 - e) := by ring
      _ = 0 := by rw [h3, h4, add_zero]
  · rintro ⟨d, y⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨(1 - e) * (d ⊗ₜ 1) + e * y, ?_⟩
    refine Prod.ext ?_ ?_
    · show mulHom S D _ = d
      simp [map_add, map_mul, map_sub, hme, mulHom_tmul]
    · show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ y
      rw [Ideal.Quotient.eq]
      rw [show (1 - e) * (d ⊗ₜ[S] (1 : D)) + e * y - y = (d ⊗ₜ 1 - y) * (1 - e) by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

section

variable [Algebra.FormallyUnramified S D] [Algebra.FiniteType S D]

theorem exists_idempotent_ker :
    ∃ e : D ⊗[S] D, IsIdempotentElem e ∧ RingHom.ker (mulHom S D) = Ideal.span {e} := by
  have hI : IsIdempotentElem (RingHom.ker (mulHom S D).toRingHom) := by
    rw [show (RingHom.ker (mulHom S D).toRingHom) = KaehlerDifferential.ideal S D from ker_mulHom_eq S D]
    rw [← Ideal.cotangent_subsingleton_iff]
    exact (inferInstance : Subsingleton (KaehlerDifferential S D))
  have hfg : (RingHom.ker (mulHom S D).toRingHom).FG := by
    rw [show (RingHom.ker (mulHom S D).toRingHom) = KaehlerDifferential.ideal S D from ker_mulHom_eq S D]
    exact KaehlerDifferential.ideal_fg S D
  obtain ⟨e, he, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hI
  exact ⟨e, he, hspan⟩

end

theorem rankAtStalk_self' (R : Type u) [CommRing R] : Module.rankAtStalk (R := R) R = 1 := by
  cases subsingleton_or_nontrivial R
  · funext p; exact ((inferInstance : IsEmpty (PrimeSpectrum R)).false p).elim
  · exact Module.rankAtStalk_self

theorem diag_alg [Algebra.Etale S D] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra D C), Algebra.Etale D C ∧
      Nonempty ((D ⊗[S] D) ≃ₐ[D] D × C) := by
  obtain ⟨e, he, hker⟩ := exists_idempotent_ker S D
  haveI : IsLocalization.Away e ((D ⊗[S] D) ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  haveI : Algebra.Etale (D ⊗[S] D) ((D ⊗[S] D) ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  haveI : Algebra.Etale D (D ⊗[S] D) := inferInstance
  exact ⟨(D ⊗[S] D) ⧸ Ideal.span {1 - e}, inferInstance, inferInstance,
    Algebra.Etale.comp D (D ⊗[S] D) _,
    ⟨AlgEquiv.ofBijective (splitHom e) (splitHom_bijective he hker)⟩⟩

theorem diag [Module.Finite S D] [Algebra.Etale S D]
    (m : ℕ) (hrank : ∀ p, Module.rankAtStalk (R := S) D p = m + 1) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra D C), Module.Finite D C ∧ Algebra.Etale D C ∧
      (∀ q, Module.rankAtStalk (R := D) C q = m) ∧ Nonempty ((D ⊗[S] D) ≃ₐ[D] D × C) := by
  obtain ⟨C, _, _, hEt, ⟨φ⟩⟩ := diag_alg S D
  haveI : Module.Finite D (D × C) := Module.Finite.equiv φ.toLinearEquiv
  haveI hFin : Module.Finite D C :=
    Module.Finite.of_surjective (LinearMap.snd D D C) Prod.snd_surjective
  haveI : Module.Flat D C := inferInstance
  refine ⟨C, inferInstance, inferInstance, hFin, hEt, fun q => ?_, ⟨φ⟩⟩
  have key : Module.rankAtStalk (R := D) (D × C) q = m + 1 := by
    rw [← congr_fun (Module.rankAtStalk_eq_of_equiv φ.toLinearEquiv) q]
    exact (Module.rankAtStalk_baseChange q).trans (hrank _)
  have key2 : Module.rankAtStalk (R := D) D q + Module.rankAtStalk (R := D) C q = m + 1 := by
    have h3 := congr_fun (Module.rankAtStalk_prod (R := D) D C) q
    rw [Pi.add_apply] at h3
    rw [← h3]
    exact key
  rw [congr_fun (rankAtStalk_self' D) q, Pi.one_apply] at key2
  omega

end Diag

section Induct

def algEquivOfSubsingleton (T A B : Type*) [CommSemiring T] [Semiring A] [Semiring B]
    [Algebra T A] [Algebra T B] [Subsingleton A] [Subsingleton B] : A ≃ₐ[T] B where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

def prodPiFinSuccAlgEquiv (T A : Type*) [CommSemiring T] [Semiring A] [Algebra T A] (m : ℕ) :
    (A × (Fin m → A)) ≃ₐ[T] (Fin (m + 1) → A) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  left_inv p := by obtain ⟨a, f⟩ := p; simp
  right_inv f := Fin.cons_self_tail f
  map_mul' p q := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_add' p q := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  commutes' t := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem split_induct (m : ℕ) : ∀ (S D : Type u) [CommRing S] [CommRing D] [Algebra S D]
    [Module.Finite S D] [Algebra.Etale S D], (∀ p, Module.rankAtStalk (R := S) D p = m) →
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S') (_ : Module.Finite S S')
      (_ : Algebra.Etale S S') (_ : Module.FaithfullyFlat S S'),
      Nonempty ((S' ⊗[S] D) ≃ₐ[S'] (Fin m → S')) := by
  induction m with
  | zero =>
    intro S D _ _ _ _ _ hrank
    have hD : Subsingleton D := Module.rankAtStalk_eq_zero_iff_subsingleton.mp (funext hrank)
    haveI : Subsingleton (S ⊗[S] D) := (Algebra.TensorProduct.lid S D).toEquiv.subsingleton
    exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨algEquivOfSubsingleton S _ _⟩⟩
  | succ m ih =>
    intro S D _ _ _ _ _ hrank
    haveI : Module.FaithfullyFlat S D := Module.FaithfullyFlat.of_comap_surjective
      (PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective.mp (fun p => by rw [hrank]; omega))
    obtain ⟨C, _, _, hCfin, hCet, hCrank, ⟨δ⟩⟩ := diag S D m hrank
    obtain ⟨S', _, _, _, _, _, ⟨ψ⟩⟩ := ih D C hCrank
    letI : Algebra S S' := ((algebraMap D S').comp (algebraMap S D)).toAlgebra
    haveI : IsScalarTower S D S' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    refine ⟨S', inferInstance, inferInstance, Module.Finite.trans D S', Algebra.Etale.comp S D S',
      Module.FaithfullyFlat.trans S D S', ⟨?_⟩⟩
    exact (Algebra.TensorProduct.cancelBaseChange S D S' S' D).symm.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : S' ≃ₐ[S'] S') δ).trans <|
      (Algebra.TensorProduct.prodRight D S' S' D C).trans <|
      (AlgEquiv.prodCongr (Algebra.TensorProduct.rid D S' S') ψ).trans <|
      prodPiFinSuccAlgEquiv S' S' m

end Induct

end Algebra.Etale.SplitAux
p2m_reactivate "P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.Algebra P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.Algebra.Etale P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.Algebra.Etale.SplitAux"
p2m_reactivate "P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.Algebra P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.Algebra.Etale"
p2m_reactivate "P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.Algebra"

theorem solution
    (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B]
    (n : ℕ) (hn : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) B p = n) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin n → R')) :=
  Algebra.Etale.SplitAux.split_induct n R B hn

end S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
end P2MW
export P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq (solution)
