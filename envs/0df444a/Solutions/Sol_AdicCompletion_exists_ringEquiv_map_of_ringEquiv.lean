-- Prove2me | solution 1 for AdicCompletion.exists_ringEquiv_map_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a32aca94-8026-5797-bae1-ad4207f2bad3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_ringEquiv_map_of_ringEquiv

set_option autoImplicit false

universe u v

namespace BDescAdic

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

noncomputable def levelMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) (n : ℕ) :
    AdicCompletion I R →+* S ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f (hf n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)

theorem levelMap_compat (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (levelMap I J f hf n) = levelMap I J f hf m := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [levelMap, RingHom.coe_comp, Function.comp_apply]
  have hn : (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n) (AdicCompletion.mk I R a)
        = Ideal.Quotient.mk (I ^ n) (a.val n) := AdicCompletion.evalₐ_mk I n a
  have hm : (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m) (AdicCompletion.mk I R a)
        = Ideal.Quotient.mk (I ^ m) (a.val m) := AdicCompletion.evalₐ_mk I m a
  rw [hn, hm, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  show Ideal.Quotient.factor _ (Ideal.Quotient.mk (J ^ n) (f (a.val n))) = Ideal.Quotient.mk (J ^ m) (f (a.val m))
  rw [Ideal.Quotient.factor_mk]
  have := congrArg (Ideal.quotientMap (J ^ m) f (hf m)) (AdicCompletion.Ideal.mk_eq_mk I hle a)
  rwa [Ideal.quotientMap_mk, Ideal.quotientMap_mk] at this

noncomputable def transportHom (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (levelMap I J f hf) (fun hle => levelMap_compat I J f hf hle)

theorem evalₐ_transportHom (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (transportHom I J f hf x) = Ideal.quotientMap (J ^ n) f (hf n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J (levelMap I J f hf) (fun hle => levelMap_compat I J f hf hle) n x

end BDescAdic
open BDescAdic in
theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (I : Ideal R) (e : R ≃+* S) :
    ∃ ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion (I.map e) S) (e r) := by
  classical
  have hJn : ∀ n : ℕ, (I.map e) ^ n = (I ^ n).map (e : R →+* S) := fun n => (Ideal.map_pow (e : R →+* S) I n).symm
  have hf : ∀ n : ℕ, I ^ n ≤ ((I.map e) ^ n).comap (e : R →+* S) := by
    intro n x hx
    rw [Ideal.mem_comap, hJn]
    exact Ideal.mem_map_of_mem _ hx
  have hg : ∀ n : ℕ, (I.map e) ^ n ≤ (I ^ n).comap (e.symm : S →+* R) := by
    intro n y hy
    rw [hJn, Ideal.map_comap_of_equiv] at hy
    exact hy
  let φ := transportHom I (I.map e) (e : R →+* S) hf
  let ψ := transportHom (I.map e) I (e.symm : S →+* R) hg
  have hφψ : ∀ y, φ (ψ y) = y := by
    intro y
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [evalₐ_transportHom, evalₐ_transportHom]
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (I.map e) n y)
    rw [← hs, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    simp
  have hψφ : ∀ x, ψ (φ x) = x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [evalₐ_transportHom, evalₐ_transportHom]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [← hr, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    simp
  let ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S :=
    { toFun := φ, invFun := ψ, left_inv := hψφ, right_inv := hφψ,
      map_mul' := fun x y => φ.map_mul x y, map_add' := fun x y => φ.map_add x y }
  refine ⟨ê, fun r => ?_⟩
  show φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion (I.map e) S) (e r)
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_transportHom, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  rfl

end S_AdicCompletion_exists_ringEquiv_map_of_ringEquiv
end P2MW
export P2MW.S_AdicCompletion_exists_ringEquiv_map_of_ringEquiv (solution)
