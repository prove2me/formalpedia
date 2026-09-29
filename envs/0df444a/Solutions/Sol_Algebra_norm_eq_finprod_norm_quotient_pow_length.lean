-- Prove2me | solution 1 for Algebra.norm_eq_finprod_norm_quotient_pow_length
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/dd4ea01b-319e-5b33-b046-4a69f840333e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length

set_option maxHeartbeats 800000
set_option autoImplicit false

universe u v w

namespace NormDecomp

theorem moduleFinite_localization_atPrime_of_moduleFinite
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (m : MaximalSpectrum A) :
    Module.Finite K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K A (Localization.AtPrime m.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)

theorem finrank_eq_sum_finrank_localization_atPrime
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [Fintype (MaximalSpectrum A)] :
    Module.finrank K A = ∑ m : MaximalSpectrum A, Module.finrank K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : ∀ m : MaximalSpectrum A, Module.Finite K (Localization.AtPrime m.asIdeal) :=
    fun m => moduleFinite_localization_atPrime_of_moduleFinite K A m
  let e : A ≃ₗ[K] MaximalSpectrum.PiLocalization A :=
    (MaximalSpectrum.toPiLocalizationEquiv A).toLinearEquiv.restrictScalars K
  rw [e.finrank_eq]
  exact Module.finrank_pi_fintype K

end NormDecomp

namespace NormDecomp

open IsLocalRing

theorem finrank_eq_finrank_residueField_mul_length
    (K : Type u) (L : Type v) (M : Type w) [Field K] [CommRing L] [IsLocalRing L] [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Module.Finite K M] :
    (Module.finrank K M : ℕ∞) = (Module.finrank K (IsLocalRing.ResidueField L) : ℕ∞) * Module.length L M := by

  suffices h : ∀ n : ℕ, ∀ (M : Type w) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
      [Module.Finite K M], Module.finrank K M = n →
      (Module.finrank K M : ℕ∞) = (Module.finrank K (IsLocalRing.ResidueField L) : ℕ∞) * Module.length L M from
    h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn
  by_cases hM : Subsingleton M
  · rw [Module.finrank_zero_of_subsingleton, Module.length_eq_zero_iff.mpr hM, Nat.cast_zero, mul_zero]
  · have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM

    haveI : IsArtinian L M := isArtinian_of_tower K inferInstance
    haveI : IsNoetherian L M := isNoetherian_of_tower K inferInstance
    obtain ⟨S, hS⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule L M)).resolve_left top_ne_bot
    obtain ⟨hSatom, -⟩ := hS
    haveI hSsimple : IsSimpleModule L S := isSimpleModule_iff_isAtom.mpr hSatom

    obtain ⟨I, hImax, ⟨eS⟩⟩ := isSimpleModule_iff_quot_maximal.mp hSsimple
    have hI : I = maximalIdeal L := IsLocalRing.eq_maximalIdeal hImax
    subst hI
    have hfinS : Module.finrank K S = Module.finrank K (IsLocalRing.ResidueField L) :=
      (eS.restrictScalars K).finrank_eq

    haveI : Module.Finite K (M ⧸ S) :=
      Module.Finite.of_surjective (S.mkQ.restrictScalars K) (Submodule.mkQ_surjective S)
    have hdim : Module.finrank K M = Module.finrank K S + Module.finrank K (M ⧸ S) := by
      rw [← (Submodule.Quotient.restrictScalarsEquiv K S).finrank_eq, add_comm]
      exact (Submodule.finrank_quotient_add_finrank (S.restrictScalars K)).symm
    have hκpos : 0 < Module.finrank K (IsLocalRing.ResidueField L) := by
      rw [← hfinS]
      haveI : Nontrivial S := IsSimpleModule.nontrivial L S
      haveI : Module.Finite K S := Module.Finite.of_injective (S.subtype.restrictScalars K) (Submodule.injective_subtype S)
      exact Module.finrank_pos
    have hlt : Module.finrank K (M ⧸ S) < n := by omega
    have ihq := ih _ hlt (M ⧸ S) rfl

    have hlen : Module.length L M = 1 + Module.length L (M ⧸ S) := by
      rw [Module.length_eq_add_of_exact S.subtype S.mkQ (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
        (LinearMap.exact_subtype_mkQ S), Module.length_eq_one_iff.mpr hSsimple]
    rw [hdim, hfinS, Nat.cast_add, ihq, hlen, mul_add, mul_one]

end NormDecomp

open IsLocalRing
open scoped TensorProduct

namespace NormDecomp

theorem length_eq_of_orderIso {R : Type*} {R' : Type*} [Ring R] [Ring R'] {M : Type*} {M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (e : Submodule R M ≃o Submodule R' M') :
    Module.length R M = Module.length R' M' := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso e

theorem length_self_eq_of_ringEquiv {R : Type*} {R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' :=
  (length_eq_of_orderIso (Ideal.relIsoOfBijective e e.bijective)).symm

noncomputable def restrictScalarsOrderIsoOfSurjective (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
    (N : Type*) [AddCommGroup N] [Module T N] [Module S N] [IsScalarTower S T N]
    (h : Function.Surjective (algebraMap S T)) : Submodule T N ≃o Submodule S N where
  toFun p := p.restrictScalars S
  invFun p :=
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun t n hn => by
        obtain ⟨s, rfl⟩ := h t
        rw [algebraMap_smul]
        exact p.smul_mem s hn }
  left_inv p := by ext; rfl
  right_inv p := by ext; rfl
  map_rel_iff' := Iff.rfl

theorem length_eq_of_surjective_algebraMap (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
    (N : Type*) [AddCommGroup N] [Module T N] [Module S N] [IsScalarTower S T N]
    (h : Function.Surjective (algebraMap S T)) : Module.length S N = Module.length T N :=
  (length_eq_of_orderIso (restrictScalarsOrderIsoOfSurjective S T N h)).symm

theorem length_localization_atPrime_eq_of_isLocalization
    (B : Type u) [CommRing B] (S : Submonoid B) (A : Type v) [CommRing A] [Algebra B A] [IsLocalization S A]
    (𝔪 : Ideal A) [𝔪.IsPrime] :
    Module.length (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪) =
      Module.length (Localization.AtPrime (𝔪.comap (algebraMap B A))) (Localization.AtPrime (𝔪.comap (algebraMap B A))) := by
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔪) (𝔪.comap (algebraMap B A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S (Localization.AtPrime 𝔪) 𝔪
  exact length_self_eq_of_ringEquiv
    (IsLocalization.algEquiv (𝔪.comap (algebraMap B A)).primeCompl (Localization.AtPrime 𝔪)
      (Localization.AtPrime (𝔪.comap (algebraMap B A)))).toRingEquiv

theorem length_localizedModule_quotient_eq_length_localization
    (R : Type u) [CommRing R] (I : Ideal R) (Q : Ideal (R ⧸ I)) [Q.IsPrime] :
    Module.length (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
        (LocalizedModule (Q.comap (Ideal.Quotient.mk I)).primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) := by
  set P : Ideal R := Q.comap (Ideal.Quotient.mk I) with hP

  have hS : Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl = Q.primeCompl := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hz
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨s, hz, rfl⟩

  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl) (Localization.AtPrime Q) := by
    rw [hS]; infer_instance
  haveI hloc : IsLocalizedModule P.primeCompl
      (IsScalarTower.toAlgHom R (R ⧸ I) (Localization.AtPrime Q)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  let e₀ : LocalizedModule P.primeCompl (R ⧸ I) ≃ₗ[R] Localization.AtPrime Q :=
    IsLocalizedModule.iso P.primeCompl (IsScalarTower.toAlgHom R (R ⧸ I) (Localization.AtPrime Q)).toLinearMap

  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (Ideal.Quotient.mk I) hP
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      change algebraMap (R ⧸ I) (Localization.AtPrime Q) (Ideal.Quotient.mk I r) = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map])
  have hφ : Function.Surjective (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) := by
    intro z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
    obtain ⟨a', ha'⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : R ⧸ I)
    have hs'P : s' ∈ P.primeCompl := by
      change Ideal.Quotient.mk I s' ∉ Q
      rw [hs']; exact s.2
    refine ⟨IsLocalization.mk' _ a' ⟨s', hs'P⟩, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_mk']
    congr 1
    · exact Subtype.ext hs'
  let e : LocalizedModule P.primeCompl (R ⧸ I) ≃ₗ[Localization.AtPrime P] Localization.AtPrime Q :=
    LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P) e₀
  rw [e.length_eq]
  exact length_eq_of_surjective_algebraMap _ _ _ hφ

end NormDecomp

open Polynomial

namespace NormDecomp

theorem toMatrix_prod_eq_fromBlocks {K : Type u} [CommRing K] {N P : Type v} [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] {ιN ιP : Type*} [Fintype ιN] [Fintype ιP] [DecidableEq ιN] [DecidableEq ιP]
    (bN : Module.Basis ιN K N) (bP : Module.Basis ιP K P) (f : (N × P) →ₗ[K] (N × P)) :
    LinearMap.toMatrix (bN.prod bP) (bN.prod bP) f =
      Matrix.fromBlocks
        (LinearMap.toMatrix bN bN ((LinearMap.fst K N P).comp (f.comp (LinearMap.inl K N P))))
        (LinearMap.toMatrix bP bN ((LinearMap.fst K N P).comp (f.comp (LinearMap.inr K N P))))
        (LinearMap.toMatrix bN bP ((LinearMap.snd K N P).comp (f.comp (LinearMap.inl K N P))))
        (LinearMap.toMatrix bP bP ((LinearMap.snd K N P).comp (f.comp (LinearMap.inr K N P)))) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [LinearMap.toMatrix_apply, Matrix.fromBlocks, Module.Basis.prod_apply, Module.Basis.prod_repr_inl,
      Module.Basis.prod_repr_inr]

theorem charpoly_eq_charpoly_restrict_mul_charpoly_quotient
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : V →ₗ[K] V) (N : Submodule K V) (hN : N ≤ N.comap T) :
    T.charpoly = (T.restrict (p := N) (q := N) (fun x hx => hN hx)).charpoly * (N.mapQ N T hN).charpoly := by
  classical
  obtain ⟨P, hNP⟩ := N.exists_isCompl

  let e : V ≃ₗ[K] (N × P) := (Submodule.prodEquivOfIsCompl N P hNP).symm
  let T' : (N × P) →ₗ[K] (N × P) := e.conj T
  have hT' : T'.charpoly = T.charpoly := LinearEquiv.charpoly_conj e T
  have hsymm : ∀ (n : N) (p : P), e.symm (n, p) = (n : V) + (p : V) := fun n p => rfl
  have hT'apply : ∀ z, T' z = e (T (e.symm z)) := fun z => rfl

  have hdec : ∀ v : V, (((e v).1 : N) : V) + (((e v).2 : P) : V) = v := by
    intro v
    have := e.symm_apply_apply v
    rw [hsymm] at this
    exact this
  have heN : ∀ (v : V) (hv : v ∈ N), e v = (⟨v, hv⟩, 0) := by
    intro v hv
    apply e.symm.injective
    rw [LinearEquiv.symm_apply_apply, hsymm]
    simp

  let A := (LinearMap.fst K N P).comp (T'.comp (LinearMap.inl K N P))
  let D := (LinearMap.snd K N P).comp (T'.comp (LinearMap.inr K N P))
  have h21 : (LinearMap.snd K N P).comp (T'.comp (LinearMap.inl K N P)) = 0 := by
    apply LinearMap.ext
    intro n
    change (e (T (e.symm (n, 0)))).2 = 0
    rw [hsymm, Submodule.coe_zero, add_zero, heN (T n) (hN n.2)]
  have hA : A = T.restrict (p := N) (q := N) (fun x hx => hN hx) := by
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    change (((e (T (e.symm (n, 0)))).1 : N) : V) = T n
    rw [hsymm, Submodule.coe_zero, add_zero, heN (T n) (hN n.2)]
  let q : P ≃ₗ[K] (V ⧸ N) := (Submodule.quotientEquivOfIsCompl N P hNP).symm
  have hq : ∀ p : P, q p = Submodule.Quotient.mk (p : V) := fun p =>
    Submodule.quotientEquivOfIsCompl_symm_apply N P hNP p
  have hD : q.conj D = N.mapQ N T hN := by
    apply LinearMap.ext
    intro z
    obtain ⟨p, rfl⟩ := q.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hq p, Submodule.mapQ_apply, hq (D p)]
    change Submodule.Quotient.mk ((((e (T (e.symm (0, p)))).2 : P) : V)) = Submodule.Quotient.mk (T (p : V))
    rw [hsymm, Submodule.coe_zero, zero_add, Submodule.Quotient.eq]
    have h := hdec (T p)

    have h2 : (((e (T ↑p)).2 : P) : V) - ((((e (T ↑p)).1 : N) : V) + (((e (T ↑p)).2 : P) : V)) =
        -((((e (T ↑p)).1 : N) : V)) := by abel
    rw [h] at h2
    rw [h2]
    exact N.neg_mem (Submodule.coe_mem _)

  let bN := Module.Free.chooseBasis K N
  let bP := Module.Free.chooseBasis K P
  haveI : Fintype (Module.Free.ChooseBasisIndex K N) := Module.Free.ChooseBasisIndex.fintype K N
  haveI : Fintype (Module.Free.ChooseBasisIndex K P) := Module.Free.ChooseBasisIndex.fintype K P
  rw [← hT', ← LinearMap.charpoly_toMatrix T' (bN.prod bP), toMatrix_prod_eq_fromBlocks, h21, map_zero,
    Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
  change A.charpoly * D.charpoly = _
  rw [← LinearEquiv.charpoly_conj q D, hD, hA]
  try rfl

end NormDecomp

open Polynomial

namespace NormDecomp

theorem charpoly_eq_one_of_subsingleton' {K : Type v} [CommRing K] {V : Type w} [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V] [Subsingleton V] (f : V →ₗ[K] V) : f.charpoly = 1 := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  · exact Polynomial.eq_one_of_monic_natDegree_zero f.charpoly_monic
      (by rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])

theorem charpoly_pi {K : Type v} [CommRing K] (ι : Type u) [Fintype ι] :
    ∀ (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
      [∀ i, Module.Free K (M i)] [∀ i, Module.Finite K (M i)] (f : ∀ i, M i →ₗ[K] M i),
      (LinearMap.pi fun i => (f i).comp (LinearMap.proj i) : (∀ i, M i) →ₗ[K] ∀ i, M i).charpoly =
        ∏ i, (f i).charpoly := by
  refine @Fintype.induction_empty_option
    (fun (α : Type u) [Fintype α] => ∀ (M : α → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
      [∀ i, Module.Free K (M i)] [∀ i, Module.Finite K (M i)] (f : ∀ i, M i →ₗ[K] M i),
      (LinearMap.pi fun i => (f i).comp (LinearMap.proj i) : (∀ i, M i) →ₗ[K] ∀ i, M i).charpoly =
        ∏ i, (f i).charpoly) ?_ ?_ ?_ ι inferInstance
  · intro α β _ e hα M _ _ _ _ f
    classical
    letI : Fintype α := Fintype.ofEquiv β e.symm

    let L : (∀ a, M (e a)) ≃ₗ[K] (∀ b, M b) := LinearEquiv.piCongrLeft K M e
    have hconj : L.conj (LinearMap.pi fun a => (f (e a)).comp (LinearMap.proj a)) =
        LinearMap.pi fun i => (f i).comp (LinearMap.proj i) := by
      apply LinearMap.ext
      intro x
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [LinearEquiv.conj_apply_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      change (Equiv.piCongrLeft M e) _ (e a) = _
      rw [Equiv.piCongrLeft_apply_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      congr 1
    rw [← hconj, LinearEquiv.charpoly_conj, hα (fun a => M (e a)) (fun a => f (e a))]
    exact Fintype.prod_equiv e (fun a => (f (e a)).charpoly) (fun b => (f b).charpoly) (fun a => rfl)
  · intro M _ _ _ _ f
    rw [Fintype.prod_empty]
    exact charpoly_eq_one_of_subsingleton' _
  · intro α _ hα M _ _ _ _ f
    classical
    let L : (∀ i, M i) ≃ₗ[K] (M none × ∀ a, M (some a)) := LinearEquiv.piOptionEquivProd K
    have hconj : L.conj (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
        (f none).prodMap (LinearMap.pi fun a => (f (some a)).comp (LinearMap.proj a)) := by
      apply LinearMap.ext
      intro x
      rfl
    rw [← LinearEquiv.charpoly_conj L, hconj, LinearMap.charpoly_prodMap, hα (fun a => M (some a)) (fun a => f (some a)),
      Fintype.prod_option]

scoped instance moduleFinite_localization_atPrime_inst
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (m : MaximalSpectrum A) :
    Module.Finite K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K A (Localization.AtPrime m.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)

theorem charpoly_mulLeft_eq_prod_localization
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [Fintype (MaximalSpectrum A)]
    (a : A) :
    (LinearMap.mulLeft K a).charpoly =
      ∏ m : MaximalSpectrum A,
        (LinearMap.mulLeft K (algebraMap A (Localization.AtPrime m.asIdeal) a)).charpoly := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let e : A ≃ₗ[K] MaximalSpectrum.PiLocalization A :=
    (MaximalSpectrum.toPiLocalizationEquiv A).toLinearEquiv.restrictScalars K
  have he : ∀ (y : A) (m : MaximalSpectrum A), e y m = algebraMap A (Localization.AtPrime m.asIdeal) y :=
    fun y m => MaximalSpectrum.toPiLocalization_apply_apply A
  have hconj : e.conj (LinearMap.mulLeft K a) =
      LinearMap.pi fun m => (LinearMap.mulLeft K (algebraMap A (Localization.AtPrime m.asIdeal) a)).comp
        (LinearMap.proj m) := by
    apply LinearMap.ext
    intro x
    funext m
    rw [LinearEquiv.conj_apply_apply, LinearMap.mulLeft_apply, he, map_mul, ← he (e.symm x) m,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [← LinearEquiv.charpoly_conj e, hconj]
  exact charpoly_pi (K := K) (MaximalSpectrum A) (fun m => Localization.AtPrime m.asIdeal)
    (fun m => LinearMap.mulLeft K (algebraMap A (Localization.AtPrime m.asIdeal) a))

end NormDecomp
p2m_reactivate "P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length.NormDecomp"

open Polynomial IsLocalRing

namespace NormDecomp

theorem charpoly_eq_one_of_subsingleton {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Subsingleton V] (f : V →ₗ[K] V) : f.charpoly = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero f.charpoly_monic
    (by rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])

theorem charpoly_smul_eq_pow_length
    (K : Type u) (L : Type v) [Field K] [CommRing L] [IsLocalRing L] [Algebra K L]
    [Module.Finite K (ResidueField L)] (a : L)
    (M : Type w) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Module.Finite K M] :
    (DistribSMul.toLinearMap K M a).charpoly =
      (DistribSMul.toLinearMap K (ResidueField L) (residue L a)).charpoly ^ (Module.length L M).toNat := by

  suffices h : ∀ n : ℕ, ∀ (M : Type w) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
      [Module.Finite K M], Module.finrank K M = n →
      (DistribSMul.toLinearMap K M a).charpoly =
        (DistribSMul.toLinearMap K (ResidueField L) (residue L a)).charpoly ^ (Module.length L M).toNat from
    h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn
  haveI : IsArtinian L M := isArtinian_of_tower K inferInstance
  haveI : IsNoetherian L M := isNoetherian_of_tower K inferInstance
  by_cases hM : Subsingleton M
  · rw [Module.length_eq_zero_iff.mpr hM, ENat.toNat_zero, pow_zero]
    exact charpoly_eq_one_of_subsingleton _
  have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  obtain ⟨S, hS⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule L M)).resolve_left top_ne_bot
  obtain ⟨hSatom, -⟩ := hS
  haveI hSsimple : IsSimpleModule L S := isSimpleModule_iff_isAtom.mpr hSatom
  obtain ⟨I, hImax, ⟨eS⟩⟩ := isSimpleModule_iff_quot_maximal.mp hSsimple
  have hI : I = maximalIdeal L := IsLocalRing.eq_maximalIdeal hImax
  subst hI

  set T : M →ₗ[K] M := DistribSMul.toLinearMap K M a with hT
  have hTapply : ∀ m : M, T m = a • m := fun m => rfl
  set N : Submodule K M := S.restrictScalars K with hNdef
  have hN : N ≤ N.comap T := fun m hm => S.smul_mem a hm
  rw [charpoly_eq_charpoly_restrict_mul_charpoly_quotient T N hN]

  let e1 : N ≃ₗ[K] ResidueField L :=
    { toFun := fun s => eS ⟨s.1, s.2⟩
      invFun := fun q => ⟨(eS.symm q).1, (eS.symm q).2⟩
      map_add' := fun s t => map_add eS ⟨s.1, s.2⟩ ⟨t.1, t.2⟩
      map_smul' := fun k s => by
        change eS (k • ⟨s.1, s.2⟩) = k • eS ⟨s.1, s.2⟩
        rw [← algebraMap_smul L k, map_smul, algebraMap_smul]
      left_inv := fun s => by
        apply Subtype.ext
        change ((eS.symm (eS ⟨s.1, s.2⟩)) : M) = s.1
        rw [LinearEquiv.symm_apply_apply]
      right_inv := fun q => by
        change eS ⟨(eS.symm q).1, (eS.symm q).2⟩ = q
        exact eS.apply_symm_apply q }
  have he1 : ∀ s : N, e1 s = eS ⟨s.1, s.2⟩ := fun s => rfl
  have h1 : (T.restrict (p := N) (q := N) (fun x hx => hN hx)).charpoly =
      (DistribSMul.toLinearMap K (ResidueField L) (residue L a)).charpoly := by
    rw [← LinearEquiv.charpoly_conj e1]
    congr 1
    apply LinearMap.ext
    intro z
    obtain ⟨s, rfl⟩ := e1.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, he1, he1]
    have hl : (⟨(T.restrict (p := N) (q := N) (fun x hx => hN hx) s).1, (T.restrict (p := N) (q := N) (fun x hx => hN hx) s).2⟩ : S) = a • ⟨s.1, s.2⟩ := rfl
    rw [hl, map_smul]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (eS ⟨s.1, s.2⟩)
    rw [← hb]
    change a • Ideal.Quotient.mk (maximalIdeal L) b = Ideal.Quotient.mk (maximalIdeal L) a * Ideal.Quotient.mk (maximalIdeal L) b
    rw [← map_mul]
    rfl

  haveI : Module.Finite K (M ⧸ S) :=
    Module.Finite.of_surjective (S.mkQ.restrictScalars K) (Submodule.mkQ_surjective S)
  have h2 : (N.mapQ N T hN).charpoly = (DistribSMul.toLinearMap K (M ⧸ S) a).charpoly := by
    rw [← LinearEquiv.charpoly_conj (Submodule.Quotient.restrictScalarsEquiv K S)]
    congr 1
    apply LinearMap.ext
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective S z
    rw [LinearEquiv.conj_apply_apply]
    have hsymm : (Submodule.Quotient.restrictScalarsEquiv K S).symm (Submodule.Quotient.mk m) =
        Submodule.Quotient.mk m := rfl
    rw [hsymm, Submodule.mapQ_apply, hTapply]
    rfl

  have hdim : Module.finrank K M = Module.finrank K N + Module.finrank K (M ⧸ S) := by
    rw [← (Submodule.Quotient.restrictScalarsEquiv K S).finrank_eq, add_comm]
    exact (Submodule.finrank_quotient_add_finrank N).symm
  have hκpos : 0 < Module.finrank K N := by
    rw [e1.finrank_eq]
    haveI : Nontrivial (ResidueField L) := inferInstance
    exact Module.finrank_pos
  have hlt : Module.finrank K (M ⧸ S) < n := by omega
  have ihq := ih _ hlt (M ⧸ S) rfl

  have hlen : Module.length L M = 1 + Module.length L (M ⧸ S) := by
    rw [Module.length_eq_add_of_exact S.subtype S.mkQ (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
      (LinearMap.exact_subtype_mkQ S), Module.length_eq_one_iff.mpr hSsimple]
  haveI : IsArtinian L (M ⧸ S) := isArtinian_of_tower K inferInstance
  haveI : IsNoetherian L (M ⧸ S) := isNoetherian_of_tower K inferInstance
  have hfinq : Module.length L (M ⧸ S) ≠ ⊤ := Module.length_ne_top
  obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp hfinq
  rw [h1, h2, ihq, hlen, ← hℓ, show (1 : ℕ∞) + (ℓ : ℕ∞) = ((1 + ℓ : ℕ) : ℕ∞) by push_cast; rfl,
    ENat.toNat_coe, ENat.toNat_coe, pow_add, pow_one]

end NormDecomp
p2m_reactivate "P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length.NormDecomp"

namespace NormDecomp
open IsLocalRing Polynomial

section ResidueAlgEquiv

noncomputable def quotMaxAlgEquivResidueField
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    (A ⧸ 𝔪) ≃ₐ[K] ResidueField (Localization.AtPrime 𝔪) := by
  let ρ : A →+* ResidueField (Localization.AtPrime 𝔪) :=
    (residue (Localization.AtPrime 𝔪)).comp (algebraMap A (Localization.AtPrime 𝔪))
  have hρ : ∀ a ∈ 𝔪, ρ a = 0 := by
    intro a ha
    change residue _ (algebraMap A (Localization.AtPrime 𝔪) a) = 0
    rw [residue_eq_zero_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a).mpr ha
  let ψ₀ : (A ⧸ 𝔪) →+* ResidueField (Localization.AtPrime 𝔪) := Ideal.Quotient.lift 𝔪 ρ hρ
  have hψmk : ∀ a : A, ψ₀ (Ideal.Quotient.mk _ a) = residue _ (algebraMap A (Localization.AtPrime 𝔪) a) :=
    fun a => rfl
  have hKL : ∀ k : K, algebraMap K (ResidueField (Localization.AtPrime 𝔪)) k =
      residue _ (algebraMap A (Localization.AtPrime 𝔪) (algebraMap K A k)) := by
    intro k
    rw [← IsScalarTower.algebraMap_apply K A (Localization.AtPrime 𝔪) k,
      IsScalarTower.algebraMap_apply K (Localization.AtPrime 𝔪) (ResidueField (Localization.AtPrime 𝔪)) k,
      ResidueField.algebraMap_eq]
  let ψ : (A ⧸ 𝔪) →ₐ[K] ResidueField (Localization.AtPrime 𝔪) := AlgHom.mk' ψ₀ (by
    intro k x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Algebra.smul_def, hKL, ← hψmk, ← map_mul, IsScalarTower.algebraMap_apply K A (A ⧸ 𝔪) k,
      Ideal.Quotient.algebraMap_eq, ← map_mul])
  refine AlgEquiv.ofBijective ψ ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change ψ₀ _ = 0 at hz
    rw [hψmk, residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro z
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl l
    have hs0 : (Ideal.Quotient.mk 𝔪 (s : A)) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact s.2
    obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ t', ?_⟩
    have hsunit : residue _ (algebraMap A (Localization.AtPrime 𝔪) s) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪]
      exact s.2
    apply mul_right_cancel₀ hsunit
    dsimp only
    change ψ₀ _ * _ = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔪) a s) *
      residue _ (algebraMap A (Localization.AtPrime 𝔪) s)
    have hts : Ideal.Quotient.mk 𝔪 t' * Ideal.Quotient.mk 𝔪 (s : A) = 1 := by
      rw [mul_comm]; exact ht
    rw [← map_mul (residue _), IsLocalization.mk'_spec, ← hψmk a, ← hψmk (s : A), ← map_mul ψ₀, mul_assoc,
      hts, mul_one]

theorem quotMaxAlgEquivResidueField_mk
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] (𝔪 : Ideal A) [𝔪.IsMaximal] (a : A) :
    quotMaxAlgEquivResidueField K A 𝔪 (Ideal.Quotient.mk 𝔪 a) =
      residue _ (algebraMap A (Localization.AtPrime 𝔪) a) := rfl

end ResidueAlgEquiv
p2m_reactivate "P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length.NormDecomp"
section ConjLemmas

theorem charpoly_mulLeft_algEquiv {K : Type u} [CommRing K] {B : Type v} {C : Type w} [Ring B] [Ring C]
    [Algebra K B] [Algebra K C] [Module.Free K B] [Module.Finite K B] [Module.Free K C] [Module.Finite K C]
    (Φ : B ≃ₐ[K] C) (b : B) :
    (LinearMap.mulLeft K b).charpoly = (LinearMap.mulLeft K (Φ b)).charpoly := by
  rw [← LinearEquiv.charpoly_conj Φ.toLinearEquiv (LinearMap.mulLeft K b)]
  congr 1
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, AlgEquiv.toLinearEquiv_apply,
    map_mul]
  congr 1
  exact Φ.toLinearEquiv.apply_symm_apply z

theorem mulLeft_eq_toLinearMap {K : Type u} [CommRing K] {L : Type v} [CommRing L] [Algebra K L] (a : L) :
    (LinearMap.mulLeft K a : L →ₗ[K] L) = DistribSMul.toLinearMap K L a := by
  apply LinearMap.ext; intro z; rfl

theorem moduleFinite_residueField (K : Type u) [Field K] (L : Type v) [CommRing L] [IsLocalRing L] [Algebra K L]
    [Module.Finite K L] : Module.Finite K (ResidueField L) :=
  Module.Finite.of_surjective (IsScalarTower.toAlgHom K L (ResidueField L)).toLinearMap Ideal.Quotient.mk_surjective

end ConjLemmas
p2m_reactivate "P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length.NormDecomp"
end NormDecomp
p2m_reactivate "P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length.NormDecomp"

open IsLocalRing Polynomial in
theorem solution
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] [Module.Finite K A] (a : A) :
    Algebra.norm K a =
      ∏ᶠ 𝔪 : MaximalSpectrum A,
        Algebra.norm K (Ideal.Quotient.mk 𝔪.asIdeal a) ^
          (Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal)).toNat := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]

  have hnorm : ∀ (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B] (b : B),
      Algebra.norm K b = (-1) ^ Module.finrank K B * (LinearMap.mulLeft K b).charpoly.coeff 0 := by
    intro B _ _ _ b
    have hl : (Algebra.lmul K B b : B →ₗ[K] B) = LinearMap.mulLeft K b := LinearMap.ext fun _ => rfl
    rw [Algebra.norm_apply, hl, LinearMap.det_eq_sign_charpoly_coeff]

  have hfinQ : ∀ m : MaximalSpectrum A, Module.Finite K (A ⧸ m.asIdeal) := fun m =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal).toLinearMap Ideal.Quotient.mk_surjective

  have hloc : ∀ m : MaximalSpectrum A,
      (LinearMap.mulLeft K (algebraMap A (Localization.AtPrime m.asIdeal) a)).charpoly =
        (LinearMap.mulLeft K (Ideal.Quotient.mk m.asIdeal a)).charpoly ^
          (Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal)).toNat := by
    intro m
    haveI : m.asIdeal.IsMaximal := m.isMaximal
    haveI := hfinQ m
    haveI : Module.Finite K (ResidueField (Localization.AtPrime m.asIdeal)) :=
      NormDecomp.moduleFinite_residueField K _
    rw [NormDecomp.mulLeft_eq_toLinearMap,
      NormDecomp.charpoly_smul_eq_pow_length K (Localization.AtPrime m.asIdeal) _ (Localization.AtPrime m.asIdeal),
      ← NormDecomp.mulLeft_eq_toLinearMap,
      NormDecomp.charpoly_mulLeft_algEquiv (NormDecomp.quotMaxAlgEquivResidueField K A m.asIdeal)
        (Ideal.Quotient.mk m.asIdeal a), NormDecomp.quotMaxAlgEquivResidueField_mk]

  have hlen : ∀ m : MaximalSpectrum A,
      Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) ≠ ⊤ := by
    intro m
    haveI : IsArtinianRing (Localization.AtPrime m.asIdeal) := IsArtinianRing.of_finite K _
    haveI : IsNoetherianRing (Localization.AtPrime m.asIdeal) := isNoetherian_of_tower K inferInstance
    exact Module.length_ne_top
  have hfr : Module.finrank K A = ∑ m : MaximalSpectrum A, Module.finrank K (A ⧸ m.asIdeal) *
      (Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal)).toNat := by
    rw [NormDecomp.finrank_eq_sum_finrank_localization_atPrime K A]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    haveI : m.asIdeal.IsMaximal := m.isMaximal
    haveI := hfinQ m
    have h1 := NormDecomp.finrank_eq_finrank_residueField_mul_length K (Localization.AtPrime m.asIdeal)
      (Localization.AtPrime m.asIdeal)
    have h2 : Module.finrank K (A ⧸ m.asIdeal) = Module.finrank K (ResidueField (Localization.AtPrime m.asIdeal)) :=
      (NormDecomp.quotMaxAlgEquivResidueField K A m.asIdeal).toLinearEquiv.finrank_eq
    rw [← ENat.coe_toNat (hlen m), ← h2] at h1
    exact_mod_cast h1

  have hcz : ∀ (p : Polynomial K) (n : ℕ), (p ^ n).coeff 0 = p.coeff 0 ^ n := fun p n => by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.coeff_zero_eq_eval_zero]
  have hq : ∀ m : MaximalSpectrum A, haveI := hfinQ m
      Algebra.norm K (Ideal.Quotient.mk m.asIdeal a) =
        (-1) ^ Module.finrank K (A ⧸ m.asIdeal) * (LinearMap.mulLeft K (Ideal.Quotient.mk m.asIdeal a)).charpoly.coeff 0 :=
    fun m => by haveI := hfinQ m; exact hnorm _ _
  simp_rw [hq]
  rw [hnorm A a, NormDecomp.charpoly_mulLeft_eq_prod_localization K A a, Finset.prod_congr rfl (fun m _ => hloc m),
    Polynomial.coeff_zero_prod, hfr]
  simp_rw [hcz, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]

end S_Algebra_norm_eq_finprod_norm_quotient_pow_length
end P2MW
export P2MW.S_Algebra_norm_eq_finprod_norm_quotient_pow_length (solution)
