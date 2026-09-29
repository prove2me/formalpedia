-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a438582d-aef7-5bac-99ee-f759d8ce91ba

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ValuationSubring_exists_regularProlongation_ratFunc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed

set_option autoImplicit false
universe u v

namespace PlaneRelationReduction

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private noncomputable def toL (A : ValuationSubring L) (Q : Polynomial (Polynomial A)) : Polynomial (Polynomial L) :=
  Q.map (Polynomial.mapRingHom A.subtype)

private noncomputable def toRes (A : ValuationSubring L) (Q : Polynomial (Polynomial A)) :
    Polynomial (RatFunc (IsLocalRing.ResidueField A)) :=
  (Q.map (Polynomial.mapRingHom (IsLocalRing.residue A))).map
    (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))

private noncomputable def evalFY (f y : F) (P : Polynomial (Polynomial L)) : F :=
  P.eval₂ (Polynomial.aeval f : Polynomial L →ₐ[L] F).toRingHom y

end PlaneRelationReduction

section

open Polynomial IntermediateField

namespace PlaneRelationReduction

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem aeval_eq_comp (f : F) (hf : Transcendental L f) (g : Polynomial L) :
    aeval f g =
      algebraMap L⟮f⟯ F (RatFunc.algEquivOfTranscendental f hf (algebraMap (Polynomial L) (RatFunc L) g)) := by
  rw [RatFunc.algEquivOfTranscendental_algebraMap, ← Polynomial.aeval_algebraMap_apply,
    IntermediateField.AdjoinSimple.algebraMap_gen]

private theorem exists_bivariate_relation (f : F) (hf : Transcendental L f)
    [FiniteDimensional L⟮f⟯ F] (y : F) (hy : (L⟮f⟯)⟮y⟯ = ⊤) :
    ∃ P : Polynomial (Polynomial L),
      evalFY f y P = 0 ∧
      P.natDegree = Module.finrank L⟮f⟯ F ∧
      P.IsPrimitive ∧
      ∀ G H : Polynomial (Polynomial L), G * H = P → 1 ≤ G.natDegree → 1 ≤ H.natDegree → False := by
  classical
  have hyint : IsIntegral L⟮f⟯ y := IsIntegral.of_finite L⟮f⟯ y
  have hn : (minpoly L⟮f⟯ y).natDegree = Module.finrank L⟮f⟯ F := by
    rw [← IntermediateField.adjoin.finrank hyint, hy, IntermediateField.finrank_top']

  let e : RatFunc L ≃ₐ[L] L⟮f⟯ := RatFunc.algEquivOfTranscendental f hf
  let e' : L⟮f⟯ →+* RatFunc L := (e.symm.toRingEquiv : L⟮f⟯ →+* RatFunc L)
  let m' : Polynomial (RatFunc L) := Polynomial.mapEquiv e.symm.toRingEquiv (minpoly L⟮f⟯ y)
  have hm'map : m' = (minpoly L⟮f⟯ y).map e' := rfl
  have hm'irr : Irreducible m' :=
    (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e.symm.toRingEquiv)).mpr (minpoly.irreducible hyint)
  have hm'deg : m'.natDegree = Module.finrank L⟮f⟯ F := by
    rw [hm'map, natDegree_map_eq_of_injective e'.injective, hn]

  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial L)) m'
  set N : Polynomial (Polynomial L) := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial L)) m'
    with hNdef
  set b' : RatFunc L := algebraMap (Polynomial L) (RatFunc L) b with hb'def
  have hb0 : b' ≠ 0 := by
    rw [hb'def]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) (RatFunc L))).mpr
      (nonZeroDivisors.ne_zero hbM)
  have hsmul : b • m' = C b' * m' := by
    ext i
    simp [Polynomial.coeff_C_mul, Algebra.smul_def, hb'def]
  have hNmap : N.map (algebraMap (Polynomial L) (RatFunc L)) = C b' * m' := by rw [hb, hsmul]
  have hNdeg : N.natDegree = Module.finrank L⟮f⟯ F := by
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) (RatFunc L)) N, hNmap,
      natDegree_C_mul hb0, hm'deg]
  have hN0 : N ≠ 0 := by
    intro h
    have h' := hNdeg
    rw [h, natDegree_zero] at h'
    exact (Module.finrank_pos (R := L⟮f⟯) (M := F)).ne h'

  set ψ : Polynomial L →+* F := (aeval f : Polynomial L →ₐ[L] F).toRingHom with hψdef
  have hψ : ψ = ((algebraMap L⟮f⟯ F).comp (e : RatFunc L →+* L⟮f⟯)).comp (algebraMap (Polynomial L) (RatFunc L)) :=
    RingHom.ext fun g => aeval_eq_comp f hf g
  have hψinj : Function.Injective ψ := by
    intro g₁ g₂ h
    have h' : aeval f (g₁ - g₂) = 0 := by
      rw [map_sub]
      change ψ g₁ - ψ g₂ = 0
      rw [h, sub_self]
    exact sub_eq_zero.mp (transcendental_iff.mp hf _ h')
  have hevalN : evalFY f y N = 0 := by
    change N.eval₂ ψ y = 0
    rw [hψ, ← Polynomial.eval₂_map, hNmap, eval₂_mul, eval₂_C, ← Polynomial.eval₂_map, hm'map,
      Polynomial.map_map]
    have hcomp : ((e : RatFunc L →+* L⟮f⟯).comp e') = RingHom.id L⟮f⟯ :=
      RingHom.ext fun x => by simp [e']
    rw [hcomp, Polynomial.map_id, ← Polynomial.aeval_def, minpoly.aeval, mul_zero]
  refine ⟨N.primPart, ?_, ?_, isPrimitive_primPart N, ?_⟩
  ·
    have hc : ψ N.content ≠ 0 := by
      intro h
      have h0 : N.content = 0 := hψinj (by rw [h, map_zero])
      exact hN0 (content_eq_zero_iff.mp h0)
    have h := hevalN
    change N.eval₂ ψ y = 0 at h
    rw [eq_C_content_mul_primPart N, eval₂_mul, eval₂_C] at h
    change N.primPart.eval₂ ψ y = 0
    exact (mul_eq_zero.mp h).resolve_left hc
  · rw [natDegree_primPart, hNdeg]
  · intro G H hGH hG hH

    set Φ : Polynomial (Polynomial L) →+* Polynomial (RatFunc L) :=
      Polynomial.mapRingHom (algebraMap (Polynomial L) (RatFunc L)) with hΦdef
    have hΦN : Φ N = C b' * m' := hNmap
    have hcont : algebraMap (Polynomial L) (RatFunc L) N.content ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) (RatFunc L))).mpr
        (by rw [Ne, content_eq_zero_iff]; exact hN0)
    have hsplit : Φ N = C (algebraMap (Polynomial L) (RatFunc L) N.content) * (Φ G * Φ H) := by
      rw [← map_mul, hGH]
      conv_lhs => rw [eq_C_content_mul_primPart N]
      rw [map_mul, hΦdef, coe_mapRingHom, Polynomial.map_C]
    set u : RatFunc L := b'⁻¹ * algebraMap (Polynomial L) (RatFunc L) N.content with hudef
    have hu0 : u ≠ 0 := mul_ne_zero (inv_ne_zero hb0) hcont
    have hfac : m' = (C u * Φ G) * Φ H := by
      have h1 : C b'⁻¹ * (C b' * m') = m' := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]
      rw [← h1, ← hΦN, hsplit, hudef, C_mul]
      ring
    rcases hm'irr.isUnit_or_isUnit hfac with hunit | hunit
    · have hdeg : (C u * Φ G).natDegree = G.natDegree := by
        rw [natDegree_C_mul hu0, hΦdef, coe_mapRingHom,
          natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) (RatFunc L))]
      have h0 := natDegree_eq_zero_of_isUnit hunit
      omega
    · have hdeg : (Φ H).natDegree = H.natDegree := by
        rw [hΦdef, coe_mapRingHom,
          natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) (RatFunc L))]
      have h0 := natDegree_eq_zero_of_isUnit hunit
      omega

end PlaneRelationReduction

end

section

open Polynomial

namespace PlaneRelationReduction

section Table

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]

private noncomputable def ofTable (d e : ℕ) (w : Fin (d + 1) → Fin (e + 1) → R) : Polynomial (Polynomial R) :=
  ∑ c : Fin (e + 1), C (∑ a : Fin (d + 1), C (w a c) * X ^ (a : ℕ)) * X ^ (c : ℕ)

private theorem ofTable_map (φ : R →+* S) (d e : ℕ) (w : Fin (d + 1) → Fin (e + 1) → R) :
    (ofTable d e w).map (mapRingHom φ) = ofTable d e fun a c => φ (w a c) := by
  simp [ofTable, Polynomial.map_sum]

private theorem natDegree_ofTable_le (d e : ℕ) (w : Fin (d + 1) → Fin (e + 1) → R) :
    (ofTable d e w).natDegree ≤ e := by
  unfold ofTable
  refine natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans ?_)
  exact Nat.lt_succ_iff.mp c.2

private theorem coeff_ofTable (d e : ℕ) (w : Fin (d + 1) → Fin (e + 1) → R) (a : Fin (d + 1)) (c : Fin (e + 1)) :
    ((ofTable d e w).coeff c).coeff a = w a c := by
  unfold ofTable
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem ofTable_coeff_eq_self (d e : ℕ) (p : Polynomial (Polynomial R)) (hp : p.natDegree ≤ e)
    (hpd : ∀ c, (p.coeff c).natDegree ≤ d) :
    ofTable d e (fun a c => (p.coeff c).coeff a) = p := by
  unfold ofTable
  conv_rhs => rw [p.as_sum_range' (e + 1) (Nat.lt_succ_of_le hp), Finset.sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [C_mul_X_pow_eq_monomial]
  congr 1
  conv_rhs => rw [(p.coeff c).as_sum_range' (d + 1) (Nat.lt_succ_of_le (hpd c)), Finset.sum_range]
  exact Finset.sum_congr rfl fun a _ => C_mul_X_pow_eq_monomial

end Table

section System

variable (R : Type*) [CommRing R]

private abbrev SysVar (d b b' : ℕ) : Type := (Fin (d + 1) × Fin (b + 1)) ⊕ (Fin (d + 1) × Fin (b' + 1))

private noncomputable def genG (d b b' : ℕ) : Polynomial (Polynomial (MvPolynomial (SysVar d b b') R)) :=
  ofTable d b fun a c => MvPolynomial.X (Sum.inl (a, c))

private noncomputable def genH (d b b' : ℕ) : Polynomial (Polynomial (MvPolynomial (SysVar d b b') R)) :=
  ofTable d b' fun a c => MvPolynomial.X (Sum.inr (a, c))

variable {R}

private noncomputable def eqn (T : Polynomial (Polynomial R)) (d b b' : ℕ) (k : ℕ × ℕ) :
    MvPolynomial (SysVar d b b') R :=
  (((genG R d b b' * genH R d b b' - T.map (mapRingHom MvPolynomial.C)).coeff k.2).coeff k.1)

variable {V : Type*} [CommRing V]

private theorem map_eqn (T : Polynomial (Polynomial R)) (d b b' : ℕ) (χ : MvPolynomial (SysVar d b b') R →+* V)
    (k : ℕ × ℕ) :
    χ (eqn T d b b' k) =
      (((ofTable d b (fun a c => χ (MvPolynomial.X (Sum.inl (a, c)))) *
          ofTable d b' (fun a c => χ (MvPolynomial.X (Sum.inr (a, c)))) -
            T.map (mapRingHom (χ.comp MvPolynomial.C))).coeff k.2).coeff k.1) := by
  unfold eqn
  rw [← ofTable_map, ← ofTable_map, ← mapRingHom_comp, ← Polynomial.map_map]
  change _ = ((((genG R d b b').map (mapRingHom χ) * (genH R d b b').map (mapRingHom χ) -
    (T.map (mapRingHom MvPolynomial.C)).map (mapRingHom χ)).coeff k.2).coeff k.1)
  rw [← Polynomial.map_mul, ← Polynomial.map_sub, coeff_map, coe_mapRingHom, coeff_map]

private theorem eval_eqn (T : Polynomial (Polynomial R)) (d b b' : ℕ) (z : SysVar d b b' → R) (k : ℕ × ℕ) :
    MvPolynomial.eval z (eqn T d b b' k) =
      (((ofTable d b (fun a c => z (Sum.inl (a, c))) *
          ofTable d b' (fun a c => z (Sum.inr (a, c))) - T).coeff k.2).coeff
        k.1) := by
  rw [map_eqn]
  have h : (MvPolynomial.eval z).comp MvPolynomial.C = RingHom.id R := RingHom.ext fun r => MvPolynomial.eval_C r
  simp only [MvPolynomial.eval_X, h, mapRingHom_id, Polynomial.map_id]

private theorem forall_eval_eqn_eq_zero_iff (T : Polynomial (Polynomial R)) (d b b' : ℕ) (z : SysVar d b b' → R) :
    (∀ k, MvPolynomial.eval z (eqn T d b b' k) = 0) ↔
      ofTable d b (fun a c => z (Sum.inl (a, c))) * ofTable d b' (fun a c => z (Sum.inr (a, c))) = T := by
  simp only [eval_eqn]
  constructor
  · intro h
    rw [← sub_eq_zero]
    ext c a
    simpa using h (a, c)
  · intro h k
    rw [h, sub_self, coeff_zero, coeff_zero]

private theorem map_eqn_eq_eqn_map {S : Type*} [CommRing S] (φ : R →+* S) (T : Polynomial (Polynomial R)) (d b b' : ℕ)
    (k : ℕ × ℕ) :
    MvPolynomial.map φ (eqn T d b b' k) = eqn (T.map (mapRingHom φ)) d b b' k := by
  have hC : (MvPolynomial.map φ).comp (MvPolynomial.C : R →+* MvPolynomial (SysVar d b b') R) =
      (MvPolynomial.C : S →+* MvPolynomial (SysVar d b b') S).comp φ :=
    RingHom.ext fun r => MvPolynomial.map_C φ r
  rw [map_eqn]
  unfold eqn genG genH
  simp only [MvPolynomial.map_X]
  rw [hC, Polynomial.map_map, mapRingHom_comp]

end System

end PlaneRelationReduction
end

section

open Polynomial

namespace PlaneRelationReduction

section Lift

variable {L : Type*} [Field L] (A : ValuationSubring L) {σ : Type*}

private noncomputable def constants (c : MvPolynomial σ L) : Finset L := by
  classical exact c.support.image fun m => MvPolynomial.coeff m c

private theorem coeff_mem_constants (c : MvPolynomial σ L) (m : σ →₀ ℕ) (hm : MvPolynomial.coeff m c ≠ 0) :
    MvPolynomial.coeff m c ∈ constants c := by
  classical
  unfold constants
  exact Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩

private theorem exists_map_subtype_eq (c : MvPolynomial σ L) (hc : ∀ s ∈ constants c, s ∈ A) :
    ∃ c' : MvPolynomial σ A, MvPolynomial.map A.subtype c' = c := by
  classical
  have hmem : ∀ m : σ →₀ ℕ, MvPolynomial.coeff m c ∈ A := by
    intro m
    by_cases hm : MvPolynomial.coeff m c = 0
    · rw [hm]; exact A.zero_mem
    · exact hc _ (coeff_mem_constants c m hm)
  refine ⟨∑ m ∈ c.support, MvPolynomial.monomial m (⟨MvPolynomial.coeff m c, hmem m⟩ : A), ?_⟩
  rw [map_sum]
  simp only [MvPolynomial.map_monomial]
  conv_rhs => rw [c.as_sum]
  rfl

end Lift

section Certificate

variable {L : Type*} [Field L] [IsAlgClosed L]

private noncomputable abbrev redPoly (A : ValuationSubring L) (Q : Polynomial (Polynomial A)) :
    Polynomial (Polynomial (IsLocalRing.ResidueField A)) :=
  Q.map (mapRingHom (IsLocalRing.residue A))

private theorem exists_finset_forall_ofTable_mul_ofTable_ne (P : Polynomial (Polynomial L)) (n : ℕ)
    (hPn : P.natDegree = n)
    (hP : ∀ G H : Polynomial (Polynomial L), G * H = P → 1 ≤ G.natDegree → 1 ≤ H.natDegree → False)
    (d β β' : ℕ) (hβ : 1 ≤ β) (hβ' : 1 ≤ β') (hsum : β + β' = n) :
    ∃ S : Finset L, ∀ A : ValuationSubring L, (∀ s ∈ S, s ∈ A) →
      ∀ Q : Polynomial (Polynomial A), Q.map (mapRingHom A.subtype) = P →
        ∀ w : SysVar d β β' → IsLocalRing.ResidueField A,
          ofTable d β (fun a c => w (Sum.inl (a, c))) * ofTable d β' (fun a c => w (Sum.inr (a, c))) ≠
            redPoly A Q := by
  classical
  set I : Ideal (MvPolynomial (SysVar d β β') L) := Ideal.span (Set.range (eqn P d β β')) with hI

  have hzero : MvPolynomial.zeroLocus L I = ∅ := by
    rw [hI, MvPolynomial.zeroLocus_span, Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hz' : ∀ k, MvPolynomial.eval z (eqn P d β β' k) = 0 := by
      intro k
      have := hz (eqn P d β β' k) ⟨k, rfl⟩
      simpa using this
    rw [forall_eval_eqn_eq_zero_iff] at hz'
    have h1 := natDegree_ofTable_le d β fun a c => z (Sum.inl (a, c))
    have h2 := natDegree_ofTable_le d β' fun a c => z (Sum.inr (a, c))
    have h3 := natDegree_mul_le (p := ofTable d β fun a c => z (Sum.inl (a, c)))
      (q := ofTable d β' fun a c => z (Sum.inr (a, c)))
    rw [hz', hPn] at h3
    exact hP _ _ hz' (by omega) (by omega)
  have hItop : I = ⊤ := by
    have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := L) I
    rw [hzero, MvPolynomial.vanishingIdeal_empty] at h
    exact Ideal.radical_eq_top.mp h.symm

  have h1 : (1 : MvPolynomial (SysVar d β β') L) ∈ I := by rw [hItop]; exact Submodule.mem_top
  rw [hI, Ideal.span, Submodule.mem_span_iff_exists_finset_subset] at h1
  obtain ⟨cf, t, hts, -, hcomb⟩ := h1
  refine ⟨t.biUnion fun g => constants (cf g), ?_⟩
  intro A hA Q hQ w hw

  have hlift : ∀ g ∈ t, ∃ c' : MvPolynomial (SysVar d β β') A, MvPolynomial.map A.subtype c' = cf g := by
    intro g hg
    exact exists_map_subtype_eq A (cf g) fun s hs => hA s (Finset.mem_biUnion.mpr ⟨g, hg, hs⟩)
  choose! cf' hcf' using hlift

  have hgen : ∀ g ∈ t, ∃ k : ℕ × ℕ, MvPolynomial.map A.subtype (eqn Q d β β' k) = g := by
    intro g hg
    obtain ⟨k, hk⟩ := Set.mem_range.mp (hts hg)
    exact ⟨k, by rw [map_eqn_eq_eqn_map, hQ, hk]⟩
  choose! kk hkk using hgen

  have hA1 : (∑ g ∈ t, cf' g * eqn Q d β β' (kk g)) = 1 := by
    apply MvPolynomial.map_injective A.subtype A.subtype_injective
    rw [map_sum, map_one, ← hcomb]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [map_mul, hcf' g hg, hkk g hg, smul_eq_mul]

  have hvan : ∀ g ∈ t,
      MvPolynomial.eval w (MvPolynomial.map (IsLocalRing.residue A) (eqn Q d β β' (kk g))) = 0 := by
    intro g _
    rw [map_eqn_eq_eqn_map, eval_eqn]
    change (((_ - redPoly A Q).coeff _).coeff _) = 0
    rw [hw, sub_self, coeff_zero, coeff_zero]
  have hκ : (1 : IsLocalRing.ResidueField A) = 0 := by
    calc (1 : IsLocalRing.ResidueField A)
        = MvPolynomial.eval w (MvPolynomial.map (IsLocalRing.residue A) (∑ g ∈ t, cf' g * eqn Q d β β' (kk g))) := by
          rw [hA1, map_one, map_one]
      _ = ∑ g ∈ t, MvPolynomial.eval w (MvPolynomial.map (IsLocalRing.residue A) (cf' g)) *
            MvPolynomial.eval w (MvPolynomial.map (IsLocalRing.residue A) (eqn Q d β β' (kk g))) := by
          simp only [map_sum, map_mul]
      _ = 0 := Finset.sum_eq_zero fun g hg => by rw [hvan g hg, mul_zero]
  exact one_ne_zero hκ

private theorem exists_finset_forall_splitting (P : Polynomial (Polynomial L)) (n : ℕ) (hPn : P.natDegree = n)
    (hP : ∀ G H : Polynomial (Polynomial L), G * H = P → 1 ≤ G.natDegree → 1 ≤ H.natDegree → False) (d : ℕ) :
    ∃ S : Finset L, ∀ A : ValuationSubring L, (∀ s ∈ S, s ∈ A) →
      ∀ Q : Polynomial (Polynomial A), Q.map (mapRingHom A.subtype) = P →
        ∀ β β' : ℕ, 1 ≤ β → 1 ≤ β' → β + β' = n →
          ∀ w : SysVar d β β' → IsLocalRing.ResidueField A,
            ofTable d β (fun a c => w (Sum.inl (a, c))) * ofTable d β' (fun a c => w (Sum.inr (a, c))) ≠
              redPoly A Q := by
  classical
  have hβ : ∀ β ∈ Finset.range (n + 1), ∃ S : Finset L, 1 ≤ β → 1 ≤ n - β →
      ∀ A : ValuationSubring L, (∀ s ∈ S, s ∈ A) →
        ∀ Q : Polynomial (Polynomial A), Q.map (mapRingHom A.subtype) = P →
          ∀ w : SysVar d β (n - β) → IsLocalRing.ResidueField A,
            ofTable d β (fun a c => w (Sum.inl (a, c))) * ofTable d (n - β) (fun a c => w (Sum.inr (a, c))) ≠
              redPoly A Q := by
    intro β hβmem
    by_cases h : 1 ≤ β ∧ 1 ≤ n - β
    · obtain ⟨S, hS⟩ := exists_finset_forall_ofTable_mul_ofTable_ne P n hPn hP d β (n - β) h.1 h.2
        (by have := Finset.mem_range.mp hβmem; omega)
      exact ⟨S, fun _ _ => hS⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose! Sβ hSβ using hβ
  refine ⟨(Finset.range (n + 1)).biUnion Sβ, ?_⟩
  intro A hA Q hQ β β' hβ1 hβ'1 hsum w
  have hβmem : β ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hβ' : β' = n - β := by omega
  subst hβ'
  exact hSβ β hβmem hβ1 hβ'1 A (fun s hs => hA s (Finset.mem_biUnion.mpr ⟨β, hβmem, hs⟩)) Q hQ w

end Certificate

end PlaneRelationReduction
end

section

open Polynomial

namespace PlaneRelationReduction

variable {L : Type*} [Field L]

section LiftPoly

variable (A : ValuationSubring L)

private noncomputable def polyConstants (p : Polynomial L) : Finset L := by
  classical exact p.support.image fun i => p.coeff i

private theorem coeff_mem_polyConstants (p : Polynomial L) (i : ℕ) (hi : p.coeff i ≠ 0) :
    p.coeff i ∈ polyConstants p := by
  classical
  unfold polyConstants
  exact Finset.mem_image.mpr ⟨i, mem_support_iff.mpr hi, rfl⟩

private theorem exists_polynomial_map_eq (p : Polynomial L) (hp : ∀ s ∈ polyConstants p, s ∈ A) :
    ∃ p' : Polynomial A, p'.map A.subtype = p := by
  have hmem : p ∈ (mapRingHom A.subtype).rangeS := by
    rw [mem_map_rangeS]
    intro i
    by_cases hi : p.coeff i = 0
    · rw [hi]; exact ⟨0, by simp⟩
    · exact ⟨⟨p.coeff i, hp _ (coeff_mem_polyConstants p i hi)⟩, rfl⟩
  obtain ⟨p', hp'⟩ := hmem
  exact ⟨p', hp'⟩

private noncomputable def biConstants (P : Polynomial (Polynomial L)) : Finset L := by
  classical exact (Finset.range (P.natDegree + 1)).biUnion fun c => polyConstants (P.coeff c)

private theorem exists_bivariate_map_eq (P : Polynomial (Polynomial L)) (hP : ∀ s ∈ biConstants P, s ∈ A) :
    ∃ Q : Polynomial (Polynomial A), Q.map (mapRingHom A.subtype) = P := by
  classical
  have hmem : P ∈ (mapRingHom (mapRingHom A.subtype)).rangeS := by
    rw [mem_map_rangeS]
    intro c
    by_cases hc : P.natDegree < c
    · rw [coeff_eq_zero_of_natDegree_lt hc]; exact ⟨0, by simp⟩
    · obtain ⟨p', hp'⟩ := exists_polynomial_map_eq A (P.coeff c) fun s hs => hP s
        (Finset.mem_biUnion.mpr ⟨c, Finset.mem_range.mpr (by omega), hs⟩)
      exact ⟨p', by simpa using hp'⟩
  obtain ⟨Q, hQ⟩ := hmem
  exact ⟨Q, hQ⟩

private theorem ne_zero_of_mem_polyConstants (p : Polynomial L) (s : L) (hs : s ∈ polyConstants p) : s ≠ 0 := by
  classical
  unfold polyConstants at hs
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
  exact mem_support_iff.mp hi

private theorem ne_zero_of_mem_biConstants (P : Polynomial (Polynomial L)) (s : L) (hs : s ∈ biConstants P) :
    s ≠ 0 := by
  classical
  unfold biConstants at hs
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hs
  exact ne_zero_of_mem_polyConstants (P.coeff c) s hc

private theorem ne_zero_of_mem_constants {σ : Type*} (c : MvPolynomial σ L) (s : L) (hs : s ∈ constants c) :
    s ≠ 0 := by
  classical
  unfold constants at hs
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hs
  exact MvPolynomial.mem_support_iff.mp hm

end LiftPoly

section Primitivity

private theorem exists_finset_forall_isPrimitive_redPoly (P : Polynomial (Polynomial L)) (hprim : P.IsPrimitive) :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧ ∀ A : ValuationSubring L, (∀ s ∈ S, s ∈ A) →
      ∀ Q : Polynomial (Polynomial A), Q.map (mapRingHom A.subtype) = P → (redPoly A Q).IsPrimitive := by
  classical

  set J : Ideal (Polynomial L) := Ideal.span (Set.range fun c : ℕ => P.coeff c) with hJ
  have hJtop : J = ⊤ := by
    have hg : Ideal.span {Submodule.IsPrincipal.generator J} = J := Ideal.span_singleton_generator J
    have hgdvd : ∀ c, Submodule.IsPrincipal.generator J ∣ P.coeff c := by
      intro c
      have hc : P.coeff c ∈ J := Ideal.subset_span ⟨c, rfl⟩
      rw [← hg] at hc
      exact Ideal.mem_span_singleton.mp hc
    have hunit : IsUnit (Submodule.IsPrincipal.generator J) :=
      hprim _ ((C_dvd_iff_dvd_coeff _ P).mpr hgdvd)
    rw [← hg]
    exact Ideal.span_singleton_eq_top.mpr hunit
  have h1 : (1 : Polynomial L) ∈ J := by rw [hJtop]; exact Submodule.mem_top
  rw [hJ, Ideal.span, Submodule.mem_span_iff_exists_finset_subset] at h1
  obtain ⟨cf, t, hts, -, hcomb⟩ := h1
  refine ⟨t.biUnion fun g => polyConstants (cf g), fun s hs => ?_, ?_⟩
  · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hs
    exact ne_zero_of_mem_polyConstants _ s hg
  intro A hA Q hQ

  have hlift : ∀ g ∈ t, ∃ c' : Polynomial A, c'.map A.subtype = cf g := fun g hg =>
    exists_polynomial_map_eq A (cf g) fun s hs => hA s (Finset.mem_biUnion.mpr ⟨g, hg, hs⟩)
  choose! cf' hcf' using hlift
  have hgen : ∀ g ∈ t, ∃ c : ℕ, (Q.coeff c).map A.subtype = g := by
    intro g hg
    obtain ⟨c, hc⟩ := Set.mem_range.mp (hts hg)
    refine ⟨c, ?_⟩
    have : P.coeff c = (Q.coeff c).map A.subtype := by rw [← hQ, coeff_map, coe_mapRingHom]
    rw [← this]
    exact hc
  choose! cc hcc using hgen
  have hA1 : (∑ g ∈ t, cf' g * Q.coeff (cc g)) = 1 := by
    apply Polynomial.map_injective A.subtype A.subtype_injective
    rw [Polynomial.map_one, ← hcomb, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Polynomial.map_mul, hcf' g hg, hcc g hg, smul_eq_mul]

  have hκ : (∑ g ∈ t, (cf' g).map (IsLocalRing.residue A) * (redPoly A Q).coeff (cc g)) = 1 := by
    have h := congrArg (Polynomial.map (IsLocalRing.residue A)) hA1
    rw [Polynomial.map_sum, Polynomial.map_one] at h
    rw [← h]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Polynomial.map_mul]
    congr 1
    rw [redPoly, coeff_map, coe_mapRingHom]
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have hr1 : r ∣ 1 := by
    rw [← hκ]
    exact Finset.dvd_sum fun g _ => (hr (cc g)).mul_left _
  exact isUnit_of_dvd_one hr1

end Primitivity

end PlaneRelationReduction
end

section

open Polynomial

namespace PlaneRelationReduction

section Swap

variable {R : Type*} [CommRing R]

private theorem coeff_coeff_swap (p : Polynomial (Polynomial R)) (i j : ℕ) :
    ((Polynomial.Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial n q =>
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => simp only [map_add, coeff_add, h₁, h₂]
    | monomial m r =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [coeff_monomial, hi, hj]

private theorem natDegree_coeff_le_natDegree_swap (p : Polynomial (Polynomial R)) (c : ℕ) :
    (p.coeff c).natDegree ≤ (Polynomial.Bivariate.swap p).natDegree := by
  by_cases h : p.coeff c = 0
  · rw [h, natDegree_zero]; exact Nat.zero_le _
  · apply le_natDegree_of_ne_zero
    intro h0
    have h1 := congrArg (fun q : Polynomial R => q.coeff c) h0
    simp only [coeff_coeff_swap, coeff_zero] at h1
    exact h (leadingCoeff_eq_zero.mp h1)

private theorem natDegree_swap_le (p : Polynomial (Polynomial R)) (D : ℕ) (hD : ∀ c, (p.coeff c).natDegree ≤ D) :
    (Polynomial.Bivariate.swap p).natDegree ≤ D := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  ext c
  rw [coeff_coeff_swap, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hD c) hN)

variable [IsDomain R]

private theorem natDegree_coeff_le_of_mul_eq {a b q : Polynomial (Polynomial R)} (hab : a * b = q) (hb : b ≠ 0) (D : ℕ)
    (hq : ∀ c, (q.coeff c).natDegree ≤ D) (c : ℕ) : (a.coeff c).natDegree ≤ D := by
  by_cases ha : a = 0
  · rw [ha, coeff_zero, natDegree_zero]; exact Nat.zero_le _
  · refine (natDegree_coeff_le_natDegree_swap a c).trans (le_trans ?_ (natDegree_swap_le q D hq))
    rw [← hab, map_mul,
      natDegree_mul ((map_ne_zero_iff _ (Polynomial.Bivariate.swap (R := R)).injective).mpr ha)
        ((map_ne_zero_iff _ (Polynomial.Bivariate.swap (R := R)).injective).mpr hb)]
    exact Nat.le_add_right _ _

private theorem exists_table_of_mul_eq (d : ℕ) {a b q : Polynomial (Polynomial R)} (hab : a * b = q) (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hq : ∀ c, (q.coeff c).natDegree ≤ d) :
    ∃ w : SysVar d a.natDegree b.natDegree → R,
      ofTable d a.natDegree (fun i j => w (Sum.inl (i, j))) *
        ofTable d b.natDegree (fun i j => w (Sum.inr (i, j))) = q := by
  refine ⟨Sum.elim (fun ij => (a.coeff ij.2).coeff ij.1) (fun ij => (b.coeff ij.2).coeff ij.1), ?_⟩
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [ofTable_coeff_eq_self d a.natDegree a le_rfl (natDegree_coeff_le_of_mul_eq hab hb d hq),
    ofTable_coeff_eq_self d b.natDegree b le_rfl
      (natDegree_coeff_le_of_mul_eq (by rw [mul_comm]; exact hab) ha d hq)]
  exact hab

end Swap

end PlaneRelationReduction
end

section

open Polynomial

namespace PlaneRelationReduction

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem exists_finset_forall_exists_irreducible_toRes
    [IsAlgClosed L] (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (y : F)
    (hy : IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F)) ({y} : Set F) = ⊤) :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∃ Q : Polynomial (Polynomial A),
          evalFY f y (toL A Q) = 0 ∧
          (toL A Q).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F ∧
          Irreducible (toRes A Q) ∧
          (toRes A Q).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  obtain ⟨P, hPeval, hPdeg, hPprim, hPfac⟩ := exists_bivariate_relation f hf y hy
  set n := Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hPdeg
    omega

  set d := (Finset.range (n + 1)).sup fun c => (P.coeff c).natDegree with hd
  have hPd : ∀ c, (P.coeff c).natDegree ≤ d := by
    intro c
    by_cases hc : c ≤ n
    · exact Finset.le_sup (f := fun c => (P.coeff c).natDegree) (Finset.mem_range.mpr (by omega))
    · have hlt : P.natDegree < c := by omega
      rw [coeff_eq_zero_of_natDegree_lt hlt, natDegree_zero]
      exact Nat.zero_le _
  obtain ⟨S₁, hS₁⟩ := exists_finset_forall_splitting P n hPdeg hPfac d
  obtain ⟨S₂, -, hS₂⟩ := exists_finset_forall_isPrimitive_redPoly P hPprim
  refine ⟨(S₁ ∪ S₂ ∪ biConstants P).filter (fun s => s ≠ 0), fun s hs => (Finset.mem_filter.mp hs).2, ?_⟩
  intro A hA
  have hmem : ∀ s ∈ S₁ ∪ S₂ ∪ biConstants P, s ∈ A := by
    intro s hs
    by_cases h0 : s = 0
    · rw [h0]; exact A.zero_mem
    · exact A.mem_of_valuation_le_one s (le_of_eq (hA s (Finset.mem_filter.mpr ⟨hs, h0⟩)))
  have hmem₁ : ∀ s ∈ S₁, s ∈ A := fun s hs => hmem s (Finset.mem_union_left _ (Finset.mem_union_left _ hs))
  have hmem₂ : ∀ s ∈ S₂, s ∈ A := fun s hs => hmem s (Finset.mem_union_left _ (Finset.mem_union_right _ hs))
  have hmem₃ : ∀ s ∈ biConstants P, s ∈ A := fun s hs => hmem s (Finset.mem_union_right _ hs)
  obtain ⟨Q, hQ⟩ := exists_bivariate_map_eq A P hmem₃
  have htoL : toL A Q = P := hQ

  set Qb := redPoly A Q with hQb
  have hQdeg : Q.natDegree = n := by
    rw [← hPdeg, ← hQ]
    exact (natDegree_map_eq_of_injective
      (by rw [coe_mapRingHom]; exact Polynomial.map_injective A.subtype A.subtype_injective) Q).symm
  have hQbdeg_le : Qb.natDegree ≤ n := by
    rw [← hQdeg]
    exact natDegree_map_le
  have hlead : Qb.coeff n ≠ 0 := by
    have hPn : P.coeff n ≠ 0 := by
      rw [← hPdeg]
      exact leadingCoeff_ne_zero.mpr hP0
    set m := (P.coeff n).natDegree with hm
    have hℓ : (P.coeff n).coeff m ≠ 0 := leadingCoeff_ne_zero.mpr hPn
    have hℓmem : (P.coeff n).coeff m ∈ biConstants P := by
      unfold biConstants
      exact Finset.mem_biUnion.mpr
        ⟨n, Finset.mem_range.mpr (by rw [hPdeg]; exact Nat.lt_succ_self n), coeff_mem_polyConstants _ _ hℓ⟩
    have hval : A.valuation ((P.coeff n).coeff m) = 1 :=
      hA _ (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hℓmem, hℓ⟩)
    have hQcoeff : A.subtype ((Q.coeff n).coeff m) = (P.coeff n).coeff m := by
      rw [← hQ, coeff_map, coe_mapRingHom, coeff_map]
    have hQcoeff' : (((Q.coeff n).coeff m : A) : L) = (P.coeff n).coeff m := hQcoeff
    have hQunit : IsUnit ((Q.coeff n).coeff m) := by
      rw [ValuationSubring.valuation_eq_one_iff, hQcoeff']
      exact hval
    intro hzero
    have h1 : (Qb.coeff n).coeff m = IsLocalRing.residue A ((Q.coeff n).coeff m) := by
      simp only [hQb, redPoly, coeff_map, coe_mapRingHom]
    rw [hzero, coeff_zero] at h1
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hQunit h1.symm
  have hQbdeg : Qb.natDegree = n := le_antisymm hQbdeg_le (le_natDegree_of_ne_zero hlead)
  have hQb0 : Qb ≠ 0 := fun h => hlead (by rw [h, coeff_zero])
  have hprim : Qb.IsPrimitive := hS₂ A hmem₂ Q hQ
  have hQbd : ∀ c, (Qb.coeff c).natDegree ≤ d := by
    intro c
    have h1 : (Q.coeff c).natDegree = (P.coeff c).natDegree := by
      rw [← hQ, coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective A.subtype_injective]
    calc (Qb.coeff c).natDegree = ((Q.coeff c).map (IsLocalRing.residue A)).natDegree := by
          simp only [hQb, redPoly, coeff_map, coe_mapRingHom]
      _ ≤ (Q.coeff c).natDegree := natDegree_map_le
      _ = (P.coeff c).natDegree := h1
      _ ≤ d := hPd c

  have hirr : Irreducible Qb := by
    refine irreducible_iff.mpr ⟨fun hu => ?_, ?_⟩
    · have := natDegree_eq_zero_of_isUnit hu
      omega
    intro a b hab
    have ha : a ≠ 0 := fun h => hQb0 (by rw [hab, h, zero_mul])
    have hb : b ≠ 0 := fun h => hQb0 (by rw [hab, h, mul_zero])
    have hdeg : a.natDegree + b.natDegree = n := by
      rw [← hQbdeg, hab, natDegree_mul ha hb]
    by_cases ha0 : a.natDegree = 0
    · left
      rw [eq_C_of_natDegree_eq_zero ha0, isUnit_C]
      apply hprim
      exact ⟨b, by rw [← eq_C_of_natDegree_eq_zero ha0]; exact hab⟩
    by_cases hb0 : b.natDegree = 0
    · right
      rw [eq_C_of_natDegree_eq_zero hb0, isUnit_C]
      apply hprim
      exact ⟨a, by rw [← eq_C_of_natDegree_eq_zero hb0, mul_comm]; exact hab⟩
    exfalso
    obtain ⟨w, hw⟩ := exists_table_of_mul_eq d hab.symm ha hb hQbd
    exact hS₁ A hmem₁ Q hQ a.natDegree b.natDegree (by omega) (by omega) hdeg w hw
  have htoRes : toRes A Q = Qb.map (algebraMap (Polynomial (IsLocalRing.ResidueField A))
      (RatFunc (IsLocalRing.ResidueField A))) := rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · rw [htoL]; exact hPeval
  · rw [htoL]; exact hPdeg
  · rw [htoRes]
    exact hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  · rw [htoRes, natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial (IsLocalRing.ResidueField A))
      (RatFunc (IsLocalRing.ResidueField A))), hQbdeg]

end PlaneRelationReduction

end

section

open Polynomial

namespace PlaneRelationReduction

private theorem isUnit_of_mul_eq_one' {M : Type*} [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit a :=
  ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩

section Conclusions

variable {κ : Type*} [Field κ]

private theorem finrank_adjoin_map {E₁ E₂ : Type*} [Field E₁] [Field E₂] [Algebra κ E₁] [Algebra κ E₂]
    (e : E₁ ≃ₐ[κ] E₂) (x : E₁) :
    Module.finrank (IntermediateField.adjoin κ ({x} : Set E₁)) E₁
      = Module.finrank (IntermediateField.adjoin κ ({e x} : Set E₂)) E₂ := by
  have hmap : (IntermediateField.adjoin κ ({x} : Set E₁)).map e.toAlgHom
      = IntermediateField.adjoin κ ({e x} : Set E₂) := by
    simp [IntermediateField.adjoin_map]
  exact Algebra.finrank_eq_of_equiv_equiv
    ((IntermediateField.intermediateFieldMap e _).trans (IntermediateField.equivOfEq hmap)).toRingEquiv
    e.toRingEquiv (RingHom.ext fun _ => rfl)

private theorem finrank_adjoin_algebraMap_X (T : Type*) [Field T] [Algebra κ T] [Algebra (RatFunc κ) T]
    [IsScalarTower κ (RatFunc κ) T] :
    Module.finrank (IntermediateField.adjoin κ ({algebraMap (RatFunc κ) T RatFunc.X} : Set T)) T
      = Module.finrank (RatFunc κ) T := by
  have key : ∀ p : κ[X], aeval (algebraMap (RatFunc κ) T RatFunc.X) p
      = algebraMap (RatFunc κ) T (algebraMap κ[X] (RatFunc κ) p) := fun p => by
    rw [aeval_algebraMap_apply, ← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]
  have hmem : ∀ q : RatFunc κ, algebraMap (RatFunc κ) T q
      ∈ IntermediateField.adjoin κ ({algebraMap (RatFunc κ) T RatFunc.X} : Set T) := fun q =>
    RatFunc.induction_on (P := fun q => algebraMap (RatFunc κ) T q
        ∈ IntermediateField.adjoin κ ({algebraMap (RatFunc κ) T RatFunc.X} : Set T)) q fun p p' _ => by
      show algebraMap (RatFunc κ) T (_ / _) ∈ _
      rw [map_div₀]
      exact (IntermediateField.mem_adjoin_simple_iff _ _).mpr ⟨p, p', by rw [key, key]⟩
  have hbij : Function.Bijective ((algebraMap (RatFunc κ) T).codRestrict
      (IntermediateField.adjoin κ ({algebraMap (RatFunc κ) T RatFunc.X} : Set T)) hmem) := by
    refine ⟨fun a b hab => (algebraMap (RatFunc κ) T).injective (congrArg Subtype.val hab), fun z => ?_⟩
    obtain ⟨r, s, hz⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp z.2
    refine ⟨algebraMap κ[X] (RatFunc κ) r / algebraMap κ[X] (RatFunc κ) s, Subtype.ext ?_⟩
    show algebraMap (RatFunc κ) T (_ / _) = (z : T)
    rw [hz, map_div₀, key, key]
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective _ hbij) (RingEquiv.refl T)
    (RingHom.ext fun _ => rfl)).symm

private theorem transcendental_and_finrank_of_ringEquiv {E T : Type*} [Field E] [Field T] [Algebra κ E] [Algebra κ T]
    (e : E ≃+* T) (he : ∀ c : κ, e (algebraMap κ E c) = algebraMap κ T c) {x : E} {s : T} (hx : e x = s)
    (hs : Transcendental κ s) {n : ℕ} (hn : Module.finrank (IntermediateField.adjoin κ ({s} : Set T)) T = n) :
    Transcendental κ x ∧ Module.finrank (IntermediateField.adjoin κ ({x} : Set E)) E = n := by
  let ea : E ≃ₐ[κ] T := AlgEquiv.ofRingEquiv (f := e) he
  have hea : ea x = s := by rw [← hx]; rfl
  refine ⟨fun halg => hs ?_, ?_⟩
  · rw [← hea]
    exact (isAlgebraic_algHom_iff ea.toAlgHom ea.injective).mpr halg
  · rw [finrank_adjoin_map ea x, hea, hn]

end Conclusions

namespace KD

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] {k₀ : Type*} [Field k₀]
variable (G : ValuationSubring K) (ρ₀ : G →+* k₀) (y : F) (P : G[X])

private noncomputable def evG : G[X] →+* F :=
  ((Polynomial.aeval y : K[X] →ₐ[K] F) : K[X] →+* F).comp (Polynomial.mapRingHom (algebraMap G K))

private structure Setup : Prop where
  monic : P.Monic
  natDegree_pos : 0 < P.natDegree
  evG_P : evG G y P = 0
  gen : ∀ z : F, ∃ r : K[X], aeval y r = z
  uniq : ∀ r : K[X], r.natDegree < P.natDegree → aeval y r = 0 → r = 0
  irr : Irreducible (P.map ρ₀)
  isUnit_of_ne_zero : ∀ g : G, ρ₀ g ≠ 0 → IsUnit g
  surj : Function.Surjective ρ₀

variable {G ρ₀ y P}

private theorem evG_apply (p : G[X]) : evG G y p = aeval y (p.map (algebraMap G K)) := rfl

private theorem evG_C (g : G) : evG G y (C g) = algebraMap K F (g : K) := by
  rw [evG_apply, Polynomial.map_C, aeval_C]
  rfl

private theorem algebraMap_G_injective : Function.Injective (algebraMap G K) := fun _ _ hab => Subtype.ext hab

private theorem P_ne_one (h : Setup G ρ₀ y P) : P ≠ 1 := fun hP1 => by
  have := h.natDegree_pos
  rw [hP1, natDegree_one] at this
  exact lt_irrefl 0 this

private theorem evG_modByMonic (h : Setup G ρ₀ y P) (p : G[X]) : evG G y (p %ₘ P) = evG G y p := by
  conv_rhs => rw [← modByMonic_add_div p P]
  rw [map_add, map_mul, h.evG_P, zero_mul, add_zero]

private theorem natDegree_modByMonic_lt' (h : Setup G ρ₀ y P) (p : G[X]) : (p %ₘ P).natDegree < P.natDegree :=
  natDegree_modByMonic_lt p h.monic (P_ne_one h)

private theorem P_dvd_of_evG_eq_zero (h : Setup G ρ₀ y P) {p : G[X]} (hp : evG G y p = 0) : P ∣ p := by
  rw [← modByMonic_eq_zero_iff_dvd h.monic]
  have h1 : evG G y (p %ₘ P) = 0 := by rw [evG_modByMonic h, hp]
  rw [evG_apply] at h1
  have h2 := h.uniq _ (lt_of_le_of_lt natDegree_map_le (natDegree_modByMonic_lt' h p)) h1
  exact (Polynomial.map_eq_zero_iff algebraMap_G_injective).mp h2

private theorem algebraMap_mem_range_iff (h : Setup G ρ₀ y P) (c : K) :
    algebraMap K F c ∈ (evG G y).range ↔ c ∈ G := by
  constructor
  · rintro ⟨p, hp⟩
    have hr1 : evG G y (p %ₘ P) = algebraMap K F c := by rw [evG_modByMonic h, hp]
    rw [evG_apply] at hr1
    have ht : aeval y ((p %ₘ P).map (algebraMap G K) - C c) = 0 := by
      rw [map_sub, aeval_C, hr1, sub_self]
    have hdeg : ((p %ₘ P).map (algebraMap G K) - C c).natDegree < P.natDegree := by
      refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt natDegree_map_le (natDegree_modByMonic_lt' h p)
      · rw [natDegree_C]; exact h.natDegree_pos
    have h0 := h.uniq _ hdeg ht
    rw [sub_eq_zero] at h0
    have hc : ((p %ₘ P).map (algebraMap G K)).coeff 0 = (C c).coeff 0 := by rw [h0]
    rw [coeff_map, coeff_C_zero] at hc
    rw [← hc]
    exact ((p %ₘ P).coeff 0).2
  · intro hc
    refine ⟨C ⟨c, hc⟩, ?_⟩
    rw [evG_C]

variable [Fact (Irreducible (P.map ρ₀))]

variable (G ρ₀ P) in

private noncomputable def ψ : G[X] →+* AdjoinRoot (P.map ρ₀) :=
  (AdjoinRoot.mk (P.map ρ₀)).comp (Polynomial.mapRingHom ρ₀)

private theorem ψ_apply (p : G[X]) : ψ G ρ₀ P p = AdjoinRoot.mk (P.map ρ₀) (p.map ρ₀) := rfl

private theorem ψ_P : ψ G ρ₀ P P = 0 := AdjoinRoot.mk_self

private theorem ψ_C (g : G) : ψ G ρ₀ P (C g) = algebraMap k₀ (AdjoinRoot (P.map ρ₀)) (ρ₀ g) := by
  rw [ψ_apply, Polynomial.map_C, AdjoinRoot.mk_C]
  rfl

private theorem ψ_modByMonic (p : G[X]) : ψ G ρ₀ P (p %ₘ P) = ψ G ρ₀ P p := by
  conv_rhs => rw [← modByMonic_add_div p P]
  rw [map_add, map_mul, ψ_P, zero_mul, add_zero]

private theorem ψ_eq_zero_of_evG_eq_zero (h : Setup G ρ₀ y P) {p : G[X]} (hp : evG G y p = 0) : ψ G ρ₀ P p = 0 :=
  AdjoinRoot.mk_eq_zero.mpr (Polynomial.map_dvd ρ₀ (P_dvd_of_evG_eq_zero h hp))

private theorem evG_ne_zero_of_ψ_ne_zero (h : Setup G ρ₀ y P) {p : G[X]} (hp : ψ G ρ₀ P p ≠ 0) : evG G y p ≠ 0 :=
  fun h0 => hp (ψ_eq_zero_of_evG_eq_zero h h0)

private theorem exists_eq_algebraMap_mul_evG (h : Setup G ρ₀ y P) (z : F) (hz : z ≠ 0) :
    ∃ (c : K) (s : G[X]), c ≠ 0 ∧ ψ G ρ₀ P s ≠ 0 ∧ z = algebraMap K F c * evG G y s := by

  obtain ⟨r, hry, hr0, hrdeg⟩ : ∃ r : K[X], aeval y r = z ∧ r ≠ 0 ∧ r.natDegree < P.natDegree := by
    obtain ⟨r₀, hr₀⟩ := h.gen z
    have hPKm : (P.map (algebraMap G K)).Monic := h.monic.map _
    have hPKy : aeval y (P.map (algebraMap G K)) = 0 := h.evG_P
    have hPK1 : P.map (algebraMap G K) ≠ 1 := fun h1 => by
      have h2 := h.monic.natDegree_map (algebraMap G K)
      rw [h1, natDegree_one] at h2
      exact h.natDegree_pos.ne h2
    have hry : aeval y (r₀ %ₘ P.map (algebraMap G K)) = z := by
      rw [← hr₀]
      conv_rhs => rw [← modByMonic_add_div r₀ (P.map (algebraMap G K))]
      rw [map_add, map_mul, hPKy, zero_mul, add_zero]
    refine ⟨r₀ %ₘ P.map (algebraMap G K), hry, fun h0 => hz (by rw [← hry, h0, map_zero]), ?_⟩
    calc (r₀ %ₘ P.map (algebraMap G K)).natDegree < (P.map (algebraMap G K)).natDegree :=
          natDegree_modByMonic_lt r₀ hPKm hPK1
      _ = P.natDegree := h.monic.natDegree_map _

  obtain ⟨i₀, hi₀, hmax⟩ := r.support.exists_max_image (fun i => G.valuation (r.coeff i))
    (nonempty_support_iff.mpr hr0)
  have hc0 : r.coeff i₀ ≠ 0 := mem_support_iff.mp hi₀
  have hv : ∀ i, G.valuation (r.coeff i) ≤ G.valuation (r.coeff i₀) := by
    intro i
    by_cases hi : i ∈ r.support
    · exact hmax i hi
    · have h0 : r.coeff i = 0 := by
        by_contra hne
        exact hi (mem_support_iff.mpr hne)
      rw [h0, map_zero]
      exact zero_le'
  have hvc : 0 < G.valuation (r.coeff i₀) := zero_lt_iff.mpr fun h0 => hc0 ((Valuation.zero_iff _).mp h0)

  have hmem : ∀ i, (r * C (r.coeff i₀)⁻¹).coeff i ∈ G := by
    intro i
    rw [coeff_mul_C, ← div_eq_mul_inv, ← G.valuation_le_one_iff, map_div₀]
    exact (div_le_one₀ hvc).mpr (hv i)
  obtain ⟨s, hs⟩ := (mem_lifts (f := algebraMap G K) (r * C (r.coeff i₀)⁻¹)).mp
    ((lifts_iff_coeff_lifts (f := algebraMap G K) (r * C (r.coeff i₀)⁻¹)).mpr (fun i => ⟨⟨_, hmem i⟩, rfl⟩))
  refine ⟨r.coeff i₀, s, hc0, ?_, ?_⟩
  ·
    intro hψ
    rw [ψ_apply, AdjoinRoot.mk_eq_zero] at hψ
    have hs_i₀ : s.coeff i₀ = 1 := by
      apply Subtype.ext
      have h1 : (s.map (algebraMap G K)).coeff i₀ = (r * C (r.coeff i₀)⁻¹).coeff i₀ := by rw [hs]
      rw [coeff_map, coeff_mul_C, mul_inv_cancel₀ hc0] at h1
      exact h1
    have hne : s.map ρ₀ ≠ 0 := fun h1 => by
      have h2 : (s.map ρ₀).coeff i₀ = (0 : k₀[X]).coeff i₀ := by rw [h1]
      rw [coeff_map, hs_i₀, map_one, coeff_zero] at h2
      exact one_ne_zero h2
    have hdeg : (s.map ρ₀).natDegree < (P.map ρ₀).natDegree :=
      calc (s.map ρ₀).natDegree ≤ s.natDegree := natDegree_map_le
        _ = (s.map (algebraMap G K)).natDegree := (natDegree_map_eq_of_injective algebraMap_G_injective s).symm
        _ ≤ r.natDegree := by rw [hs]; exact natDegree_mul_C_le _ _
        _ < P.natDegree := hrdeg
        _ = (P.map ρ₀).natDegree := (h.monic.natDegree_map ρ₀).symm
    exact absurd (natDegree_le_of_dvd hψ hne) (not_le.mpr hdeg)
  · have hc' : algebraMap K F (r.coeff i₀) ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hc0
    rw [evG_apply, hs, _root_.map_mul, aeval_C, ← hry, map_inv₀, mul_comm, mul_assoc, inv_mul_cancel₀ hc', mul_one]

private theorem exists_evG_mul_eq_one (h : Setup G ρ₀ y P) {p : G[X]} (hp : ψ G ρ₀ P p ≠ 0) :
    ∃ q : G[X], evG G y p * evG G y q = 1 := by
  have hp0 : evG G y p ≠ 0 := evG_ne_zero_of_ψ_ne_zero h hp
  obtain ⟨c, s, hc, hs, hz⟩ := exists_eq_algebraMap_mul_evG h (evG G y p)⁻¹ (inv_ne_zero hp0)
  have hd_ψ : ψ G ρ₀ P ((p * s) %ₘ P) ≠ 0 := by
    rw [ψ_modByMonic, map_mul]; exact mul_ne_zero hp hs
  have hd_ev : evG G y ((p * s) %ₘ P) = evG G y p * evG G y s := by rw [evG_modByMonic h, map_mul]
  have hd_deg := natDegree_modByMonic_lt' h (p * s)
  have hkey : algebraMap K F c * evG G y ((p * s) %ₘ P) = 1 := by
    rw [hd_ev, mul_left_comm, ← hz, mul_inv_cancel₀ hp0]

  obtain ⟨i, hi⟩ : ∃ i, ρ₀ (((p * s) %ₘ P).coeff i) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hd_ψ
    rw [ψ_apply]
    have h0 : ((p * s) %ₘ P).map ρ₀ = 0 := by
      ext j; rw [coeff_map, hall j, coeff_zero]
    rw [h0, map_zero]
  have hunit : IsUnit (((p * s) %ₘ P).coeff i) := h.isUnit_of_ne_zero _ hi

  have hpoly : C c * (((p * s) %ₘ P).map (algebraMap G K)) = 1 := by
    rw [← sub_eq_zero]
    apply h.uniq
    · refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (lt_of_le_of_lt natDegree_map_le hd_deg)
      · rw [natDegree_one]; exact h.natDegree_pos
    · rw [map_sub, map_mul, aeval_C, map_one, ← evG_apply, hkey, sub_self]
  have hcoeff : (C c * (((p * s) %ₘ P).map (algebraMap G K))).coeff i = (1 : K[X]).coeff i := by rw [hpoly]
  rw [coeff_C_mul, coeff_map, coeff_one] at hcoeff
  have hdi : algebraMap G K (((p * s) %ₘ P).coeff i) ≠ 0 := fun h0 =>
    hunit.ne_zero (algebraMap_G_injective (by rw [h0, map_zero]))
  split_ifs at hcoeff with hi0
  · subst hi0
    obtain ⟨u, hu⟩ := hunit
    have hcG : c ∈ G := by
      have h1 : algebraMap G K (u : G) * algebraMap G K (↑u⁻¹ : G) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [hu] at h1
      have hc_eq : c = algebraMap G K (↑u⁻¹ : G) :=
        calc c = c * (algebraMap G K (((p * s) %ₘ P).coeff 0) * algebraMap G K (↑u⁻¹ : G)) := by
              rw [h1, mul_one]
          _ = (c * algebraMap G K (((p * s) %ₘ P).coeff 0)) * algebraMap G K (↑u⁻¹ : G) := by ring
          _ = algebraMap G K (↑u⁻¹ : G) := by rw [hcoeff, one_mul]
      rw [hc_eq]
      exact (↑u⁻¹ : G).2
    refine ⟨C ⟨c, hcG⟩ * s, ?_⟩
    rw [map_mul, evG_C]
    show evG G y p * (algebraMap K F c * evG G y s) = 1
    rw [← hz, mul_inv_cancel₀ hp0]
  · exact absurd hcoeff (mul_ne_zero hc hdi)

private theorem _root_.PlaneRelationReduction.KD.mem_or_inv_mem (h : Setup G ρ₀ y P) (z : F) : z ∈ (evG G y).range ∨ z⁻¹ ∈ (evG G y).range := by
  by_cases hz : z = 0
  · left; rw [hz]; exact zero_mem _
  obtain ⟨c, s, _, hs, hzeq⟩ := exists_eq_algebraMap_mul_evG h z hz
  obtain ⟨q, hq⟩ := exists_evG_mul_eq_one h hs
  rcases G.mem_or_inv_mem c with hcG | hcG
  · left
    refine ⟨C ⟨c, hcG⟩ * s, ?_⟩
    rw [map_mul, evG_C, hzeq]
  · right
    refine ⟨C ⟨c⁻¹, hcG⟩ * q, ?_⟩
    rw [map_mul, evG_C, hzeq, mul_inv, inv_eq_of_mul_eq_one_right hq, ← map_inv₀]

p2m_export "PlaneRelationReduction.KD" "mem_or_inv_mem"

private noncomputable def V (h : Setup G ρ₀ y P) : ValuationSubring F where
  toSubring := (evG G y).range
  mem_or_inv_mem' := mem_or_inv_mem h

private theorem mem_V_iff (h : Setup G ρ₀ y P) (z : F) : z ∈ V h ↔ ∃ p : G[X], evG G y p = z := RingHom.mem_range

private theorem evG_mem_V (h : Setup G ρ₀ y P) (p : G[X]) : evG G y p ∈ V h := (mem_V_iff h _).mpr ⟨p, rfl⟩

private theorem algebraMap_mem_V_iff (h : Setup G ρ₀ y P) (c : K) : algebraMap K F c ∈ V h ↔ c ∈ G :=
  algebraMap_mem_range_iff h c

private noncomputable def evV (h : Setup G ρ₀ y P) : G[X] →+* V h := (evG G y).codRestrict (V h) (evG_mem_V h)

private theorem coe_evV (h : Setup G ρ₀ y P) (p : G[X]) : ((evV h p : V h) : F) = evG G y p := rfl

private theorem evV_surjective (h : Setup G ρ₀ y P) : Function.Surjective (evV h) := fun v => by
  obtain ⟨p, hp⟩ := (mem_V_iff h v).mp v.2
  exact ⟨p, Subtype.ext hp⟩

private noncomputable def ρ (h : Setup G ρ₀ y P) : V h →+* AdjoinRoot (P.map ρ₀) :=
  (evV h).liftOfSurjective (evV_surjective h) ⟨ψ G ρ₀ P, fun p hp => by
    rw [RingHom.mem_ker] at hp ⊢
    exact ψ_eq_zero_of_evG_eq_zero h (congrArg Subtype.val hp)⟩

private theorem ρ_evV (h : Setup G ρ₀ y P) (p : G[X]) : ρ h (evV h p) = ψ G ρ₀ P p := by
  unfold ρ
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem isUnit_of_ρ_ne_zero (h : Setup G ρ₀ y P) {v : V h} (hv : ρ h v ≠ 0) : IsUnit v := by
  obtain ⟨p, rfl⟩ := evV_surjective h v
  rw [ρ_evV] at hv
  obtain ⟨q, hq⟩ := exists_evG_mul_eq_one h hv
  exact isUnit_of_mul_eq_one' _ (evV h q) (Subtype.ext hq)

private theorem ρ_ne_zero_of_isUnit (h : Setup G ρ₀ y P) {v : V h} (hv : IsUnit v) : ρ h v ≠ 0 :=
  (hv.map (ρ h)).ne_zero

private theorem ker_ρ (h : Setup G ρ₀ y P) : RingHom.ker (ρ h) = IsLocalRing.maximalIdeal (V h) := by
  ext v
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h0 hu => ρ_ne_zero_of_isUnit h hu h0,
    fun hnu => by_contra fun h0 => hnu (isUnit_of_ρ_ne_zero h h0)⟩

private theorem ρ_surjective (h : Setup G ρ₀ y P) : Function.Surjective (ρ h) := by
  intro t
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective t
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective ρ₀ h.surj q
  exact ⟨evV h p, ρ_evV h p⟩

private noncomputable def resEquiv (h : Setup G ρ₀ y P) : IsLocalRing.ResidueField (V h) ≃+* AdjoinRoot (P.map ρ₀) :=
  (Ideal.quotEquivOfEq (ker_ρ h).symm).trans (RingHom.quotientKerEquivOfSurjective (ρ_surjective h))

private theorem resEquiv_residue (h : Setup G ρ₀ y P) (v : V h) :
    resEquiv h (IsLocalRing.residue (V h) v) = ρ h v := rfl

private noncomputable def constV (h : Setup G ρ₀ y P) : G →+* V h := (evV h).comp Polynomial.C

private theorem coe_constV (h : Setup G ρ₀ y P) (g : G) : ((constV h g : V h) : F) = algebraMap K F (g : K) := evG_C g

private theorem resEquiv_residue_constV (h : Setup G ρ₀ y P) (g : G) :
    resEquiv h (IsLocalRing.residue (V h) (constV h g)) = algebraMap k₀ (AdjoinRoot (P.map ρ₀)) (ρ₀ g) := by
  rw [resEquiv_residue]
  show ρ h (evV h (C g)) = _
  rw [ρ_evV, ψ_C]

private theorem exists_eq_algebraMap_mul_unit (h : Setup G ρ₀ y P) (z : F) (hz : z ≠ 0) :
    ∃ (c : K) (v : V h), c ≠ 0 ∧ IsUnit v ∧ z = algebraMap K F c * (v : F) := by
  obtain ⟨c, s, hc, hs, hzeq⟩ := exists_eq_algebraMap_mul_evG h z hz
  exact ⟨c, evV h s, hc, isUnit_of_ρ_ne_zero h (by rw [ρ_evV]; exact hs), hzeq⟩

end KD

namespace KD

private theorem conclusions {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] {κ₀ : Type*} [Field κ₀]
    {G : ValuationSubring K} {ρ₀ : G →+* RatFunc κ₀} {y : F} {P : G[X]} [Fact (Irreducible (P.map ρ₀))]
    (h : Setup G ρ₀ y P) [algk : Algebra κ₀ (IsLocalRing.ResidueField (V h))]
    (hcomm : ∀ c : κ₀, resEquiv h (algebraMap κ₀ (IsLocalRing.ResidueField (V h)) c)
      = algebraMap κ₀ (AdjoinRoot (P.map ρ₀)) c)
    (v : V h)
    (hv : resEquiv h (IsLocalRing.residue (V h) v) = algebraMap (RatFunc κ₀) (AdjoinRoot (P.map ρ₀)) RatFunc.X) :
    Transcendental κ₀ (IsLocalRing.residue (V h) v) ∧
      Module.finrank
          (IntermediateField.adjoin κ₀ ({IsLocalRing.residue (V h) v} : Set (IsLocalRing.ResidueField (V h))))
          (IsLocalRing.ResidueField (V h))
        = (P.map ρ₀).natDegree :=
  transcendental_and_finrank_of_ringEquiv (resEquiv h) hcomm hv
    ((transcendental_algebraMap_iff (algebraMap (RatFunc κ₀) (AdjoinRoot (P.map ρ₀))).injective).mpr
      RatFunc.transcendental_X)
    ((finrank_adjoin_algebraMap_X (AdjoinRoot (P.map ρ₀))).trans (AdjoinRoot.powerBasis h.irr.ne_zero).finrank)

end KD

end PlaneRelationReduction

end

section

namespace PlaneRelationReduction

section Steps

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem exists_embedding (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F] (y : F)
    (hy : IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F)) ({y} : Set F) = ⊤) :
    ∃ ι : RatFunc L →ₐ[L] F,
      (∀ p : Polynomial L, ι (algebraMap (Polynomial L) (RatFunc L) p) = Polynomial.aeval f p) ∧
      ι RatFunc.X = f ∧
      (∀ z : F, ∃ r : Polynomial (RatFunc L), r.eval₂ ι.toRingHom y = z) ∧
      (∀ r : Polynomial (RatFunc L), r.natDegree < Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
        r.eval₂ ι.toRingHom y = 0 → r = 0) := by
  classical
  have hinj : Function.Injective (Polynomial.aeval f : Polynomial L →ₐ[L] F) := transcendental_iff_injective.mp hf
  obtain ⟨ι, hι, hι_alg⟩ : ∃ ι : RatFunc L →ₐ[L] F, Function.Injective ι ∧
      ∀ p : Polynomial L, ι (algebraMap (Polynomial L) (RatFunc L) p) = Polynomial.aeval f p :=
    ⟨RatFunc.liftAlgHom (Polynomial.aeval f) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj),
      RatFunc.liftAlgHom_injective _ hinj, fun p => by
        simpa using RatFunc.liftAlgHom_apply_div (Polynomial.aeval f)
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) p 1⟩
  have hιX : ι RatFunc.X = f := by rw [← RatFunc.algebraMap_X, hι_alg, Polynomial.aeval_X]
  letI : Algebra (RatFunc L) F := ι.toRingHom.toAlgebra
  haveI : IsScalarTower L (RatFunc L) F := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  have halg : ∀ r : RatFunc L, algebraMap (RatFunc L) F r = ι r := fun _ => rfl

  have hι_mem : ∀ r : RatFunc L, ι r ∈ IntermediateField.adjoin L ({f} : Set F) := fun r =>
    RatFunc.induction_on (P := fun r => ι r ∈ IntermediateField.adjoin L ({f} : Set F)) r fun p q _ => by
      show ι (_ / _) ∈ _
      rw [map_div₀, hι_alg, hι_alg]
      exact (IntermediateField.mem_adjoin_simple_iff _ _).mpr ⟨p, q, rfl⟩
  obtain ⟨ιK, hιK⟩ : ∃ ιK : RatFunc L →+* IntermediateField.adjoin L ({f} : Set F),
      ∀ r, (ιK r : F) = ι r :=
    ⟨ι.toRingHom.codRestrict (IntermediateField.adjoin L ({f} : Set F)) hι_mem, fun _ => rfl⟩
  have hιK_inj : Function.Injective ιK := fun a b hab => hι (by rw [← hιK, ← hιK, hab])
  have hιK_surj : Function.Surjective ιK := by
    intro c
    have hle : IntermediateField.adjoin L ({f} : Set F) ≤ ι.fieldRange := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact AlgHom.mem_fieldRange.mpr ⟨RatFunc.X, hιX⟩
    obtain ⟨r, hr⟩ := AlgHom.mem_fieldRange.mp (hle c.2)
    exact ⟨r, Subtype.ext (by rw [hιK, hr])⟩
  have hcomp : (algebraMap (IntermediateField.adjoin L ({f} : Set F)) F).comp ιK = algebraMap (RatFunc L) F :=
    RingHom.ext fun r => by rw [RingHom.comp_apply, halg, ← hιK]; rfl
  have hint : IsIntegral (IntermediateField.adjoin L ({f} : Set F)) y := Algebra.IsIntegral.isIntegral y
  have hgen : ∀ z : F, ∃ r : Polynomial (RatFunc L), Polynomial.aeval y r = z := by
    intro z
    have hz : z ∈ IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F)) ({y} : Set F) := by
      rw [hy]; exact IntermediateField.mem_top
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hz
    obtain ⟨rK, hrK⟩ := hz
    obtain ⟨r, hr⟩ := Polynomial.map_surjective ιK hιK_surj rK
    refine ⟨r, ?_⟩
    rw [← hrK, ← hr, Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  have hmin : (minpoly (IntermediateField.adjoin L ({f} : Set F)) y).natDegree
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    rw [← IntermediateField.adjoin.finrank hint, hy, IntermediateField.finrank_top']
  have huniq : ∀ r : Polynomial (RatFunc L),
      r.natDegree < Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
        Polynomial.aeval y r = 0 → r = 0 := by
    intro r hdeg hr0
    by_contra hne
    have hmap_ne : r.map ιK ≠ 0 := (Polynomial.map_ne_zero_iff hιK_inj).mpr hne
    have heval : Polynomial.aeval y (r.map ιK) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def, hr0]
    have h1 := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero _ y hmap_ne heval)
    rw [hmin] at h1
    exact absurd (lt_of_le_of_lt (h1.trans Polynomial.natDegree_map_le) hdeg) (lt_irrefl _)
  exact ⟨ι, hι_alg, hιX, fun z => (hgen z).imp fun r hr => (Polynomial.aeval_def y r).symm.trans hr,
    fun r hr h0 => huniq r hr ((Polynomial.aeval_def y r).trans h0)⟩

private theorem exists_setup [Algebra (RatFunc L) F] (A : ValuationSubring L) (f y : F)
    (halgp : ∀ p : Polynomial L,
      algebraMap (RatFunc L) F (algebraMap (Polynomial L) (RatFunc L) p) = Polynomial.aeval f p)
    (hgen : ∀ z : F, ∃ r : Polynomial (RatFunc L), Polynomial.aeval y r = z)
    (huniq : ∀ r : Polynomial (RatFunc L),
      r.natDegree < Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F → Polynomial.aeval y r = 0 → r = 0)
    (Q : Polynomial (Polynomial A))
    (hQ0 : evalFY f y (toL A Q) = 0)
    (hQdeg : (toL A Q).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hirr : Irreducible (toRes A Q))
    (hresdeg : (toRes A Q).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ R₀ : AlgebraicCurve.RegularProlongation A (RatFunc L) (RatFunc (IsLocalRing.ResidueField A)),
      (∃ hX : (RatFunc.X : RatFunc L) ∈ R₀.integers, R₀.residue ⟨RatFunc.X, hX⟩ = RatFunc.X) ∧
      ∃ P : Polynomial R₀.integers, ∃ _ : KD.Setup R₀.integers R₀.residue y P,
        (P.map R₀.residue).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  obtain ⟨R₀, ⟨hX, hXres⟩, hpoly⟩ := ValuationSubring.exists_regularProlongation_ratFunc A
  obtain ⟨θ, hθ⟩ : ∃ θ : Polynomial A →+* R₀.integers,
      ∀ q : Polynomial A, (θ q : RatFunc L) = algebraMap (Polynomial L) (RatFunc L) (q.map A.subtype) :=
    ⟨((algebraMap (Polynomial L) (RatFunc L)).comp (Polynomial.mapRingHom A.subtype)).codRestrict R₀.integers
      (fun q => (hpoly q).elim fun hq _ => hq), fun _ => rfl⟩
  have hQGres : (Q.map θ).map R₀.residue = toRes A Q := by
    unfold toRes
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun q => ?_
    obtain ⟨hq, hres⟩ := hpoly q
    have hθq : θ q = ⟨_, hq⟩ := Subtype.ext (hθ q)
    rw [RingHom.comp_apply, hθq, hres]
    rfl
  have hQnat : Q.natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    rw [← hQdeg]
    unfold toL
    exact (Polynomial.natDegree_map_eq_of_injective
      (Polynomial.map_injective A.subtype fun _ _ hab => Subtype.ext hab) Q).symm
  have hQGdeg : (Q.map θ).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    refine le_antisymm (Polynomial.natDegree_map_le.trans hQnat.le) ?_
    rw [← hresdeg, ← hQGres]
    exact Polynomial.natDegree_map_le
  have hlc : R₀.residue (Q.map θ).leadingCoeff ≠ 0 := by
    have h1 : (toRes A Q).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
    have hnd : ((Q.map θ).map R₀.residue).natDegree = (Q.map θ).natDegree := by rw [hQGres, hresdeg, hQGdeg]
    rw [← hQGres, Polynomial.leadingCoeff, hnd, Polynomial.coeff_map] at h1
    exact h1
  obtain ⟨u, hu⟩ := R₀.isUnit_of_residue_ne_zero hlc
  have hu0 : ((u⁻¹ : (R₀.integers)ˣ) : R₀.integers) ≠ 0 := Units.ne_zero _

  have hhom : (algebraMap (RatFunc L) F).comp ((algebraMap R₀.integers (RatFunc L)).comp θ)
      = (Polynomial.aeval f : Polynomial L →ₐ[L] F).toRingHom.comp (Polynomial.mapRingHom A.subtype) :=
    RingHom.ext fun q => by
      show algebraMap (RatFunc L) F (θ q : RatFunc L) = Polynomial.aeval f (q.map A.subtype)
      rw [hθ q, halgp]
  have hQG0 : KD.evG R₀.integers y (Q.map θ) = 0 := by
    rw [KD.evG_apply, Polynomial.map_map, Polynomial.aeval_def, Polynomial.eval₂_map, hhom]
    have h0 := hQ0
    unfold evalFY toL at h0
    rw [Polynomial.eval₂_map] at h0
    exact h0
  have hsetup : KD.Setup R₀.integers R₀.residue y
      (Polynomial.C ((u⁻¹ : (R₀.integers)ˣ) : R₀.integers) * Q.map θ) :=
    { monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; exact Units.inv_mul u)
      natDegree_pos := by
        rw [Polynomial.natDegree_C_mul hu0, hQGdeg, ← hresdeg]
        exact hirr.natDegree_pos
      evG_P := by rw [map_mul, hQG0, mul_zero]
      gen := hgen
      uniq := fun r hdeg => huniq r (by rwa [Polynomial.natDegree_C_mul hu0, hQGdeg] at hdeg)
      irr := by
        rw [Polynomial.map_mul, Polynomial.map_C, hQGres]
        exact (irreducible_isUnit_mul (Polynomial.isUnit_C.mpr ((u⁻¹).isUnit.map R₀.residue))).mpr hirr
      isUnit_of_ne_zero := fun _ hg => R₀.isUnit_of_residue_ne_zero hg
      surj := R₀.residue_surjective }
  exact ⟨R₀, ⟨hX, hXres⟩, _, hsetup,
    by rw [hsetup.monic.natDegree_map, Polynomial.natDegree_C_mul hu0, hQGdeg]⟩

private theorem exists_prolongation_of_setup [Algebra (RatFunc L) F] [IsScalarTower L (RatFunc L) F]
    (A : ValuationSubring L) (f : F) {y : F} (n : ℕ)
    (ι : RatFunc L →ₐ[L] F) (halg : ∀ r : RatFunc L, algebraMap (RatFunc L) F r = ι r)
    (hXf : algebraMap (RatFunc L) F RatFunc.X = f)
    (R₀ : AlgebraicCurve.RegularProlongation A (RatFunc L) (RatFunc (IsLocalRing.ResidueField A)))
    (hX : (RatFunc.X : RatFunc L) ∈ R₀.integers) (hXres : R₀.residue ⟨RatFunc.X, hX⟩ = RatFunc.X)
    {P : Polynomial R₀.integers} (hsetup : KD.Setup R₀.integers R₀.residue y P)
    (hdeg : (P.map R₀.residue).natDegree = n) :
    ∃ (Fb : Type v) (_ : Field Fb) (_ : Algebra (IsLocalRing.ResidueField A) Fb)
      (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
      Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) ∧
      Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
        = n := by
  classical
  haveI hfact := Fact.mk hsetup.irr
  have hmemK : ∀ r : RatFunc L, algebraMap (RatFunc L) F r ∈ KD.V hsetup ↔ r ∈ R₀.integers :=
    KD.algebraMap_mem_V_iff hsetup
  have hmemL : ∀ x : L, algebraMap L F x ∈ KD.V hsetup ↔ x ∈ A := fun x => by
    rw [IsScalarTower.algebraMap_apply L (RatFunc L) F x, hmemK, R₀.algebraMap_mem_iff]
  have hfV : f ∈ KD.V hsetup := by
    have h1 := (hmemK RatFunc.X).mpr hX
    rwa [hXf] at h1
  obtain ⟨ψA, hψA⟩ : ∃ ψA : A →+* KD.V hsetup, ∀ a : A, (ψA a : F) = algebraMap L F a :=
    ⟨((algebraMap L F).comp A.subtype).codRestrict (KD.V hsetup) (fun a => (hmemL a).mpr a.2), fun _ => rfl⟩
  haveI hψA_local : IsLocalHom ψA := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨w, hw⟩ := ha.exists_right_inv
    have hwF : (ψA a : F) * (w : F) = 1 := congrArg Subtype.val hw
    rw [hψA] at hwF
    have ha0 : (a : L) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at hwF
      exact zero_ne_one hwF
    have hwmem : algebraMap L F (a : L)⁻¹ ∈ KD.V hsetup := by
      rw [map_inv₀, inv_eq_of_mul_eq_one_right hwF]
      exact w.2
    exact isUnit_of_mul_eq_one' a ⟨(a : L)⁻¹, (hmemL _).mp hwmem⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
  have hfconst : (⟨f, hfV⟩ : KD.V hsetup) = KD.constV hsetup ⟨RatFunc.X, hX⟩ := by
    apply Subtype.ext
    rw [KD.coe_constV]
    exact hXf.symm
  have hψA_const : ∀ a : A, ψA a = KD.constV hsetup
      ⟨algebraMap L (RatFunc L) a, (R₀.algebraMap_mem_iff a).mpr a.2⟩ := by
    intro a
    apply Subtype.ext
    rw [hψA, KD.coe_constV, IsScalarTower.algebraMap_apply L (RatFunc L) F]
  letI algFb : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (KD.V hsetup)) :=
    (IsLocalRing.ResidueField.map ψA).toAlgebra
  have hcomm : ∀ c : IsLocalRing.ResidueField A,
      KD.resEquiv hsetup (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (KD.V hsetup)) c)
        = algebraMap (IsLocalRing.ResidueField A) _ c := by
    intro c
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c
    rw [← ha, RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue, hψA_const,
      KD.resEquiv_residue_constV, R₀.residue_algebraMap a]
    rfl
  have hv : KD.resEquiv hsetup (IsLocalRing.residue _ (⟨f, hfV⟩ : KD.V hsetup))
      = algebraMap (RatFunc (IsLocalRing.ResidueField A)) _ RatFunc.X := by
    rw [hfconst, KD.resEquiv_residue_constV, hXres]
  have hconc := KD.conclusions (algk := algFb) hsetup hcomm ⟨f, hfV⟩ hv
  obtain ⟨htr, hfin₀⟩ := hconc
  have hfin : Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({IsLocalRing.residue _ (⟨f, hfV⟩ : KD.V hsetup)} : Set (IsLocalRing.ResidueField (KD.V hsetup))))
      (IsLocalRing.ResidueField (KD.V hsetup)) = n :=
    hfin₀.trans hdeg
  refine ⟨IsLocalRing.ResidueField (KD.V hsetup), inferInstance, algFb,
    { integers := KD.V hsetup
      residue := IsLocalRing.residue _
      algebraMap_mem_iff := hmemL
      residue_surjective := IsLocalRing.residue_surjective
      ker_residue := IsLocalRing.ker_residue
      residue_algebraMap := fun a => by
        rw [RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue]
        congr 1
        exact Subtype.ext (hψA a).symm
      exists_smul_mem := fun z hz => by
        obtain ⟨c, v, hc, hv, hzeq⟩ := KD.exists_eq_algebraMap_mul_unit hsetup z hz
        obtain ⟨a, hac, hres⟩ := R₀.exists_smul_mem c hc
        have hg : IsUnit (⟨a • c, hac⟩ : R₀.integers) := R₀.isUnit_of_residue_ne_zero hres
        have he : ((KD.constV hsetup ⟨a • c, hac⟩ * v : KD.V hsetup) : F) = a • z := by
          show (KD.constV hsetup ⟨a • c, hac⟩ : F) * (v : F) = a • z
          rw [hzeq, KD.coe_constV]
          show algebraMap (RatFunc L) F (a • c) * (v : F) = a • (algebraMap (RatFunc L) F c * (v : F))
          rw [halg, halg, map_smul, smul_mul_assoc]
        refine ⟨a, he ▸ (KD.constV hsetup ⟨a • c, hac⟩ * v).2, ?_⟩
        have hel : (⟨a • z, he ▸ (KD.constV hsetup ⟨a • c, hac⟩ * v).2⟩ : KD.V hsetup)
            = KD.constV hsetup ⟨a • c, hac⟩ * v := Subtype.ext he.symm
        rw [hel]
        exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr ((hg.map (KD.constV hsetup)).mul hv) },
    hfV, htr, hfin⟩

end Steps

private theorem exists_regularProlongation_of_irreducible_toRes
    {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
    (A : ValuationSubring L) (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (y : F)
    (hy : IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F)) ({y} : Set F) = ⊤)
    (Q : Polynomial (Polynomial A))
    (hQ0 : evalFY f y (toL A Q) = 0)
    (hQdeg : (toL A Q).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hirr : Irreducible (toRes A Q))
    (hresdeg : (toRes A Q).natDegree = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (Fb : Type v) (_ : Field Fb) (_ : Algebra (IsLocalRing.ResidueField A) Fb)
      (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
      Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) ∧
      Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
        = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  obtain ⟨ι, hι_alg, hιX, hgen, huniq⟩ := exists_embedding f hf y hy
  letI : Algebra (RatFunc L) F := ι.toRingHom.toAlgebra
  haveI : IsScalarTower L (RatFunc L) F := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  have halg : ∀ r : RatFunc L, algebraMap (RatFunc L) F r = ι r := fun _ => rfl
  obtain ⟨R₀, ⟨hX, hXres⟩, P, hsetup, hdeg⟩ := exists_setup A f y (fun p => (halg _).trans (hι_alg p))
    (fun z => (hgen z).imp fun r hr => (Polynomial.aeval_def y r).trans hr)
    (fun r hr h0 => huniq r hr ((Polynomial.aeval_def y r).symm.trans h0)) Q hQ0 hQdeg hirr hresdeg
  exact exists_prolongation_of_setup A f _ ι halg ((halg _).trans hιX) R₀ hX hXres hsetup hdeg

end PlaneRelationReduction

end

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∃ (Fb : Type v) (_ : Field Fb) (_ : Algebra (IsLocalRing.ResidueField A) Fb)
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) ∧
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F ∧
          ∀ (Fb' : Type v) [Field Fb'] [Algebra (IsLocalRing.ResidueField A) Fb']
            (R' : AlgebraicCurve.RegularProlongation A F Fb') (hfR' : f ∈ R'.integers),
            Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨f, hfR'⟩) →
              R'.integers = R.integers := by
  obtain ⟨y, hy⟩ := Field.exists_primitive_element (IntermediateField.adjoin L ({f} : Set F)) F
  obtain ⟨S, hS, hP1⟩ := PlaneRelationReduction.exists_finset_forall_exists_irreducible_toRes f hf y hy
  refine ⟨S, hS, fun A hA => ?_⟩
  obtain ⟨Q, hQ0, hQdeg, hirr, hresdeg⟩ := hP1 A hA
  obtain ⟨Fb, instFb, instAlg, R, hfR, htr, hdeg⟩ :=
    PlaneRelationReduction.exists_regularProlongation_of_irreducible_toRes A f hf y hy Q hQ0 hQdeg hirr hresdeg
  refine ⟨Fb, instFb, instAlg, R, hfR, htr, hdeg, ?_⟩
  intro Fb' _ _ R' hfR' htr'
  have hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb := by
    rw [hdeg]; exact Module.finrank_pos
  exact AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨f, hfR⟩ htr hfin hdeg.symm
    R'.integers fun e he =>
      AlgebraicCurve.RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue A R' R f hfR' hfR
        htr' htr e he

#print axioms solution

end S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed (solution)
