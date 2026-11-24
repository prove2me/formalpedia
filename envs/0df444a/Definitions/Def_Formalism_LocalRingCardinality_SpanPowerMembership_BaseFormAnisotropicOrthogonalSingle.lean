-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BaseFormAnisotropicOrthogonalSingle
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_BaseFormAnisotropicOrthogonalSingle
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:36.05634+00:00
-- url     : https://prove2.me/theorems/b2d1d256-205a-4df0-9b26-f5ae93c83920
-- title:
--   Base Form Anisotropic Orthogonal Single
-- statement:
--   Definitions and structural lemmas for Base Form Anisotropic Orthogonal Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BaseFormAnisotropicOrthogonalSingle.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__diag_congr_3bcbdc2a3fa9
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_e_cd4c86133218
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_f_95382bea84da
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_k_8a59f7856bba
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_m_92f5719d2794
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_n_ddfb24727e1c
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_r_6b0f69a7b59a
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_rankComplement_9cb33f905537
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_t_ec1b9c4ed304
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_vertexCount_b44560ac9584
attribute [local simp] P2M_Formalism_BasicNotions_Examples__exampleRanks_wittIndex_e86ea14fff7c


set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂
open NumberField IsDedekindDomain
open scoped TensorProduct
def negTail (N q : ℕ) : Fin N → Bool := fun i => decide (N - q ≤ (i : ℕ))
theorem negTail_zero (N : ℕ) : negTail N 0 = fun _ => false := by
  funext i
  simp only [negTail, decide_eq_false_iff_not, Nat.sub_zero, not_le]
  exact i.isLt
theorem negTail_false (N q : ℕ) (i : Fin N) (h : (i : ℕ) < N - q) : negTail N q i = false := by
  unfold negTail
  exact decide_eq_false (by omega)
theorem negTail_true (N q : ℕ) (i : Fin N) (h : N - q ≤ (i : ℕ)) : negTail N q i = true := by
  unfold negTail
  exact decide_eq_true h
theorem hasSig_tail (N q : ℕ) (h : q ≤ N) : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin N => (sgn (negTail N q i) : ℂ)) (N - q) q := by
  let e : Fin N ≃ Fin (N - q) ⊕ Fin q :=
    (finCongr (by omega : N = (N - q) + q)).trans finSumFinEquiv.symm
  have hl : ∀ i, ((e.symm (Sum.inl i) : Fin N) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e.symm (Sum.inr i) : Fin N) : ℕ) = N - q + i := fun i => by simp [e]
  refine ⟨e, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply,
    e.symm.injective.eq_iff]
  rcases i with i | i <;> rcases j with j | j
  · have hn : negTail N q (e.symm (Sum.inl i)) = false :=
      negTail_false _ _ _ (by rw [hl]; exact i.isLt)
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₁₁, Matrix.one_apply, Sum.inl.injEq, hn]
    simp [sgn]
  · simp [Formalism.UG.Jpq]
  · simp [Formalism.UG.Jpq]
  · have hn : negTail N q (e.symm (Sum.inr i)) = true :=
      negTail_true _ _ _ (by rw [hr]; omega)
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply,
      Sum.inr.injEq, hn]
    split_ifs <;> simp [sgn]
section Space
variable {E : Type} [Field E] [NumberField E] [StarRing E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
def dSpace (N q : ℕ) : HSpace E := stdSpace hstar N (negTail N q) (N - q) q
theorem dSpace_sigOK (N q : ℕ) (h : q ≤ N) : (dSpace hstar N q).SigOK := by
  intro τ
  have hg : (dSpace hstar N q).gram.map τ =
      Matrix.diagonal fun i : Fin N => (sgn (negTail N q i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (stdSpace_gram_apply hstar N (negTail N q) (N - q) q i j)).trans ?_
    change τ (if i = j then (sgn (negTail N q i) : E) else 0) =
      if i = j then (sgn (negTail N q i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, map_sgn]
  rw [hg]
  exact hasSig_tail N q h
def extLE (a b : ℕ) : (Fin a → E) →ₗ[E] (Fin b → E) where
  toFun x := fun i => if h : (i : ℕ) < a then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp
theorem extLE_of_le (a b : ℕ) (x : Fin a → E) (i : Fin b) (h : a ≤ (i : ℕ)) : extLE a b x i = 0 := by
  simp only [extLE, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (by omega)]
theorem extLE_isom (a b : ℕ) (hab : a ≤ b) (neg : Fin a → Bool) (neg' : Fin b → Bool)
    (hneg : ∀ i : Fin a, neg' ⟨i, lt_of_lt_of_le i.isLt hab⟩ = neg i) (x y : Fin a → E) :
    diagForm b neg' (extLE a b x) (extLE a b y) = diagForm a neg x y := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [diagForm_apply, diagForm_apply, Fin.sum_univ_add]
  have h2 : ∀ i : Fin c, star (extLE a (a + c) x (Fin.natAdd a i)) * sgn (neg' (Fin.natAdd a i)) *
      extLE a (a + c) y (Fin.natAdd a i) = 0 := fun i => by
    rw [extLE_of_le a (a + c) y _ (by simp)]; simp
  rw [Finset.sum_eq_zero (fun i _ => h2 i), add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : ∀ z : Fin a → E, extLE a (a + c) z (Fin.castAdd c i) = z i := fun z => by
    simp [extLE]
  rw [h3, h3]
  congr 3
  exact hneg i
theorem z_anis_le (a b : ℕ) (h : a < b) :
    diagForm (E := E) b (fun _ => false) (Pi.single ⟨a, h⟩ 1) (Pi.single ⟨a, h⟩ 1) ≠ 0 := by
  rw [diagForm_single_left]
  simp [sgn]
theorem z_orth_le (a b : ℕ) (h : a < b) (x : Fin a → E) :
    diagForm b (fun _ => false) (extLE a b x) (Pi.single ⟨a, h⟩ 1) = 0 := by
  rw [diagForm_single_right, extLE_of_le a b x ⟨a, h⟩ (le_refl a)]
  simp
end Space
section Congr
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (cm : CMData F E)
theorem dSpace_gram_map (N p : ℕ) :
    (dSpace hstar N p).gram.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) =
      Matrix.diagonal fun i : Fin N => (sgn (negTail N p i) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) := by
  ext i j
  rw [Matrix.map_apply]
  refine (congrArg (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
    (stdSpace_gram_apply hstar N (negTail N p) (N - p) p i j)).trans ?_
  change Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (if i = j then (sgn (negTail N p i) : E) else 0) =
    if i = j then (sgn (negTail N p i) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) else 0
  by_cases h : i = j <;> simp [h, map_sgn]
theorem dSpace_congr (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1) (N N' q q' : ℕ) (hN : N = N') :
    ∃ e : Fin (dSpace hstar N q).rank ≃ Fin (dSpace hstar N' q').rank,
    ∃ g : GL (Fin (dSpace hstar N' q').rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      Formalism.UG.cT (Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F))
                (g : Matrix (Fin (dSpace hstar N' q').rank) (Fin (dSpace hstar N' q').rank)
                  (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
        (((dSpace hstar N q).gram.reindex e e).map (Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F))) *
        (g : Matrix (Fin (dSpace hstar N' q').rank) (Fin (dSpace hstar N' q').rank)
            (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (dSpace hstar N' q').gram.map (Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F)) := by
  subst hN
  obtain ⟨y, hy⟩ := hy
  have hyu : y * (-(Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y)) = 1 := by
    rw [mul_neg, mul_comm, hy, neg_neg]
  refine ⟨Equiv.refl _, diagUnit (n := Fin N)
    (fun i => if negTail N q i = negTail N q' i then 1 else y)
    (fun i => if negTail N q i = negTail N q' i then 1
      else -(Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y))
    (fun i => by split_ifs <;> simp [hyu]), ?_⟩
  have key : Formalism.UG.cT (Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F))
      (Matrix.diagonal (fun i : Fin N => if negTail N q i = negTail N q' i then 1 else y)) *
      Matrix.diagonal (fun i : Fin N => (sgn (negTail N q i) : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
      Matrix.diagonal (fun i : Fin N => if negTail N q i = negTail N q' i then 1 else y) =
      Matrix.diagonal (fun i : Fin N => (sgn (negTail N q' i) : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    refine diag_congr _ _ _ _ (fun i => ?_)
    by_cases h : negTail N q i = negTail N q' i
    · simp [h]
    · simp only [if_neg h]
      have h' : (sgn (negTail N q' i) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = - sgn (negTail N q i) := by
        cases h1 : negTail N q i <;> cases h2 : negTail N q' i <;> simp_all [sgn]
      rw [h', mul_right_comm, hy]
      ring
  refine Eq.trans ?_ (key.trans (dSpace_gram_map (F := F) hstar N q').symm)
  rw [← dSpace_gram_map (F := F) hstar N q]
  rfl
end Congr
theorem half_rank_eq_witt_index_succ (R : Ranks) : (R.m - 0) / 2 = R.rS + 1 := by
  have := R.two_le_m
  unfold Ranks.rS
  omega
theorem baseSpaceRank_eq_sum (R : Ranks) : R.rankY 0 = R.k + R.rS + (R.rS + 1) := by
  obtain ⟨a, ha⟩ := R.m_even
  have := R.two_le_m
  unfold Ranks.rankY Ranks.r Ranks.rS
  omega
theorem baseSpaceRank_eq_r (R : Ranks) : R.rankY 0 = R.r := by simp [Ranks.rankY]
theorem baseRank_eq_k (R : Ranks) : R.N 0 = R.k := by simp [Ranks.N]
theorem rk_Xm (R : Ranks) : R.N R.m = R.rankX' + 1 := by
  have h : R.m * (R.t + 1) = R.m * R.t + R.m := Nat.mul_succ _ _
  have := R.two_le_m
  unfold Ranks.N Ranks.rankX' Ranks.r
  omega
theorem rk_XY (R : Ranks) (j : ℕ) (hj : j < R.m) : R.N j ≤ R.rankY j - (R.m - j) / 2 := by
  have h : j * (R.t + 1) = j * R.t + j := Nat.mul_succ _ _
  unfold Ranks.N Ranks.rankY Ranks.r
  omega
theorem rk_qY (R : Ranks) (j : ℕ) : (R.m - j) / 2 ≤ R.rankY j := by
  have := R.m_add_three_le_k
  unfold Ranks.rankY Ranks.r
  omega
section Sp
variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)
def ixP (i : Fin R.rS) : Fin (R.rankY 0) := ⟨R.k + i, by have := baseSpaceRank_eq_sum R; have := i.isLt; omega⟩
def ixN (i : Fin R.rS) : Fin (R.rankY 0) :=
  ⟨R.k + R.rS + 1 + i, by have := baseSpaceRank_eq_sum R; have := i.isLt; omega⟩
def ixZ : Fin (R.rankY 0) := ⟨R.k + R.rS, by have := baseSpaceRank_eq_sum R; omega⟩
theorem neg_ixP (i : Fin R.rS) : negTail (R.rankY 0) ((R.m - 0) / 2) (ixP R i) = false :=
  negTail_false _ _ _ (by
    show R.k + (i : ℕ) < _
    have := baseSpaceRank_eq_sum R; have := half_rank_eq_witt_index_succ R; have := i.isLt; omega)
theorem neg_ixN (i : Fin R.rS) : negTail (R.rankY 0) ((R.m - 0) / 2) (ixN R i) = true :=
  negTail_true _ _ _ (by
    show _ ≤ R.k + R.rS + 1 + (i : ℕ)
    have := baseSpaceRank_eq_sum R; have := half_rank_eq_witt_index_succ R; omega)
theorem neg_ixZ : negTail (R.rankY 0) ((R.m - 0) / 2) (ixZ R) = true :=
  negTail_true _ _ _ (by
    show _ ≤ R.k + R.rS
    have := baseSpaceRank_eq_sum R; have := half_rank_eq_witt_index_succ R; omega)
abbrev f0 : (Fin (R.rankY 0) → E) →ₗ⋆[E] (Fin (R.rankY 0) → E) →ₗ[E] E :=
  diagForm (R.rankY 0) (negTail (R.rankY 0) ((R.m - 0) / 2))
theorem baseForm_positive_positive_pairing (i i' : Fin R.rS) : f0 (E := E) R (Pi.single (ixP R i) 1) (Pi.single (ixP R i') 1) =
    if i = i' then 1 else 0 := by
  rw [diagForm_single, neg_ixP]
  have : ixP R i = ixP R i' ↔ i = i' := by simp [ixP, Fin.ext_iff]
  simp [this, sgn]
theorem baseForm_negative_negative_pairing (i i' : Fin R.rS) : f0 (E := E) R (Pi.single (ixN R i) 1) (Pi.single (ixN R i') 1) =
    if i = i' then -1 else 0 := by
  rw [diagForm_single, neg_ixN]
  have : ixN R i = ixN R i' ↔ i = i' := by simp [ixN, Fin.ext_iff]
  simp [this, sgn]
theorem posIndex_ne_negIndex (i i' : Fin R.rS) : ixP R i ≠ ixN R i' := by
  intro h
  have h' : R.k + (i : ℕ) = R.k + R.rS + 1 + (i' : ℕ) := congrArg Fin.val h
  have := i.isLt
  omega
theorem posIndex_ne_zeroIndex (i : Fin R.rS) : ixP R i ≠ ixZ R := by
  intro h
  have h' : R.k + (i : ℕ) = R.k + R.rS := congrArg Fin.val h
  have := i.isLt
  omega
theorem ixN_ne_ixZ (i : Fin R.rS) : ixN R i ≠ ixZ R := by
  intro h
  have h' : R.k + R.rS + 1 + (i : ℕ) = R.k + R.rS := congrArg Fin.val h
  omega
theorem baseForm_positive_negative_zero (i i' : Fin R.rS) :
    f0 (E := E) R (Pi.single (ixP R i) 1) (Pi.single (ixN R i') 1) = 0 := by
  rw [diagForm_single, if_neg (posIndex_ne_negIndex R i i')]
theorem baseForm_negative_positive_zero (i i' : Fin R.rS) :
    f0 (E := E) R (Pi.single (ixN R i) 1) (Pi.single (ixP R i') 1) = 0 := by
  rw [diagForm_single, if_neg (posIndex_ne_negIndex R i' i).symm]
def hypEv (i : Fin R.rS) : Fin (R.rankY 0) → E := Pi.single (ixP R i) 1 + Pi.single (ixN R i) 1
def hypFv (i : Fin R.rS) : Fin (R.rankY 0) → E :=
  (2 : E)⁻¹ • (Pi.single (ixP R i) 1 - Pi.single (ixN R i) 1)
theorem hyperbolic_basis_basis_zero (i i' : Fin R.rS) : f0 (E := E) R (hypEv R i) (hypEv R i') = 0 := by
  simp only [hypEv, map_add, LinearMap.add_apply, baseForm_positive_positive_pairing, baseForm_negative_negative_pairing, baseForm_positive_negative_zero, baseForm_negative_positive_zero]
  split_ifs <;> simp
theorem hyperbolic_dual_dual_zero (i i' : Fin R.rS) : f0 (E := E) R (hypFv R i) (hypFv R i') = 0 := by
  simp only [hypFv, map_smulₛₗ, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, baseForm_positive_positive_pairing, baseForm_negative_negative_pairing,
    baseForm_positive_negative_zero, baseForm_negative_positive_zero]
  split_ifs <;> simp
theorem hyperbolic_basis_dual_pairing (i i' : Fin R.rS) :
    f0 (E := E) R (hypEv R i) (hypFv R i') = if i = i' then 1 else 0 := by
  simp only [hypEv, hypFv, map_smulₛₗ, map_add, LinearMap.add_apply, map_sub, baseForm_positive_positive_pairing, baseForm_negative_negative_pairing,
    baseForm_positive_negative_zero, baseForm_negative_positive_zero, RingHom.id_apply, smul_eq_mul]
  split_ifs
  · norm_num
  · simp
theorem baseForm_extension_orthogonal_single (x : Fin (R.N 0) → E) (j : Fin (R.rankY 0)) (hj : R.k ≤ (j : ℕ)) (b : E) :
    f0 R (extLE (R.N 0) (R.rankY 0) x) (Pi.single j b) = 0 := by
  rw [diagForm_single_right, extLE_of_le _ _ _ _ (by rw [baseRank_eq_k]; exact hj)]
  simp
theorem baseForm_anisotropic_orthogonal_single (j : Fin (R.rankY 0)) (hj : j ≠ ixZ R) (b : E) :
    f0 R (Pi.single (ixZ R) pz) (Pi.single j b) = 0 := by
  rw [diagForm_single_right, Pi.single_eq_of_ne hj]
  simp
theorem hyperbolic_orthogonal_extension (i : Fin R.rS) (x : Fin (R.N 0) → E) :
    f0 R (extLE (R.N 0) (R.rankY 0) x) (hypEv R i) = 0 ∧
      f0 R (extLE (R.N 0) (R.rankY 0) x) (hypFv R i) = 0 := by
  have h1 := baseForm_extension_orthogonal_single R x (ixP R i) (Nat.le_add_right _ _) 1
  have h2 := baseForm_extension_orthogonal_single R x (ixN R i) (by show R.k ≤ R.k + R.rS + 1 + (i : ℕ); omega) 1
  constructor
  · simp only [hypEv, map_add, h1, h2, add_zero]
  · simp only [hypFv, map_smul, map_sub, h1, h2, sub_zero, smul_zero]
theorem hyperbolic_orthogonal_anisotropic (i : Fin R.rS) :
    f0 R (Pi.single (ixZ R) pz) (hypEv R i) = 0 ∧ f0 R (Pi.single (ixZ R) pz) (hypFv R i) = 0 := by
  have h1 := baseForm_anisotropic_orthogonal_single R pz (ixP R i) (posIndex_ne_zeroIndex R i) 1
  have h2 := baseForm_anisotropic_orthogonal_single R pz (ixN R i) (ixN_ne_ixZ R i) 1
  constructor
  · simp only [hypEv, map_add, h1, h2, add_zero]
  · simp only [hypFv, map_smul, map_sub, h1, h2, sub_zero, smul_zero]
include hpz in
theorem anisotropic_vector_norm_eq_neg : f0 R (Pi.single (ixZ R) pz) (Pi.single (ixZ R) pz) = -(T : E) := by
  rw [diagForm_single_left, neg_ixZ]
  simp only [Pi.single_eq_same, sgn, if_true]
  rw [← hpz]
  ring
def spacesOfRanks : Spaces R F E where
  cm := cm
  T := T
  T_prime := hT
  X := fun j => posSpace hstar (R.N j)
  X_sig := fun j => posSpace_sigOK hstar _
  X_rank := fun _ _ => rfl
  X_def := fun _ _ _ => Or.inl rfl
  X' := posSpace hstar R.rankX'
  X'_sig := posSpace_sigOK hstar _
  X'_rank := rfl
  iX' := extLE R.rankX' (R.N R.m)
  iX'_isom := fun x y => extLE_isom _ _ (by rw [rk_Xm]; omega) _ _ (fun _ => rfl) x y
  z := Pi.single ⟨R.rankX', by rw [rk_Xm]; omega⟩ 1
  z_anis := z_anis_le _ _ _
  z_orth := fun x => z_orth_le _ _ _ x
  Y := fun j => dSpace hstar (R.rankY j) ((R.m - j) / 2)
  Y_sig := fun j => dSpace_sigOK hstar _ _ (rk_qY R j)
  Y_rank := fun _ _ => rfl
  iXY := fun j => extLE (R.N j) (R.rankY j)
  iXY_isom := fun j hj x y => extLE_isom _ _ ((rk_XY R j hj).trans (Nat.sub_le _ _)) _ _
    (fun i => negTail_false _ _ _ (lt_of_lt_of_le i.isLt (rk_XY R j hj))) x y
  eYm := LinearEquiv.refl E (Fin R.rankX' → E)
  eYm_isom := fun x y => by
    show diagForm (R.rankY R.m) (negTail (R.rankY R.m) ((R.m - R.m) / 2)) x y =
      diagForm (R.rankY R.m) (fun _ => false) x y
    rw [Nat.sub_self, Nat.zero_div, negTail_zero]
  zm := Pi.single (ixZ R) pz
  zm_norm := anisotropic_vector_norm_eq_neg R T pz hpz
  zm_orth := fun x => baseForm_extension_orthogonal_single R x _ (Nat.le_add_right _ _) _
  hypE := hypEv R
  hypF := hypFv R
  hyp_ee := hyperbolic_basis_basis_zero R
  hyp_ff := hyperbolic_dual_dual_zero R
  hyp_ef := hyperbolic_basis_dual_pairing R
  hyp_orthX := hyperbolic_orthogonal_extension R
  hyp_orthz := hyperbolic_orthogonal_anisotropic R pz
  baseSpace_signature_eq := fun _ => by
    show ((R.rankY 0 - (R.m - 0) / 2, (R.m - 0) / 2) : ℕ × ℕ) = (R.k + R.rS, R.rS + 1)
    have h1 := baseSpaceRank_eq_sum R
    have h2 := half_rank_eq_witt_index_succ R
    rw [h1, h2]
    exact Prod.ext (by simp) rfl
  W := fun j => dSpace hstar R.r (R.m - j)
  W_sig := fun j => dSpace_sigOK hstar _ _ (by
    have := R.m_add_three_le_k
    unfold Ranks.r; omega)
  W_rank := fun _ _ _ => rfl
  W_sigval := fun j h1 h2 τ => by
    show ((R.r - (R.m - j), R.m - j) : ℕ × ℕ) = (R.k + j - 1, R.m - j)
    exact Prod.ext (by show R.r - (R.m - j) = R.k + j - 1; unfold Ranks.r; omega) rfl
  baseSpace_isometric_graded := fun j _ _ => dSpace_congr hstar cm hy (R.rankY 0) R.r ((R.m - 0) / 2) (R.m - j) (baseSpaceRank_eq_r R)
  V := fun _ => posSpace hstar R.nV
  V_sig := fun _ => posSpace_sigOK hstar _
  V_rank := fun _ _ _ => rfl
  Vneg := fun _ => false
  V_std := fun _ _ _ => by
    refine ⟨Pi.basisFun E (Fin R.nV), (Pi.basisFun E (Fin R.nV)).linearIndependent,
      (Pi.basisFun E (Fin R.nV)).span_eq, rfl, fun i j => ?_⟩
    show diagForm _ _ _ _ = _
    rw [Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single]
    simp [sgn]
end Sp
end Formalism.BasicNotions.Examples₂


