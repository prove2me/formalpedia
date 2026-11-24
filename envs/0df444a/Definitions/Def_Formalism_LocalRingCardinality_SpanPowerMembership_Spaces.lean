-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:07:59.033056+00:00
-- url     : https://prove2.me/theorems/cea3f420-c1b7-4e24-a78b-01f68fc2d185
-- title:
--   Spaces
-- statement:
--   Definitions and structural lemmas for Spaces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_E_hermDual
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_stdform_sig_one
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
open NumberField
open scoped TensorProduct
open IsDedekindDomain
section Diag
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def sgn {A : Type} [Ring A] (b : Bool) : A := if b then -1 else 1
theorem star_sgn (b : Bool) : star (sgn b : E) = sgn b := by
  cases b <;> simp [sgn]
theorem sgn_mul_self {A : Type} [Ring A] (b : Bool) : (sgn b : A) * sgn b = 1 := by
  cases b <;> simp [sgn]
theorem sgn_ne_zero {A : Type} [Ring A] [Nontrivial A] (b : Bool) : (sgn b : A) ≠ 0 := by
  cases b <;> simp [sgn]
theorem map_sgn {A B : Type} [Ring A] [Ring B] (f : A →+* B) (b : Bool) : f (sgn b) = sgn b := by
  cases b <;> simp [sgn]
def diagForm (N : ℕ) (neg : Fin N → Bool) : (Fin N → E) →ₗ⋆[E] (Fin N → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E)
    (fun x y => ∑ i, star (x i) * sgn (neg i) * y i)
    (by intro m₁ m₂ n; simp [add_mul, Finset.sum_add_distrib])
    (by intro c m n; simp only [Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [starRingEnd_apply]; ring)
    (by intro m n₁ n₂; simp [mul_add, Finset.sum_add_distrib])
    (by intro c m n; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring)
theorem diagForm_apply (N : ℕ) (neg : Fin N → Bool) (x y : Fin N → E) :
    diagForm N neg x y = ∑ i, star (x i) * sgn (neg i) * y i := rfl
theorem diagForm_single (N : ℕ) (neg : Fin N → Bool) (i j : Fin N) :
    diagForm N neg (Pi.single i 1) (Pi.single j 1) = if i = j then (sgn (neg i) : E) else 0 := by
  rw [diagForm_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp
theorem diagForm_isSymm (N : ℕ) (neg : Fin N → Bool) : (diagForm (E := E) N neg).IsSymm := by
  constructor
  intro x y
  simp only [diagForm_apply, map_sum, starRingEnd_apply, star_mul', star_star, star_sgn]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem diagForm_nondeg (N : ℕ) (neg : Fin N → Bool) : (diagForm (E := E) N neg).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    rw [diagForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (by simp)] at h
    simp only [Pi.single_eq_same, mul_one] at h
    have := (mul_eq_zero.1 h).resolve_right (sgn_ne_zero _)
    simpa using this
  · intro y hy
    funext i
    have h := hy (Pi.single i 1)
    rw [diagForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (by simp)] at h
    simp only [Pi.single_eq_same, star_one, one_mul] at h
    have := (mul_eq_zero.1 h).resolve_left (sgn_ne_zero _)
    simpa using this
end Diag
section Lat
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def stdLat (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin N)))
theorem stdLat_isLattice (N : ℕ) : Submodule.IsLattice E (stdLat (E := E) N) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [stdLat, Submodule.span_span_of_tower]
    exact (Pi.basisFun E (Fin N)).span_eq
theorem star_integral (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (s : 𝓞 E) :
    star (algebraMap (𝓞 E) E s) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨⟨star (s : E), hstar _ s.2⟩, rfl⟩
theorem stdLat_unimod (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (neg : Fin N → Bool) : Formalism.HermitianLatticesTheory.IsUnimodular (diagForm (E := E) N neg) (stdLat N) := by
  have key := (Formalism.E.hermDual (𝓞 E) E (Fin N → E) (Fin N) (diagForm N neg) (Pi.basisFun E (Fin N))
    (IsFractionRing.injective (𝓞 E) E) (star_integral hstar)).2
    (Matrix.diagonal fun i => (sgn (neg i) : 𝓞 E)) (by
      intro i j
      rw [Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single]
      by_cases h : i = j
      · subst h; simp [map_sgn]
      · simp [h]) (by
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun i _ => sgn_ne_zero (neg i))
  exact key.2.2 (by
    rw [Matrix.det_diagonal]
    refine isUnit_iff_exists_inv.2 ⟨∏ i, (sgn (neg i) : 𝓞 E), ?_⟩
    rw [← Finset.prod_mul_distrib]
    simp [sgn_mul_self])
end Lat
section Space
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def stdSpace (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (neg : Fin N → Bool)
    (p q : ℕ) : HSpace E where
  V := Fin N → E
  hT := diagForm N neg
  herm := diagForm_isSymm N neg
  nondeg := diagForm_nondeg N neg
  rank := N
  rank_eq := Module.finrank_fin_fun E
  frame := Pi.basisFun E (Fin N)
  sig := fun _ => (p, q)
  L0 := stdLat N
  standardTuple_isLattice := stdLat_isLattice N
  baseLattice_isUnimodular := stdLat_unimod hstar N neg
variable (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
theorem stdSpace_gram_apply (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) (i j : Fin N) :
    (stdSpace hstar N neg p q).gram i j = if i = j then (sgn (neg i) : E) else 0 := by
  show diagForm N neg ((Pi.basisFun E (Fin N)) i) ((Pi.basisFun E (Fin N)) j) = _
  simp only [Pi.basisFun_apply]
  exact diagForm_single N neg i j
def posSpace (N : ℕ) : HSpace E := stdSpace hstar N (fun _ => false) N 0
theorem posSpace_sigOK (N : ℕ) : (posSpace hstar N).SigOK := by
  intro τ
  have hg : (posSpace hstar N).gram.map τ = 1 := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (stdSpace_gram_apply hstar N (fun _ => false) N 0 i j)).trans ?_
    change τ (if i = j then (sgn false : E) else 0) = if i = j then (1 : ℂ) else 0
    by_cases h : i = j <;> simp [h, sgn]
  rw [hg]
  show Formalism.UG.HasSignature _ N 0
  have h := Formalism.UG.P.stdform_sig_one (n := Fin N)
  rw [Fintype.card_fin] at h
  exact h
def negLast : Fin (8 + 1) → Bool := fun i => decide ((i : ℕ) = 8)
theorem negLast_castAdd (i : Fin 8) : negLast (Fin.castAdd 1 i) = false := by
  simp only [negLast, decide_eq_false_iff_not, Fin.val_castAdd]
  exact i.isLt.ne
theorem castAdd_ne_natAdd' (i : Fin 8) (j : Fin 1) : Fin.castAdd 1 i ≠ Fin.natAdd 8 j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega
theorem negLast_natAdd (i : Fin 1) : negLast (Fin.natAdd 8 i) = true := by
  fin_cases i; rfl
theorem lorentzDiagonal_hasSignature : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin (8 + 1) => (sgn (negLast i) : ℂ)) 8 1 := by
  refine ⟨(finSumFinEquiv (m := 8) (n := 1)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
      Matrix.one_apply, negLast_castAdd, (Fin.castAdd_injective 8 1).eq_iff]
    simp [sgn]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (castAdd_ne_natAdd' i j)]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (castAdd_ne_natAdd' j i).symm]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.neg_apply, Matrix.one_apply, negLast_natAdd, (Fin.natAdd_injective 1 8).eq_iff]
    split_ifs <;> simp [sgn]
def lorentzSpace : HSpace E := stdSpace hstar (8 + 1) negLast 8 1
theorem lorentzSpace_signature_ok : (lorentzSpace hstar).SigOK := by
  intro τ
  have hg : (lorentzSpace hstar).gram.map τ = Matrix.diagonal fun i : Fin (8 + 1) => (sgn (negLast i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (stdSpace_gram_apply hstar (8 + 1) negLast 8 1 i j)).trans ?_
    change τ (if i = j then (sgn (negLast i) : E) else 0) = if i = j then (sgn (negLast i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, map_sgn]
  rw [hg]
  exact lorentzDiagonal_hasSignature
end Space
section Maps
variable {E : Type} [Field E] [NumberField E] [StarRing E]
theorem diagForm_single_left (N : ℕ) (neg : Fin N → Bool) (j : Fin N) (b : E) (x : Fin N → E) :
    diagForm N neg (Pi.single j b) x = star b * sgn (neg j) * x j := by
  rw [diagForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp
theorem diagForm_single_right (N : ℕ) (neg : Fin N → Bool) (x : Fin N → E) (j : Fin N) (b : E) :
    diagForm N neg x (Pi.single j b) = star (x j) * sgn (neg j) * b := by
  rw [diagForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp
def extZero (n : ℕ) : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) where
  toFun x := fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp
theorem extZero_castSucc (n : ℕ) (x : Fin n → E) (i : Fin n) : extZero n x (Fin.castSucc i) = x i := by
  simp [extZero]
theorem extZero_last (n : ℕ) (x : Fin n → E) : extZero n x (Fin.last n) = 0 := by
  simp [extZero]
theorem extZero_isom (n : ℕ) (neg : Fin n → Bool) (neg' : Fin (n + 1) → Bool)
    (hneg : ∀ i, neg' (Fin.castSucc i) = neg i) (x y : Fin n → E) :
    diagForm (n + 1) neg' (extZero n x) (extZero n y) = diagForm n neg x y := by
  rw [diagForm_apply, diagForm_apply, Fin.sum_univ_castSucc]
  simp [extZero_castSucc, extZero_last, hneg]
end Maps
section Examples₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)
def toyX (j : ℕ) : HSpace E := posSpace hstar (R0.N j)
def exampleTargetSpace : ℕ → HSpace E
  | 0 => lorentzSpace hstar
  | j + 1 => posSpace hstar (R0.rankY (j + 1))
def toyW : ℕ → HSpace E
  | 1 => lorentzSpace hstar
  | _ => posSpace hstar R0.r
def exampleSpaceMap : ∀ j, (toyX hstar j).V →ₗ[E] (exampleTargetSpace hstar j).V
  | 0 => extZero 8
  | 1 => LinearMap.id
  | _ + 2 => 0
end Examples₂
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [StarRing E]
theorem definite_last_vector_anisotropic : diagForm (E := E) (39 + 1) (fun _ => false) (Pi.single (Fin.last 39) 1)
    (Pi.single (Fin.last 39) 1) ≠ 0 := by
  rw [diagForm_single_left]
  simp [sgn]
theorem definite_extension_orthogonal_last (x : Fin 39 → E) :
    diagForm (39 + 1) (fun _ => false) (extZero 39 x) (Pi.single (Fin.last 39) 1) = 0 := by
  rw [diagForm_single_right, extZero_last]
  simp
theorem lorentz_last_vector_norm (T : ℕ) (pz : E) (hpz : star pz * pz = T) :
    diagForm (8 + 1) negLast (Pi.single (Fin.last 8) pz) (Pi.single (Fin.last 8) pz) = -(T : E) := by
  rw [diagForm_single_left]
  have hn : negLast (Fin.last 8) = true := rfl
  simp only [Pi.single_eq_same, hn, sgn, if_true]
  rw [← hpz]
  ring
theorem lorentz_extension_orthogonal_last (pz : E) (x : Fin 8 → E) :
    diagForm (8 + 1) negLast (extZero 8 x) (Pi.single (Fin.last 8) pz) = 0 := by
  rw [diagForm_single_right, extZero_last]
  simp
theorem standardLattice_orthogonal : Formalism.HermitianLatticesTheory.IsOrthoLattice (diagForm (E := E) 24 (fun _ => false)) (stdLat 24) 24 := by
  refine ⟨Pi.basisFun E (Fin 24), (Pi.basisFun E (Fin 24)).linearIndependent,
    (Pi.basisFun E (Fin 24)).span_eq, rfl, fun i j => ?_⟩
  rw [Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single]
  simp [sgn]
end SlopeTestRemainingChoices
section Adelic
theorem cT_diagonal {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (σ : A →+* A)
    (d : n → A) : Formalism.UG.cT σ (Matrix.diagonal d) = Matrix.diagonal (fun i => σ (d i)) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]
def diagUnit {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (d d' : n → A)
    (h : ∀ i, d i * d' i = 1) : GL n A where
  val := Matrix.diagonal d
  inv := Matrix.diagonal d'
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    exact h _
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    rw [mul_comm]
    exact h _
theorem diagUnit_val {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (d d' : n → A)
    (h : ∀ i, d i * d' i = 1) : (diagUnit d d' h : Matrix n n A) = Matrix.diagonal d := rfl
end Adelic
section Examples₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)
include hy in
theorem example_baseSpace_isometric_graded : ∀ j, 1 ≤ j → j ≤ R0.m → ∃ e : Fin (exampleTargetSpace hstar 0).rank ≃ Fin (toyW hstar j).rank,
    ∃ g : GL (Fin (toyW hstar j).rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      Formalism.UG.cT (Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F))
                (g : Matrix (Fin (toyW hstar j).rank) (Fin (toyW hstar j).rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
        (((exampleTargetSpace hstar 0).gram.reindex e e).map (Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F))) *
        (g : Matrix (Fin (toyW hstar j).rank) (Fin (toyW hstar j).rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (toyW hstar j).gram.map (Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F)) := by
  intro j h1 h2
  have hm : R0.m = 2 := rfl
  obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
  · refine ⟨Equiv.refl _, 1, ?_⟩
    simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  · obtain ⟨y, hy⟩ := hy
    set A := FiniteAdeleRing (𝓞 F) F
    set σ := Formalism.UG.sigR cm.sig A
    have hyu : y * (-(σ y)) = 1 := by rw [mul_neg, mul_comm, hy, neg_neg]
    refine ⟨Equiv.refl _, diagUnit (n := Fin (toyW hstar 2).rank)
      (fun i => if (i : ℕ) = 8 then y else 1) (fun i => if (i : ℕ) = 8 then -(σ y) else 1)
      (fun i => by split_ifs <;> simp [hyu]), ?_⟩
    ext i j
    rw [diagUnit_val, cT_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.map_apply]
    refine (congrArg (fun z => σ (if (i : ℕ) = 8 then y else 1) * Formalism.UG.inclE A z *
      (if (j : ℕ) = 8 then y else 1)) (stdSpace_gram_apply hstar (8 + 1) negLast 8 1 i j)).trans ?_
    have e2 : (toyW hstar 2).gram i j = if i = j then (sgn false : E) else 0 :=
      stdSpace_gram_apply hstar R0.r (fun _ => false) R0.r 0 i j
    rw [e2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos (show @Eq (Fin (8 + 1)) i i from rfl), if_pos rfl]
      by_cases hi : (i : ℕ) = 8
      · have hn : negLast i = true := by simp [negLast, hi]
        rw [hn]
        simp only [if_pos hi, sgn, if_true, Bool.false_eq_true, if_false, map_neg, map_one]
        rw [mul_neg_one, neg_mul, hy, neg_neg]
      · have hn : negLast i = false := by simp [negLast, hi]
        rw [hn]
        simp [hi, sgn]
    · rw [if_neg (show ¬ @Eq (Fin (8 + 1)) i j from hij), if_neg hij]
      simp
end Examples₂
section Examples₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)
def spacesExample : Spaces R0 F E where
  cm := cm
  T := T
  T_prime := hT
  X := toyX hstar
  X_sig := fun j => posSpace_sigOK hstar _
  X_rank := fun _ _ => rfl
  X_def := fun _ _ _ => Or.inl rfl
  X' := posSpace hstar 39
  X'_sig := posSpace_sigOK hstar 39
  X'_rank := rfl
  iX' := extZero 39
  iX'_isom := fun x y => extZero_isom 39 (fun _ => false) (fun _ => false) (fun _ => rfl) x y
  z := Pi.single (Fin.last 39) 1
  z_anis := definite_last_vector_anisotropic
  z_orth := fun x => definite_extension_orthogonal_last x
  Y := exampleTargetSpace hstar
  Y_sig := fun j => match j with
    | 0 => lorentzSpace_signature_ok hstar
    | _ + 1 => posSpace_sigOK hstar _
  Y_rank := fun j _ => match j with
    | 0 => rfl
    | _ + 1 => rfl
  iXY := exampleSpaceMap hstar
  iXY_isom := fun j hj => match j, hj with
    | 0, _ => fun x y => extZero_isom 8 (fun _ => false) negLast (fun i => negLast_castAdd i) x y
    | 1, _ => fun _ _ => rfl
    | _ + 2, h => absurd h (by have : R0.m = 2 := rfl; omega)
  eYm := LinearEquiv.refl E (Fin 39 → E)
  eYm_isom := fun _ _ => rfl
  zm := Pi.single (Fin.last 8) pz
  zm_norm := lorentz_last_vector_norm T pz hpz
  zm_orth := fun x => lorentz_extension_orthogonal_last pz x
  hypE := fun _ => 0
  hypF := fun _ => 0
  hyp_ee := fun _ _ => by simp
  hyp_ff := fun _ _ => by simp
  hyp_ef := fun i _ => absurd i.isLt (by simp)
  hyp_orthX := fun _ _ => ⟨by simp, by simp⟩
  hyp_orthz := fun _ => ⟨by simp, by simp⟩
  baseSpace_signature_eq := fun _ => rfl
  W := toyW hstar
  W_sig := fun j => match j with
    | 0 => posSpace_sigOK hstar _
    | 1 => lorentzSpace_signature_ok hstar
    | _ + 2 => posSpace_sigOK hstar _
  W_rank := fun j h1 h2 => by
    have : R0.m = 2 := rfl
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · rfl
    · rfl
  W_sigval := fun j h1 h2 τ => by
    have : R0.m = 2 := rfl
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · rfl
    · rfl
  baseSpace_isometric_graded := example_baseSpace_isometric_graded hstar cm hy
  V := fun _ => posSpace hstar R0.nV
  V_sig := fun _ => posSpace_sigOK hstar _
  V_rank := fun _ _ _ => rfl
  Vneg := fun _ => false
  V_std := fun _ _ _ => standardLattice_orthogonal
end Examples₂
end Formalism.BasicNotions.Examples₂


