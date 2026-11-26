-- Prove2me | Definitions.Def_TunnellMap_OrderedGenerator
-- name    : TunnellMap_OrderedGenerator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:49:02.02873+00:00
-- url     : https://prove2.me/theorems/20a30d4c-76a0-5fb6-9337-16031346df6d
-- title:
--   Ordered Generator
-- statement:
--   Definitions and structural lemmas for Ordered Generator, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Theorems.Thm_P2M_TunnellMap_OrthogonalFrame_e__orthogonal_6c82c70f8b3a
import Theorems.Thm_P2M_TunnellMap_OrthogonalFrame_e__orthogonal_756a68c1a1d3
import Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_e__z_b28283f150ec
import Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_z_e__4b2fa73c6dcf
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_OrthogonalFrame_affine_norm_root_certificate
import Theorems.Thm_TunnellMap_OrthogonalFrame_det_eq_one
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_eq_iff
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


set_option autoImplicit true
namespace TunnellMap
structure GeneratorIndex where
  A : ℤ
  q : ℤ
  b : ℤ
  u : ℤ
deriving DecidableEq
namespace OrderedGenerator
variable {n : ℤ} {p : Triple}
def alpha (F : OrthogonalFrame p) : ℤ := dot F.e₁ F.e₁
def beta (F : OrthogonalFrame p) : ℤ := dot F.e₁ F.e₂
def delta (F : OrthogonalFrame p) : ℤ := dot F.z F.e₁
def epsilon (F : OrthogonalFrame p) : ℤ := dot F.z F.e₂
def K (F : OrthogonalFrame p) : ℤ :=
  beta F * delta F - alpha F * epsilon F
def M (n A q : ℤ) : ℤ := A * (n - q ^ 2 * A)
def intOffsetEmbedding (lo : ℤ) : ℕ ↪ ℤ where
  toFun k := lo + k
  inj' := by intro a b h; exact_mod_cast (Int.add_left_cancel h)
def intIcc (lo hi : ℤ) : Finset ℤ :=
  if lo ≤ hi then
    (Finset.range (Int.toNat (hi - lo) + 1)).map (intOffsetEmbedding lo)
  else
    ∅
@[simp] theorem mem_intIcc {lo hi x : ℤ} :
    x ∈ intIcc lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  by_cases hbounds : lo ≤ hi
  · constructor
    · intro hx
      have hxMap : x ∈
          (Finset.range (Int.toNat (hi - lo) + 1)).map
            (intOffsetEmbedding lo) := by
        simpa [intIcc, hbounds] using hx
      obtain ⟨k, hk, hkx⟩ := Finset.mem_map.mp hxMap
      have hklt : k < Int.toNat (hi - lo) + 1 := Finset.mem_range.mp hk
      have hdiff : 0 ≤ hi - lo := sub_nonneg.mpr hbounds
      have hkLeInt : (k : ℤ) ≤ hi - lo := by
        have hkLe : k ≤ Int.toNat (hi - lo) := by omega
        rw [← Int.toNat_of_nonneg hdiff]
        exact_mod_cast hkLe
      have hkx' : lo + (k : ℤ) = x := hkx
      constructor <;> omega
    · rintro ⟨hlo, hhi⟩
      let k : ℕ := Int.toNat (x - lo)
      have hxDiff : 0 ≤ x - lo := sub_nonneg.mpr hlo
      have hiDiff : 0 ≤ hi - lo := sub_nonneg.mpr hbounds
      have hkCast : (k : ℤ) = x - lo := by
        simp [k, Int.toNat_of_nonneg hxDiff]
      have hkLeInt : (k : ℤ) ≤ hi - lo := by omega
      have hkLe : k ≤ Int.toNat (hi - lo) := by
        have hkCastLe : (k : ℤ) ≤ (Int.toNat (hi - lo) : ℤ) := by
          simpa [Int.toNat_of_nonneg hiDiff] using hkLeInt
        exact Int.ofNat_le.mp hkCastLe
      have hkMem : k ∈ Finset.range (Int.toNat (hi - lo) + 1) := by
        simp only [Finset.mem_range]
        omega
      have hmap : x ∈
          (Finset.range (Int.toNat (hi - lo) + 1)).map
            (intOffsetEmbedding lo) := by
        apply Finset.mem_map.mpr
        refine ⟨k, hkMem, ?_⟩
        change lo + (k : ℤ) = x
        omega
      simpa [intIcc, hbounds] using hmap
  · constructor
    · simp [intIcc, hbounds]
    · rintro ⟨hlo, hhi⟩
      exact (hbounds (hlo.trans hhi)).elim
def AValues (n : ℤ) : Finset ℤ := intIcc 1 ((n - 1) / 2)
def qValues (n A : ℤ) : Finset ℤ :=
  (intIcc (-n) n).filter fun q => q ≠ 0 ∧ Odd q ∧ q ^ 2 * A < n
def bLower (n : ℤ) (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  ⌈(((q * A * K F - Int.sqrt (alpha F * M n A q) : ℤ) : ℚ) / (n : ℚ))⌉
def bUpper (n : ℤ) (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  ⌊(((q * A * K F + Int.sqrt (alpha F * M n A q) : ℤ) : ℚ) / (n : ℚ))⌋
def bValues (n : ℤ) (F : OrthogonalFrame p) (A q : ℤ) : Finset ℤ :=
  intIcc (bLower n F A q) (bUpper n F A q)
def rootValues (F : OrthogonalFrame p) (A q b : ℤ) : Finset ℤ :=
  let D := F.halfDiscriminant A q b
  let c := beta F * b + q * A * delta F
  ({Int.sqrt D, -Int.sqrt D} : Finset ℤ).filter fun u =>
    u ^ 2 = D ∧ alpha F ∣ -c + u
def indexEmbedding (A q b : ℤ) : ℤ ↪ GeneratorIndex where
  toFun u := ⟨A, q, b, u⟩
  inj' := by intro u v h; exact congrArg GeneratorIndex.u h
def rawIndices (n : ℤ) (F : OrthogonalFrame p) : Finset GeneratorIndex :=
  (AValues n).biUnion fun A =>
    (qValues n A).biUnion fun q =>
      (bValues n F A q).biUnion fun b =>
        (rootValues F A q b).map (indexEmbedding A q b)
@[simp] theorem mem_rawIndices (n : ℤ) (F : OrthogonalFrame p)
    (i : GeneratorIndex) :
    i ∈ rawIndices n F ↔
      i.A ∈ AValues n ∧ i.q ∈ qValues n i.A ∧
        i.b ∈ bValues n F i.A i.q ∧
          i.u ∈ rootValues F i.A i.q i.b := by
  simp only [rawIndices, Finset.mem_biUnion, Finset.mem_map]
  constructor
  · rintro ⟨A, hA, q, hq, b, hb, u, hu, hui⟩
    have hi : i = ⟨A, q, b, u⟩ := hui.symm
    subst i
    simpa using ⟨hA, hq, hb, hu⟩
  · rintro ⟨hA, hq, hb, hu⟩
    refine ⟨i.A, hA, i.q, hq, i.b, hb, i.u, hu, ?_⟩
    rfl
@[simp] theorem mem_rootValues (F : OrthogonalFrame p) (A q b u : ℤ) :
    u ∈ rootValues F A q b ↔
      (u = Int.sqrt (F.halfDiscriminant A q b) ∨
        u = -Int.sqrt (F.halfDiscriminant A q b)) ∧
      u ^ 2 = F.halfDiscriminant A q b ∧
      alpha F ∣ -(beta F * b + q * A * delta F) + u := by
  simp [rootValues]
def aValue (F : OrthogonalFrame p) (i : GeneratorIndex) : ℤ :=
  (-(beta F * i.b + i.q * i.A * delta F) + i.u) / alpha F
def rValue (F : OrthogonalFrame p) (i : GeneratorIndex) : Triple :=
  linComb3 (aValue F i) i.b (i.q * i.A) F.e₁ F.e₂ F.z
def dValue (F : OrthogonalFrame p) (i : GeneratorIndex) : Triple :=
  tauInv (rValue F i)
def targetValue (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Triple :=
  reconstructedTarget (residualSourceLift s) i.q (dValue F i)
theorem aValue_linear_of_dvd (F : OrthogonalFrame p) (i : GeneratorIndex)
    (hdiv : alpha F ∣ -(beta F * i.b + i.q * i.A * delta F) + i.u) :
    alpha F * aValue F i =
      -(beta F * i.b + i.q * i.A * delta F) + i.u := by
  rw [aValue, mul_comm]
  exact Int.ediv_mul_cancel hdiv
theorem dot_rValue (F : OrthogonalFrame p) (i : GeneratorIndex) :
    dot p (rValue F i) = i.q * i.A := by
  simp only [rValue, linComb3, vadd, vsmul, dot]
  have h₁ := F.e₁_orthogonal
  have h₂ := F.e₂_orthogonal
  have hz := F.bezout
  simp only [dot] at h₁ h₂ hz
  linear_combination (aValue F i) * h₁ + i.b * h₂ + (i.q * i.A) * hz
theorem tau_dValue_of_parity (F : OrthogonalFrame p) (i : GeneratorIndex)
    (hparity : InTauLattice (rValue F i)) :
    tau (dValue F i) = rValue F i := by
  exact tau_tauInv hparity
@[simp] theorem coeff₁_rValue (F : OrthogonalFrame p) (i : GeneratorIndex) :
    F.coeff₁ (rValue F i) = aValue F i := by
  unfold OrthogonalFrame.coeff₁ rValue
  rw [dot_linComb3_cross_e₂_z, F.det_eq_one]
  ring
@[simp] theorem coeff₂_rValue (F : OrthogonalFrame p) (i : GeneratorIndex) :
    F.coeff₂ (rValue F i) = i.b := by
  unfold OrthogonalFrame.coeff₂ rValue
  rw [dot_linComb3_cross_z_e₁, F.det_eq_one]
  ring
theorem affine_norm_of_rawIndex (F : OrthogonalFrame p) {i : GeneratorIndex}
    (hi : i ∈ rawIndices n F) : dot (rValue F i) (rValue F i) = i.A := by
  have hu := (mem_rawIndices n F i).mp hi |>.2.2.2
  have hroot := (mem_rootValues F i.A i.q i.b i.u).mp hu
  rw [rValue, F.affine_norm_root_certificate]
  refine ⟨i.u, hroot.2.1, ?_⟩
  exact aValue_linear_of_dvd F i hroot.2.2
theorem qForm_dValue_of_rawIndex (F : OrthogonalFrame p) {i : GeneratorIndex}
    (hi : i ∈ rawIndices n F) (hparity : InTauLattice (rValue F i)) :
    qForm (dValue F i) = i.A := by
  rw [← qForm_tau, tau_dValue_of_parity F i hparity]
  exact affine_norm_of_rawIndex F hi
theorem bilinear_dValue_of_rawIndex
    (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hparity : InTauLattice (rValue F i)) :
    qBilinear (residualSourceLift s) (dValue F i) = i.q * i.A := by
  calc
    qBilinear (residualSourceLift s) (dValue F i) =
        dot (tau (residualSourceLift s)) (tau (dValue F i)) := by
          simp [qBilinear]
    _ = dot (tau (residualSourceLift s)) (rValue F i) := by
      rw [tau_dValue_of_parity F i hparity]
    _ = i.q * i.A := dot_rValue F i
def PassesFilters (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Prop :=
  InTauLattice (rValue F i) ∧
    tripleContent (dValue F i) = 1 ∧
    FirstNonzeroPositive (dValue F i) ∧
    Odd (dValue F i).z ∧
    ∃ t : AResidual n,
      residualTargetLift t = targetValue s F i ∧
        directionKey (dValue F i) = representativeEdgeKey s t
noncomputable def validIndices (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) : Finset GeneratorIndex := by
  classical
  exact (rawIndices n F).filter (PassesFilters s F)
theorem mem_validIndices_iff (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    i ∈ validIndices s F ↔ i ∈ rawIndices n F ∧ PassesFilters s F i := by
  classical
  simp [validIndices]
noncomputable def targetOfValid (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : AResidual n := by
  have hfilters : PassesFilters s F i.1 :=
    (mem_validIndices_iff s F i.1).mp i.2 |>.2
  exact Classical.choose hfilters.2.2.2.2
theorem validIndex_raw (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : i.1 ∈ rawIndices n F :=
  (mem_validIndices_iff s F i.1).mp i.2 |>.1
theorem validIndex_filters (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : PassesFilters s F i.1 :=
  (mem_validIndices_iff s F i.1).mp i.2 |>.2
theorem validIndex_eq_of_directionKey_eq
    (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i j : {i // i ∈ validIndices s F})
    (hkey : directionKey (dValue F i.1) = directionKey (dValue F j.1)) :
    i = j := by
  have hiRaw := validIndex_raw s F i
  have hjRaw := validIndex_raw s F j
  have hiFilters := validIndex_filters s F i
  have hjFilters := validIndex_filters s F j
  have hdiFix := primitiveDirection_eq_self_of_content_one_of_oriented
    hiFilters.2.1 hiFilters.2.2.1
  have hdjFix := primitiveDirection_eq_self_of_content_one_of_oriented
    hjFilters.2.1 hjFilters.2.2.1
  have hd : dValue F i.1 = dValue F j.1 := by
    have hprimitive := directionKey_eq_iff.mp hkey
    rw [hdiFix, hdjFix] at hprimitive
    exact hprimitive
  have hAi := qForm_dValue_of_rawIndex F hiRaw hiFilters.1
  have hAj := qForm_dValue_of_rawIndex F hjRaw hjFilters.1
  have hA : i.1.A = j.1.A := by
    calc
      i.1.A = qForm (dValue F i.1) := hAi.symm
      _ = qForm (dValue F j.1) := congrArg qForm hd
      _ = j.1.A := hAj
  have hApos : 0 < i.1.A := by
    have hmem := (mem_rawIndices n F i.1).mp hiRaw |>.1
    rw [AValues, mem_intIcc] at hmem
    omega
  have hbi := bilinear_dValue_of_rawIndex s F hiFilters.1
  have hbj := bilinear_dValue_of_rawIndex s F hjFilters.1
  have hqMul : i.1.q * i.1.A = j.1.q * i.1.A := by
    calc
      i.1.q * i.1.A = qBilinear (residualSourceLift s) (dValue F i.1) := hbi.symm
      _ = qBilinear (residualSourceLift s) (dValue F j.1) := congrArg _ hd
      _ = j.1.q * j.1.A := hbj
      _ = j.1.q * i.1.A := by rw [hA]
  have hq : i.1.q = j.1.q :=
    mul_right_cancel₀ (ne_of_gt hApos) hqMul
  have hr : rValue F i.1 = rValue F j.1 := by
    calc
      rValue F i.1 = tau (dValue F i.1) :=
        (tau_dValue_of_parity F i.1 hiFilters.1).symm
      _ = tau (dValue F j.1) := congrArg tau hd
      _ = rValue F j.1 := tau_dValue_of_parity F j.1 hjFilters.1
  have hb : i.1.b = j.1.b := by
    simpa using congrArg F.coeff₂ hr
  have ha : aValue F i.1 = aValue F j.1 := by
    simpa using congrArg F.coeff₁ hr
  have hui := (mem_rootValues F i.1.A i.1.q i.1.b i.1.u).mp
    ((mem_rawIndices n F i.1).mp hiRaw |>.2.2.2)
  have huj := (mem_rootValues F j.1.A j.1.q j.1.b j.1.u).mp
    ((mem_rawIndices n F j.1).mp hjRaw |>.2.2.2)
  have hlinearI := aValue_linear_of_dvd F i.1 hui.2.2
  have hlinearJ := aValue_linear_of_dvd F j.1 huj.2.2
  have hu : i.1.u = j.1.u := by
    rw [hA, hq, hb, ha] at hlinearI
    linarith
  apply Subtype.ext
  cases hi : i.1 with
  | mk Ai qi bi ui =>
      cases hj : j.1 with
      | mk Aj qj bj uj =>
          simp_all
theorem validIndex_key_injective
    (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s))) :
    Function.Injective (fun i : {i // i ∈ validIndices s F} =>
      directionKey (dValue F i.1)) := by
  intro i j h
  exact validIndex_eq_of_directionKey_eq s F i j h
noncomputable def targetOrbitOfValid (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    (aResidualInvolution n hnpos).Orbit :=
  (aResidualInvolution n hnpos).orbit (targetOfValid s F i)
noncomputable def orderedIndexList (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    List {i // i ∈ validIndices s F} :=
  letI : LinearOrder {i // i ∈ validIndices s F} :=
    LinearOrder.lift' (fun i => directionKey (dValue F i.1))
      (validIndex_key_injective s F)
  (validIndices s F).attach.sort (· ≤ ·)
noncomputable def incidentStream (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    List (aResidualInvolution n hnpos).Orbit :=
  (orderedIndexList s F).map (targetOrbitOfValid hnpos s F)
end OrderedGenerator
end TunnellMap


