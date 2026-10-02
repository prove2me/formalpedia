-- Prove2me | Definitions.Def_Yukon_6063c44a017b9098f88bc52e
-- name    : Yukon_6063c44a017b9098f88bc52e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:40:36.191239+00:00
-- url     : https://prove2.me/theorems/91b86db2-c7b7-4bb7-9ad9-8e9c28abfca8
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeChar6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeChar6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeChar6812.lean
--
--   yukon-proof-operation:foundation-direct-6103348e7433ca8a21db1397191aeaf8b0de49086e1c1aa14dccea07833b18e2
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZTk3YTY0OGM5ODlkYjRhNTM5Y2M1MGZlYzA0ODZiMjk2M2MwYmY2NzZhZmUyMDIyOWQzN2U2ZjJmNDIwNWI5ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTYxMDMzNDhlNzQzM2NhOGEyMWRiMTM5NzE5MWFlYWY4YjBkZTQ5MDg2ZTFjMWFhMTRkY2NlYTA3ODMzYjE4ZTIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl82MDYzYzQ0YTAxN2I5MDk4Zjg4YmM1MmUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_88acd699d7b2611ef3b71a58

import Definitions.Def_Yukon_1a73be96c34fef79c5d93dc9

import Mathlib.Algebra.MvPolynomial.Funext



























































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge: pole and zero orders on a slice component are below the characteristic

On a slice component `D ∋ F, t - ℓ` the slice form `t - ℓ` is irreducible and does not divide
the surface (`t` is transcendental over `Ω`), so `original_finite_separable_finrank_bound`
bounds every transcendental coordinate's degree by `2N` (`N` the total `(Y,Y',Γ)`-degree of
`F`).  Hence every coordinate pole is `≤ 2N`, and
`zero_ν H ≤ Σ pole H ≤ N·Σ_j deg y_j ≤ 6N²`.
-/

namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero MvPolynomial
open RCN002 RCN005 RCN006 RCN095 RCN135 RCN136 RCN202 RCN204 RCN208 RCN313 RCN341
noncomputable section
set_option autoImplicit false

section SliceForm
variable {Ω E : Type} [Field Ω] [Field E] [Algebra Ω E] [Algebra (RatFunc Ω) E]

/-- The slice form `t - Σ c_m Y_m` over `E`. -/
abbrev sliceForm (c : Fin 3 → Ω) : MvPolynomial (Fin 3) E :=
  C (sliceValue Ω E) - scalarPolynomialMap Ω E (∑ m, C (c m) * MvPolynomial.X m)

theorem sliceForm_eq (c : Fin 3 → Ω) :
    sliceForm (E := E) c =
      C (sliceValue Ω E) - ∑ m, C (algebraMap Ω E (c m)) * MvPolynomial.X m := by
  simp [scalarPolynomialMap]

theorem sliceForm_coeff (c : Fin 3 → Ω) (i : Fin 3) (hci : c i = 1) :
    (sliceForm (E := E) c).coeff (Finsupp.single i 1) = -1 := by
  classical
  rw [sliceForm_eq, coeff_sub, coeff_C, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm,
    coeff_sum]
  simp [coeff_C_mul, coeff_X, Finsupp.single_left_inj one_ne_zero, Finset.sum_ite_eq', hci]

theorem sliceForm_totalDegree (c : Fin 3 → Ω) (i : Fin 3) (hci : c i = 1) :
    (sliceForm (E := E) c).totalDegree = 1 := by
  apply le_antisymm
  · rw [sliceForm_eq]
    refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])
  · have h := le_totalDegree (p := sliceForm (E := E) c) (s := Finsupp.single i 1)
      (by rw [MvPolynomial.mem_support_iff, sliceForm_coeff c i hci]
          exact neg_ne_zero.mpr one_ne_zero)
    simpa using h

public theorem isUnit_of_totalDegree_zero {a : MvPolynomial (Fin 3) E} (ha : a ≠ 0)
    (h : a.totalDegree = 0) : IsUnit a := by
  rw [totalDegree_eq_zero_iff_eq_C] at h
  rw [h] at ha ⊢
  exact (isUnit_iff_ne_zero.mpr fun h0 => ha (by rw [h0, map_zero])).map C

theorem sliceForm_irreducible (c : Fin 3 → Ω) (i : Fin 3) (hci : c i = 1) :
    Irreducible (sliceForm (E := E) c) := by
  have hd := sliceForm_totalDegree (E := E) c i hci
  have hne : sliceForm (E := E) c ≠ 0 := fun h => by rw [h] at hd; simp at hd
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · obtain ⟨q, hq⟩ := hu.exists_right_inv
    have h1 := congrArg totalDegree hq
    rw [totalDegree_mul_of_isDomain hne (right_ne_zero_of_mul_eq_one hq), totalDegree_one,
      hd] at h1
    omega
  · have ha : a ≠ 0 := by rintro rfl; exact hne (by rw [hab, zero_mul])
    have hb : b ≠ 0 := by rintro rfl; exact hne (by rw [hab, mul_zero])
    have h1 := congrArg totalDegree hab
    rw [totalDegree_mul_of_isDomain ha hb, hd] at h1
    rcases Nat.eq_zero_or_pos a.totalDegree with h | h
    · exact Or.inl (isUnit_of_totalDegree_zero ha h)
    · exact Or.inr (isUnit_of_totalDegree_zero hb (by omega))

/-- `t` is transcendental over `Ω`, so the slice form divides no nonzero polynomial over `Ω`. -/
theorem sliceForm_not_dvd [IsScalarTower Ω (RatFunc Ω) E] [Infinite Ω] (c : Fin 3 → Ω)
    (i : Fin 3) (hci : c i = 1)
    (A : MvPolynomial (Fin 3) Ω) (hA : A ≠ 0) :
    ¬ sliceForm (E := E) c ∣ scalarPolynomialMap Ω E A := by
  classical
  rintro ⟨Q, hQ⟩
  apply hA
  apply MvPolynomial.funext
  intro ω
  rw [map_zero]
  set s := ∑ m, c m * ω m
  let f : Fin 3 → Polynomial Ω := fun m =>
    Polynomial.C (ω m) + if m = i then Polynomial.X - Polynomial.C s else 0
  have hP : aeval f A = 0 := by
    apply transcendental_iff_injective.mp (sliceValue_transcendental (Ω := Ω) (E := E))
    rw [map_zero, ← AlgHom.comp_apply, comp_aeval]
    have hev : aeval (fun m => Polynomial.aeval (sliceValue Ω E) (f m)) A =
        eval (fun m => Polynomial.aeval (sliceValue Ω E) (f m)) (scalarPolynomialMap Ω E A) := by
      rw [scalarPolynomialMap, eval_map, aeval_def]
    rw [hev, hQ, eval_mul]
    apply mul_eq_zero_of_left
    rw [sliceForm_eq]
    simp only [f, map_sub, map_sum, map_mul, eval_C, eval_X, map_add, Polynomial.aeval_C,
      apply_ite (Polynomial.aeval (sliceValue Ω E)), Polynomial.aeval_X, map_zero, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      hci, map_one, one_mul, s]
    ring
  have h := congrArg (Polynomial.aeval s) hP
  rw [← AlgHom.comp_apply, comp_aeval, map_zero] at h
  have hf : (fun m => Polynomial.aeval s (f m)) = ω := by
    funext m
    by_cases hm : m = i <;> simp [f, hm]
  rw [hf] at h
  exact h

end SliceForm

section Gate
variable {E : Type} [Field E]

/-- `original_finite_separable_finrank_bound` at a literal coordinate `j`. -/
theorem coordinate_gate (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime] (j : Fin 3)
    (hj : Transcendental E (coordinate E P j)) (p : ℕ) [CharP E p]
    (G H : MvPolynomial (Fin 3) E) (hG : Irreducible G) (hGP : G ∈ P) (hHP : H ∈ P)
    (hGH : ¬ G ∣ H) (hdeg : ∀ k, G.degreeOf k < p)
    (hmix : RCN001.coordinateMixedDegree E G H j < p) :
    letI := rationalBaseAlgebra E P j hj
    FiniteDimensional (RatFunc E) (CoordinateField E P) ∧
      Algebra.IsSeparable (RatFunc E) (CoordinateField E P) ∧
      Module.finrank (RatFunc E) (CoordinateField E P) ≤
        RCN001.coordinateMixedDegree E G H j := by
  have key : ∀ k (hk : Transcendental E (coordinate E P k)), k = j →
      (letI := rationalBaseAlgebra E P k hk
       FiniteDimensional (RatFunc E) (CoordinateField E P) ∧
        Algebra.IsSeparable (RatFunc E) (CoordinateField E P) ∧
        Module.finrank (RatFunc E) (CoordinateField E P) ≤
        RCN001.coordinateMixedDegree E G H j) →
      (letI := rationalBaseAlgebra E P j hj
       FiniteDimensional (RatFunc E) (CoordinateField E P) ∧
        Algebra.IsSeparable (RatFunc E) (CoordinateField E P) ∧
        Module.finrank (RatFunc E) (CoordinateField E P) ≤
        RCN001.coordinateMixedDegree E G H j) := by
    rintro k hk rfl h; exact h
  have hj' : Transcendental E (coordinate E P ((Equiv.swap 0 j) 0)) := by
    rwa [Equiv.swap_apply_left]
  exact key _ hj' (Equiv.swap_apply_left 0 j)
    (RCN004.original_finite_separable_finrank_bound E (Equiv.swap 0 j) P hj' p G H hG hGP hHP hGH
      (hdeg _) (hdeg _) hmix)

end Gate

section Char
variable {K : Type} [Field K] {E : Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

/-- A total `(Y,Y',Γ)`-degree bound puts the surface image in the flag `⟨0,0,N⟩`. -/
theorem inFlag_total {L : Type} [Field L] (φ : Polynomial K →+* L) (P : MvPolynomial (Fin 4) K)
    (N : ℕ) (h : MvPolynomial.weightedTotalDegree ![0,1,1,1] P ≤ N) :
    PolynomialInFlag ⟨0,0,N⟩ (surfaceMap φ P) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset φ P he)
  have ht := (MvPolynomial.le_weightedTotalDegree ![0,1,1,1] hd).trans h
  simp [RCN081.weight_fin4] at ht
  simp only [InFlag, Finsupp.tail_apply, show Fin.succ (0 : Fin 3) = 1 from rfl,
    show Fin.succ (1 : Fin 3) = 2 from rfl, show Fin.succ (2 : Fin 3) = 3 from rfl]
  omega

/-- **hchar.** On a slice component of a surface of total `(Y,Y',Γ)`-degree `≤ N ≤ 9678`, every
coordinate pole is `≤ 2N` and every zero of `H` is `≤ 6N²`, both below the characteristic. -/
theorem hchar_holds [CharP K 2130706433] (F : MvPolynomial (Fin 4) K)
    (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hFD : surfaceMap (phiE K E) F ∈ D) (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F ≤ N) (hN9 : N ≤ 9678) :
    ∀ ν : RCN026.Place E (CoordinateField E D), ∀ n : ℕ, 0 < n →
      (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0 := by
  classical
  haveI : CharP E 2130706433 :=
    charP_of_injective_algebraMap (algebraMap (GenericField K) E).injective 2130706433
  set L := CoordinateField E D
  set y := coordinate E D
  set Fp := surfaceMap (phiE K E) F with hFp
  have hF : F ≠ 0 := by rintro rfl; apply hHD; simp [polyH]
  have hFflag : PolynomialInFlag ⟨0,0,N⟩ Fp := inFlag_total _ F N hN
  have hHflag : PolynomialInFlag ⟨0,0,N⟩ (surfaceMap (phiE K E) (polyH K F)) :=
    inFlag_total _ _ N ((RCN234.wt_polyH_le _ F N hN).trans (Nat.sub_le _ _))
  have hirr := sliceForm_irreducible (E := E) c i hci
  have hdvd : ¬ sliceForm (E := E) c ∣ Fp := by
    rw [hFp, surfaceMap_generic_eq]
    exact sliceForm_not_dvd c i hci _ (surfaceMap_ne_zero _ (polynomialEmbedding_injective K) F hF)
  have hdeg1 : ∀ k, (sliceForm (E := E) c).degreeOf k ≤ 1 := fun k =>
    (degreeOf_le_totalDegree _ k).trans (sliceForm_totalDegree c i hci).le
  have hdegF : ∀ k, Fp.degreeOf k ≤ N := fun k => by
    simpa using RCN084.degreeOf_le_flag_total Fp _ hFflag k
  -- every coordinate has at most `2N` poles
  have hpole : ∀ j (W : Finset (RCN026.Place E L)),
      (∑ ν ∈ W, RCN187.poleOrder ν.val (y j)) ≤ 2 * N := by
    intro j W
    have hmix : RCN001.coordinateMixedDegree E (sliceForm c) Fp j ≤ 2 * N :=
      (Nat.add_le_add (Nat.mul_le_mul (hdegF _) (hdeg1 _))
        (Nat.mul_le_mul (hdeg1 _) (hdegF _))).trans (by omega)
    have gate := fun hx : Transcendental E (y j) => coordinate_gate D j hx 2130706433 _ _ hirr
      hslice hFD hdvd (fun k => by have := hdeg1 k; omega) (by omega)
    have h := RCN344.finite_sum_coordinate_pole_le_degree E L
      (RCN042.coordinateOfGate (y j) (fun hx => ⟨(gate hx).1, (gate hx).2.1⟩)) W
    rw [RCN042.coordinateOfGate_value] at h
    refine h.trans ?_
    by_cases hx : Transcendental E (y j)
    · rw [RCN042.coordinateOfGate_degree_of_transcendental _ _ hx]
      exact_mod_cast (gate hx).2.2.trans hmix
    · rw [RCN042.coordinateOfGate_degree_of_isAlgebraic _ _ (not_not.mp hx)]
      positivity
  have hp (j) (ν : RCN026.Place E L) : RCN187.poleOrder ν.val (y j) ≤ 2 * N := by
    simpa using hpole j {ν}
  -- zeros of `H` are bounded by its poles
  set Hev := SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)
  have hHne : Hev ≠ 0 := fun h => hHD ((SecondJetComponentRoots.evaluation_zero_iff D _).mp h)
  letI := polynomialBaseAlgebra E D sep.index
  letI := rationalBaseAlgebra E D sep.index sep.transcendental
  letI := polynomialBaseScalarTower E D sep.index
  letI := polynomialRationalScalarTower E D sep.index sep.transcendental
  letI := rationalBaseScalarTower E D sep.index sep.transcendental
  letI : FiniteDimensional (RatFunc E) L := sep.finite
  letI : Algebra.IsSeparable (RatFunc E) L := sep.separable
  set Pl := RCN026.placesFor E L Hev hHne
  have hpoleH (μ : RCN026.Place E L) : RCN346.poleOrder E L μ Hev ≤
      N * (RCN187.poleOrder μ.val (y 0) + RCN187.poleOrder μ.val (y 1) +
        RCN187.poleOrder μ.val (y 2)) := by
    have h0 : 0 ≤ RCN187.poleOrder μ.val (y 0) := le_max_left _ _
    have h1 : 0 ≤ RCN187.poleOrder μ.val (y 1) := le_max_left _ _
    have h2 : 0 ≤ RCN187.poleOrder μ.val (y 2) := le_max_left _ _
    have hle : flagPole μ.val y ⟨0,0,N⟩ ≤ N * (RCN187.poleOrder μ.val (y 0) +
        RCN187.poleOrder μ.val (y 1) + RCN187.poleOrder μ.val (y 2)) := by
      simp only [flagPole, Nat.cast_zero, zero_mul, zero_add]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) (max_le (by linarith) (by linarith)))
        (by positivity)
    refine le_trans ?_ hle
    apply ActualFirstCutPole6807.pole_le_of_value_le μ.val _ _ (flagPole_nonneg _ _ _)
    have h := valuation_eval_le_flag μ.val (algebraMap E L)
      (RCN344.constant_value_le_one E L μ) y ⟨0,0,N⟩ _ hHflag
    simpa only [Hev, SecondJetComponentRoots.coefficientMap,
      coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  have hzero (ν : RCN026.Place E L) : RCN026.zeroOrder E L ν Hev ≤ N * (6 * N) := by
    have hsum : RCN026.zeroOrder E L ν Hev ≤ ∑ μ ∈ Pl, RCN026.zeroOrder E L μ Hev := by
      by_cases hν : ν ∈ Pl
      · exact Finset.single_le_sum (fun μ _ => RCN026.zeroOrder_nonneg E L μ Hev) hν
      · have hno : RCN026.order E L ν Hev = 0 := by
          by_contra hne; exact hν (RCN026.placesFor_covers E L Hev hHne ν hne)
        simp only [RCN026.zeroOrder, hno, max_self]
        exact Finset.sum_nonneg fun μ _ => RCN026.zeroOrder_nonneg E L μ Hev
    rw [RCN026.sum_placesFor_zero_eq_pole] at hsum
    refine hsum.trans ((Finset.sum_le_sum fun μ _ => hpoleH μ).trans ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (by linarith [hpole 0 Pl, hpole 1 Pl, hpole 2 Pl])
      (by positivity)
  intro ν n hn hle
  have hf : flagPole ν.val y unitAllFlag ≤ 2 * N := by
    rw [flagPole_unitAll]
    exact max_le (hp 1 ν) (max_le (hp 0 ν) (hp 2 ν))
  have hN9' : (N : ℤ) ≤ 9678 := by exact_mod_cast hN9
  have hlt : (n : ℤ) < 2130706433 := by
    have h1 := le_max_iff.mp hle
    rcases h1 with h1 | h1
    · linarith
    · have := hzero ν; nlinarith
  intro h
  exact absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)

end Char

end
end ProximityPrize.SubmissionLower.HFree6812


