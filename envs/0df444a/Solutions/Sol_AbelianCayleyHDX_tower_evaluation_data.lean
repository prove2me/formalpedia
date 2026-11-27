-- Prove2me | solution 1 for AbelianCayleyHDX.tower_evaluation_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:27:34.865563+00:00
-- url     : https://prove2.me/submissions/8f40d3a5-446b-444d-a9f9-b07b788ebecc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AbelianCayleyHDX_tower_polynomial_data

namespace AbelianCayleyHDX.P46

open Matrix MvPolynomial Finset

variable {F : Type*} [Field F]

/-- Determinants of matrices whose entries do not involve `X ℓ` do not involve `X ℓ`. -/
lemma degreeOf_det_eq_zero {σ n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial σ F)) (ℓ : σ) (h : ∀ i j, degreeOf ℓ (M i j) = 0) :
    degreeOf ℓ M.det = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [Matrix.det_apply]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ' _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul]
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 : degreeOf ℓ (((Equiv.Perm.sign σ' : ℤ) : MvPolynomial σ F)) = 0 := by
    rw [← map_intCast (C : F →+* MvPolynomial σ F), degreeOf_C]
  rw [h1, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  simp [h]

/-- **Rank-one updates are affine in the new variable.** -/
lemma degreeOf_det_rank_one {σ n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n (MvPolynomial σ F)) (ℓ : σ) (hB : ∀ i j, degreeOf ℓ (B i j) = 0)
    (u v : n → F) :
    degreeOf ℓ (B + (X ℓ : MvPolynomial σ F) • vecMulVec (fun i => C (u i)) (fun i => C (v i))).det
      ≤ 1 := by
  classical
  by_cases hu : u = 0
  · subst hu
    have : vecMulVec (fun i => C ((0 : n → F) i)) (fun i => C (v i)) = (0 : Matrix n n (MvPolynomial σ F)) := by
      ext i j; simp [vecMulVec_apply]
    rw [this, smul_zero, add_zero, degreeOf_det_eq_zero B ℓ hB]; norm_num
  obtain ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  set w0 : n → F := fun i => if i = i0 then 0 else -(u i / u i0)
  set E0 : Matrix n n F := 1 + vecMulVec w0 (Pi.single i0 1)
  set E : Matrix n n (MvPolynomial σ F) := E0.map C
  have hE0 : E0.det = 1 := by
    simp only [E0]
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, single_dotProduct]
    simp [w0]
  have hE : E.det = 1 := by
    have := RingHom.map_det (C : F →+* MvPolynomial σ F) E0
    rw [hE0, map_one, RingHom.mapMatrix_apply] at this
    exact this.symm
  have hE0u : E0 *ᵥ u = Pi.single i0 (u i0) := by
    funext i
    have : (vecMulVec w0 (Pi.single i0 1) *ᵥ u) i = w0 i * u i0 := by
      simp [mulVec, dotProduct, vecMulVec_apply, Pi.single_apply]
    simp only [E0, add_mulVec, one_mulVec, Pi.add_apply, this]
    by_cases hi : i = i0
    · subst hi; simp [w0]
    · simp only [w0, if_neg hi, Pi.single_apply, hi, if_false]
      field_simp; ring
  have hEu : E *ᵥ (fun i => C (u i)) = Pi.single i0 (C (u i0)) := by
    funext i
    have := RingHom.map_mulVec (C : F →+* MvPolynomial σ F) E0 u i
    rw [hE0u] at this
    simp only [E]
    rw [show (fun i => C (u i)) = (C : F →+* MvPolynomial σ F) ∘ u from rfl, ← this]
    by_cases hi : i = i0
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  have hEB : ∀ i j, degreeOf ℓ ((E * B) i j) = 0 := by
    intro i j
    apply Nat.eq_zero_of_le_zero
    simp only [Matrix.mul_apply, E, Matrix.map_apply]
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun r _ => ?_)
    refine (degreeOf_mul_le _ _ _).trans ?_
    rw [hB r j, degreeOf_C]
  have hM : E * (B + (X ℓ : MvPolynomial σ F) • vecMulVec (fun i => C (u i)) (fun i => C (v i))) =
      (E * B).updateRow i0 ((E * B) i0 + (X ℓ * C (u i0)) • fun i => C (v i)) := by
    rw [Matrix.mul_add, Matrix.mul_smul, mul_vecMulVec, hEu]
    ext i j
    by_cases hi : i = i0
    · subst hi
      simp [updateRow_self, vecMulVec_apply, mul_comm, mul_left_comm]
    · simp [updateRow_ne hi, vecMulVec_apply, Pi.single_apply, hi]
  have hdet : (B + (X ℓ : MvPolynomial σ F) • vecMulVec (fun i => C (u i)) (fun i => C (v i))).det =
      (E * B).det + X ℓ * C (u i0) * ((E * B).updateRow i0 (fun i => C (v i))).det := by
    have h1 := congrArg Matrix.det hM
    rw [det_mul, hE, one_mul] at h1
    rw [h1, det_updateRow_add, det_updateRow_smul, updateRow_eq_self]
  rw [hdet]
  refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · rw [degreeOf_det_eq_zero _ ℓ hEB]; norm_num
  · refine (degreeOf_mul_le _ _ _).trans ?_
    have h2 : degreeOf ℓ ((E * B).updateRow i0 (fun i => C (v i))).det = 0 := by
      apply degreeOf_det_eq_zero
      intro i j
      by_cases hi : i = i0
      · subst hi; simp [degreeOf_C]
      · rw [updateRow_ne hi]; exact hEB i j
    rw [h2, add_zero]
    refine (degreeOf_mul_le _ _ _).trans ?_
    rw [degreeOf_C, add_zero]
    exact (degreeOf_X _ _).le.trans (by split_ifs <;> norm_num)

end AbelianCayleyHDX.P46

namespace AbelianCayleyHDX.P46

open Matrix MvPolynomial Finset

variable {F : Type*} [Field F]

/-- A linear form as a polynomial. -/
noncomputable def linPoly {t : ℕ} (ℓ : Module.Dual F (Fin t → F)) : MvPolynomial (Fin t) F :=
  ∑ r : Fin t, C (ℓ (Pi.single r 1)) * X r

lemma dual_apply_eq_sum {t : ℕ} (ℓ : Module.Dual F (Fin t → F)) (x : Fin t → F) :
    ℓ x = ∑ r, x r * ℓ (Pi.single r 1) := by
  have hx : x = ∑ r, x r • (Pi.single r (1 : F) : Fin t → F) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_smul, smul_eq_mul]

lemma eval_linPoly {t : ℕ} (ℓ : Module.Dual F (Fin t → F)) (x : Fin t → F) :
    eval x (linPoly ℓ) = ℓ x := by
  rw [linPoly, dual_apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp [mul_comm]

/-- **Independence as functions** (second half of the proof of Proposition 4.6). If the maximal
minors of a `k × m` matrix of linear forms on `F^t` are linearly independent as polynomials, and the
matrix has rank one at each point of a spanning family, then the minors are linearly independent as
functions `F^t → F`. -/
theorem fun_indep_of_poly_indep {t k m N : ℕ} (L : Fin k → Fin m → Module.Dual F (Fin t → F))
    (e : Fin N → (Fin t → F)) (hspan : Submodule.span F (Set.range e) = ⊤)
    (hrank : ∀ a, ∃ (u : Fin k → F) (z : Fin m → F), ∀ i l, L i l (e a) = u i * z l)
    (hpoly : LinearIndependent F (fun J : {J : Finset (Fin m) // J.card = k} =>
      (Matrix.of fun i l => ∑ r : Fin t,
        MvPolynomial.C (L i (J.1.orderEmbOfFin J.2 l) (Pi.single r 1)) * MvPolynomial.X r).det)) :
    LinearIndependent F (fun J : {J : Finset (Fin m) // J.card = k} =>
      fun x : Fin t → F => (Matrix.of fun i l => L i (J.1.orderEmbOfFin J.2 l) x).det) := by
  classical
  -- a basis of evaluation points
  obtain ⟨κ, a, ha, hspa, hli⟩ := exists_linearIndependent' F e
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hsp : ⊤ ≤ Submodule.span F (Set.range (e ∘ a)) := by rw [hspa, hspan]
  set b := Module.Basis.mk hli hsp with hbdef
  have hb : ∀ ℓ, b ℓ = e (a ℓ) := fun ℓ => by rw [hbdef, Module.Basis.mk_apply]; rfl
  -- the change of variables
  set φ : Fin t → MvPolynomial κ F := fun r => ∑ ℓ : κ, C (b ℓ r) * X ℓ with hφ
  set ψ : κ → MvPolynomial (Fin t) F := fun ℓ => ∑ r : Fin t, C (b.coord ℓ (Pi.single r 1)) * X r
  have hinv : ∀ p : MvPolynomial (Fin t) F, bind₁ ψ (bind₁ φ p) = p := by
    intro p
    rw [bind₁_bind₁]
    have : (fun r => bind₁ ψ (φ r)) = X := by
      funext r
      simp only [hφ, map_sum, map_mul, bind₁_C_right, bind₁_X_right, ψ, Finset.mul_sum]
      rw [Finset.sum_comm]
      have e1 : ∀ r' : Fin t, ∑ ℓ : κ, C (b ℓ r) * (C (b.coord ℓ (Pi.single r' 1)) * X r') =
          C (∑ ℓ : κ, b.coord ℓ (Pi.single r' 1) * b ℓ r) * X r' := by
        intro r'
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        rw [← mul_assoc, ← C_mul, mul_comm (b ℓ r)]
      simp only [e1]
      have e2 : ∀ r' : Fin t, ∑ ℓ : κ, b.coord ℓ (Pi.single r' 1) * b ℓ r =
          (Pi.single r' 1 : Fin t → F) r := by
        intro r'
        have := b.sum_repr (Pi.single r' 1)
        have h2 := congrFun this r
        rw [Finset.sum_apply] at h2
        rw [← h2]
        rfl
      simp only [e2]
      rw [Finset.sum_eq_single r]
      · simp
      · intro r' _ hr'; simp [Pi.single_apply, Ne.symm hr']
      · simp
    rw [this, bind₁_X_left]; rfl
  have hinj : Function.Injective (bind₁ φ : MvPolynomial (Fin t) F →ₐ[F] MvPolynomial κ F) := by
    intro p q h
    rw [← hinv p, ← hinv q, h]
  -- the minors as polynomials
  set P : {J : Finset (Fin m) // J.card = k} → MvPolynomial (Fin t) F := fun J =>
    (Matrix.of fun i l => ∑ r : Fin t,
      MvPolynomial.C (L i (J.1.orderEmbOfFin J.2 l) (Pi.single r 1)) * MvPolynomial.X r).det
    with hPdef
  have hevalP : ∀ J x, eval x (P J) = (Matrix.of fun i l => L i (J.1.orderEmbOfFin J.2 l) x).det := by
    intro J x
    simp only [hPdef]
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i l
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [show (∑ r : Fin t, C (L i (J.1.orderEmbOfFin J.2 l) (Pi.single r 1)) * X r :
        MvPolynomial (Fin t) F) = linPoly (L i (J.1.orderEmbOfFin J.2 l)) from rfl, eval_linPoly]
  -- the minors in the new coordinates
  choose U Z hUZ using fun ℓ : κ => hrank (a ℓ)
  have hentry : ∀ L0 : Module.Dual F (Fin t → F),
      bind₁ φ (∑ r : Fin t, C (L0 (Pi.single r 1)) * X r) = ∑ ℓ : κ, C (L0 (b ℓ)) * X ℓ := by
    intro L0
    rw [map_sum]
    have e1 : ∀ r : Fin t, bind₁ φ (C (L0 (Pi.single r 1)) * X r) =
        ∑ ℓ : κ, C (L0 (Pi.single r 1) * b ℓ r) * X ℓ := by
      intro r
      rw [map_mul, bind₁_C_right, bind₁_X_right, hφ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [C_mul, mul_assoc]
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [← Finset.sum_mul, ← map_sum, dual_apply_eq_sum L0 (b ℓ)]
    congr 2
    refine Finset.sum_congr rfl (fun r _ => by ring)
  have hP' : ∀ J, bind₁ φ (P J) = (Matrix.of fun i l => ∑ ℓ : κ,
      X ℓ * (C (U ℓ i) * C (Z ℓ (J.1.orderEmbOfFin J.2 l)))).det := by
    intro J
    simp only [hPdef]
    rw [AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i l => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hentry]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [hb ℓ, hUZ ℓ i (J.1.orderEmbOfFin J.2 l), C_mul, mul_comm]
  have hdeg : ∀ J (ℓ : κ), degreeOf ℓ (bind₁ φ (P J)) ≤ 1 := by
    intro J ℓ
    rw [hP' J]
    have hsplit : (Matrix.of fun i l => ∑ ℓ' : κ,
        (X ℓ' : MvPolynomial κ F) * (C (U ℓ' i) * C (Z ℓ' (J.1.orderEmbOfFin J.2 l)))) =
        (Matrix.of fun i l => ∑ ℓ' ∈ Finset.univ.erase ℓ,
          (X ℓ' : MvPolynomial κ F) * (C (U ℓ' i) * C (Z ℓ' (J.1.orderEmbOfFin J.2 l)))) +
        (X ℓ : MvPolynomial κ F) • vecMulVec (fun i => C (U ℓ i))
          (fun l => C (Z ℓ (J.1.orderEmbOfFin J.2 l))) := by
      ext i l
      simp only [Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, vecMulVec_apply,
        smul_eq_mul]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ℓ)]
    rw [hsplit]
    apply degreeOf_det_rank_one
    intro i l
    apply Nat.eq_zero_of_le_zero
    simp only [Matrix.of_apply]
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun ℓ' hℓ' => ?_)
    refine (degreeOf_mul_le _ _ _).trans ?_
    rw [degreeOf_X_of_ne (Ne.symm (Finset.ne_of_mem_erase hℓ'))]
    refine (Nat.zero_add _).le.trans ((degreeOf_mul_le _ _ _).trans ?_)
    simp [degreeOf_C]
  -- conclude
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hQ' : bind₁ φ (∑ J, g J • P J) = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ (fun _ => ({0, 1} : Finset F))
    · intro ℓ
      rw [Finset.card_pair zero_ne_one, map_sum]
      have hle : degreeOf ℓ (∑ J, bind₁ φ (g J • P J)) ≤ 1 := by
        refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun J _ => ?_)
        rw [map_smul, smul_eq_C_mul]
        exact (degreeOf_C_mul_le _ _ _).trans (hdeg J ℓ)
      omega
    · intro c _
      have h1 : ∀ p : MvPolynomial (Fin t) F, eval c (bind₁ φ p) =
          eval (fun r => eval c (φ r)) p := by
        intro p
        exact eval₂Hom_bind₁ (RingHom.id F) c φ p
      rw [h1, map_sum]
      have := congrFun hg (fun r => eval c (φ r))
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [smul_eq_C_mul, map_mul, eval_C, hevalP]
  have hQ : ∑ J, g J • P J = 0 := hinj (by rw [hQ', map_zero])
  exact (Fintype.linearIndependent_iff.1 hpoly) g hQ

end AbelianCayleyHDX.P46

open Filter RSListDecodingCapacity.AllRates

open AbelianCayleyHDX in
theorem solution (h : ℕ) (hq : 8 ≤ 2 ^ h) (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (hF : Fintype.card F = (2 ^ h) ^ 2) (g₀ : ℕ) :
    ∃ g : ℕ → ℕ, Tendsto g atTop atTop ∧ (∀ j, g₀ ≤ g j) ∧
    ∃ (e : ∀ j, Fin ((2 ^ h - 2) * g j) → (Fin (2 * g j + 1) → F))
      (L : ∀ j, Fin (g j / 4) → Fin (3 * (g j / 4)) → Module.Dual F (Fin (2 * g j + 1) → F)),
      (∀ j,
        Submodule.span F (Set.range (e j)) = ⊤ ∧
        (∀ a, e j a ≠ 0) ∧
        (∀ a b, a ≠ b → ∀ c : F, e j a ≠ c • e j b) ∧
        (∀ c : Module.Dual F (Fin (2 * g j + 1) → F), c ≠ 0 →
          (Finset.univ.filter fun a => c (e j a) = 0).card ≤ 3 * g j) ∧
        (∀ a, ∃ (u : Fin (g j / 4) → F) (z : Fin (3 * (g j / 4)) → F),
          ∀ i l, L j i l (e j a) = u i * z l) ∧
        LinearIndependent F (fun J : {J : Finset (Fin (3 * (g j / 4))) // J.card = g j / 4} =>
          fun x : Fin (2 * g j + 1) → F =>
            (Matrix.of fun i l => L j i (J.1.orderEmbOfFin J.2 l) x).det)) ∧
      ∀ enc : F ≃ Fin (Fintype.card F), ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∃ p : Polynomial ℕ, ∀ j,
          HMBinPacking.OutputsWithin M (encNat j)
            (encNat (2 * g j + 1) ++ encList (encFVec enc) (List.ofFn (e j)))
            (p.eval (2 * g j + 1)) := by
  obtain ⟨g, hg, hgge, e, L, hprop, hmach⟩ := tower_polynomial_data h hq F hF g₀
  refine ⟨g, hg, hgge, e, L, fun j => ?_, hmach⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hprop j
  exact ⟨h1, h2, h3, h4, h5, AbelianCayleyHDX.P46.fun_indep_of_poly_indep (L j) (e j) h1 h5 h6⟩
