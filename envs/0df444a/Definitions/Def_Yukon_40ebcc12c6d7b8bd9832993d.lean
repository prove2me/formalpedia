-- Prove2me | Definitions.Def_Yukon_40ebcc12c6d7b8bd9832993d
-- name    : Yukon_40ebcc12c6d7b8bd9832993d
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:25:19.813563+00:00
-- url     : https://prove2.me/theorems/7e4ecb5a-81a5-435e-80db-29bfe47d78ff
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreePlace6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreePlace6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreePlace6812.lean
--
--   yukon-proof-operation:foundation-direct-c3c02552190af31c2dc800ba4eae8b1c941efc23ff651698cb62f5b409d1d122
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGU0OTkzZTdmNjNjYWQzN2RhZTYwYzQ1N2QzOTU1OWViMWIyZWJiYTcxOTc4YzBhM2I5MGRmNzg5ZDdjZmQ3YyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWMzYzAyNTUyMTkwYWYzMWMyZGM4MDBiYTRlYWU4YjFjOTQxZWZjMjNmZjY1MTY5OGNiNjJmNWI0MDlkMWQxMjIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl80MGViY2MxMmM2ZDdiOGJkOTgzMjk5M2QiLCJ2IjoyfQ]

import Definitions.Def_Yukon_8a240e81f8649dccddb88225

import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1

import Definitions.Def_Yukon_590a300e51c847902c7c8694

import Definitions.Def_Yukon_5a1990f0b7b832b98b8bcadb





















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge: the per-place bound on `L0`

For a normalized valuation `v` of `L0 = Frac(K[X,Y,Y',γ]/(F₀))` trivial on `K` with `X`
integral, the first cut `τ_m = D^m (Y')` satisfies

  `3 pole_v τ_m ≤ m (4 T_v + 2 h_v) + 3 P_v`,

where `P_v` is the largest pole of `Y, Y', Γ`, `T_v` the moving pole target, and `h_v` the
zero order of `H`.  Affine places (`P_v = 0`) use lemma (c) and the multiplicity theorem;
places at infinity use `infinity_theta`.  `CrudeBound` and `ResiduallySeparable` are
hypotheses (pieces 3 and 4); `hgen` is the two-generator property of the centre (piece 1).
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open WithZero MvPolynomial
open RCN313 RCN055

section Helpers

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Valuation L ℤᵐ⁰)

/-- Pole order (as in `RCN187.poleOrder`). -/
def vpole (x : L) : ℤ := max 0 (v x).log

/-- Zero order (as in `RCN026.zeroOrder`). -/
def vzero (x : L) : ℤ := max 0 (-(v x).log)

theorem vpole_nonneg (x : L) : 0 ≤ vpole v x := le_max_left _ _

theorem vzero_nonneg (x : L) : 0 ≤ vzero v x := le_max_left _ _

omit [Field K] [Algebra K L] in
theorem v_le_exp_vpole (x : L) : v x ≤ exp (vpole v x) := by
  by_cases hx : v x = 0
  · rw [hx]; exact zero_le
  · calc v x = exp (v x).log := (exp_log hx).symm
      _ ≤ exp (vpole v x) := by rw [exp_le_exp]; exact le_max_right _ _

omit [Field K] [Algebra K L] in
theorem vpole_le_iff (x : L) (n : ℤ) (hn : 0 ≤ n) : vpole v x ≤ n ↔ v x ≤ exp n := by
  constructor
  · intro h
    exact (v_le_exp_vpole v x).trans (by rw [exp_le_exp]; exact h)
  · intro h
    by_cases hx : v x = 0
    · simp [vpole, hx, hn]
    · exact max_le hn ((log_le_iff_le_exp hx).2 h)

theorem pole_iterate_of_bound (D : Derivation K L L) (θ : ℤ) (hθ0 : 0 ≤ θ)
    (hθ : ∀ g, v (D g) ≤ exp θ * v g) (m : ℕ) (g : L) :
    vpole v ((⇑D)^[m] g) ≤ vpole v g + m * θ := by
  have hit : ∀ m : ℕ, v ((⇑D)^[m] g) ≤ exp (m * θ) * v g := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      refine (hθ _).trans ?_
      refine (mul_le_mul_right ih _).trans ?_
      rw [← mul_assoc, ← exp_add]; push_cast; ring_nf; exact le_rfl
  exact pole_le_of_le v (m * θ) (mul_nonneg (by positivity) hθ0) g _ (hit m)

theorem integral_iterate (D : Derivation K L L) (hD : ∀ u, v u ≤ 1 → v (D u) ≤ 1)
    (m : ℕ) (g : L) (hg : v g ≤ 1) : v ((⇑D)^[m] g) ≤ 1 := by
  induction m with
  | zero => simpa using hg
  | succ m ih => rw [Function.iterate_succ_apply']; exact hD _ ih

end Helpers

section Slice

variable {K : Type} [Field K] (F F₀ : MvPolynomial (Fin 4) K) [hF₀ : Fact (Irreducible F₀)]
  (hdvd : F₀ ∣ F)
set_option linter.unusedSectionVars false

/-- The coordinates `Y, Y', Γ` in `L0`. -/
noncomputable def sliceCoord (j : Fin 3) : SliceField F₀ := sliceProj F₀ (MvPolynomial.X j.succ)

/-- `σ = G / H` in `L0`. -/
noncomputable def sliceSigma : SliceField F₀ := sliceProj F₀ (polyG K F) / sliceProj F₀ (polyH K F)

theorem sliceProj_C (a : K) : sliceProj F₀ (C a) = algebraMap K (SliceField F₀) a := by
  rw [IsScalarTower.algebraMap_apply K (SliceRing F₀) (SliceField F₀)]
  rfl

theorem sliceDerivation_coord0 (hH : sliceProj F₀ (polyH K F) ≠ 0) :
    sliceDerivation F F₀ hdvd (sliceCoord F₀ 0) = sliceCoord F₀ 1 := by
  rw [sliceCoord, sliceDerivation_proj_eq F F₀ hdvd hH]
  simp [sliceCoord, pderiv_X]

theorem sliceDerivation_coord1 (hH : sliceProj F₀ (polyH K F) ≠ 0) :
    sliceDerivation F F₀ hdvd (sliceCoord F₀ 1) = sliceSigma F F₀ := by
  rw [sliceCoord, sliceDerivation_proj_eq F F₀ hdvd hH]
  simp [sliceSigma, pderiv_X]

theorem sliceDerivation_coord2 (hH : sliceProj F₀ (polyH K F) ≠ 0) :
    sliceDerivation F F₀ hdvd (sliceCoord F₀ 2) = 0 := by
  rw [sliceCoord, sliceDerivation_proj_eq F F₀ hdvd hH]
  simp [pderiv_X]

include hdvd in
theorem sliceProj_H_eq : ∃ F₁ : MvPolynomial (Fin 4) K,
    sliceProj F₀ (polyH K F) = sliceProj F₀ F₁ * sliceProj F₀ (pderiv 2 F₀) := by
  obtain ⟨F₁, rfl⟩ := hdvd
  refine ⟨F₁, ?_⟩
  have h0 : sliceProj F₀ F₀ = 0 := (sliceProj_eq_zero_iff F₀ F₀).2 dvd_rfl
  rw [polyH, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, h0,
    zero_mul, zero_add]

theorem sliceDerivation_X0 (hH : sliceProj F₀ (polyH K F) ≠ 0) :
    sliceDerivation F F₀ hdvd (sliceProj F₀ (MvPolynomial.X 0)) = 1 := by
  rw [sliceDerivation_proj_eq F F₀ hdvd hH]
  simp [pderiv_X]

/-- The slice form in `L0`: `ℓ = Σ q_m(X) · c_m` for the coordinates `c_m = Y, Y', Γ`. -/
noncomputable def sliceLinearL (q : Fin 3 → Polynomial K) : SliceField F₀ :=
  ∑ m, Polynomial.aeval (sliceProj F₀ (MvPolynomial.X 0)) (q m) * sliceCoord F₀ m

variable (v : Valuation (SliceField F₀) ℤᵐ⁰)

theorem v_aeval_le_one (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (p : Polynomial K) :
    v (Polynomial.aeval (sliceProj F₀ (MvPolynomial.X 0)) p) ≤ 1 := by
  haveI : v.IsTrivialOn K := ⟨hK⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact (v.map_add _ _).trans (max_le hp hq)
  | monomial n a =>
    rw [Polynomial.aeval_monomial, v.map_mul, v.map_pow]
    exact mul_le_one' (Valuation.IsTrivialOn.valuation_algebraMap_le_one v a) (pow_le_one' hX0 n)

/-- Largest pole of the coordinates (`flagPole` of `unitAllFlag`). -/
noncomputable def placeP : ℤ :=
  max (vpole v (sliceCoord F₀ 1)) (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2)))

/-- The moving pole target `T` (`movingPoleTarget`). -/
noncomputable def placeT : ℤ :=
  max (2 * placeP F₀ v)
    (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2)) + vpole v (sliceSigma F F₀))

/-- The zero order of `H`. -/
noncomputable def placeH : ℤ := vzero v (sliceProj F₀ (polyH K F))

/-- At an affine place (`P = 0`) every polynomial is integral. -/
theorem place_hint (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (hP0 : placeP F₀ v = 0) :
    ∀ g : MvPolynomial (Fin 4) K, v (sliceProj F₀ g) ≤ 1 := by
  haveI : v.IsTrivialOn K := ⟨hK⟩
  have hcint : ∀ j : Fin 3, v (sliceCoord F₀ j) ≤ 1 := by
    intro j
    have hj : vpole v (sliceCoord F₀ j) ≤ 0 := by
      have h1 := le_max_left (vpole v (sliceCoord F₀ 1))
        (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2)))
      have h2 := le_max_right (vpole v (sliceCoord F₀ 1))
        (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2)))
      have h3 := le_max_left (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))
      have h4 := le_max_right (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))
      have hP : placeP F₀ v = max (vpole v (sliceCoord F₀ 1))
        (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))) := rfl
      fin_cases j
      · show vpole v (sliceCoord F₀ 0) ≤ 0; omega
      · show vpole v (sliceCoord F₀ 1) ≤ 0; omega
      · show vpole v (sliceCoord F₀ 2) ≤ 0; omega
    have := (vpole_le_iff v _ 0 le_rfl).1 hj
    rwa [exp_zero] at this
  intro g
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [sliceProj_C]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v a
  | add p q hp hq => rw [map_add]; exact (v.map_add _ _).trans (max_le hp hq)
  | mul_X p i hp =>
    rw [map_mul, v.map_mul]
    refine mul_le_one' hp ?_
    fin_cases i
    · exact hX0
    · exact hcint 0
    · exact hcint 1
    · exact hcint 2

/-- The derivative of the slice form has pole at most `max (P, pole σ)`. -/
theorem sliceLinearL_bound (hH : sliceProj F₀ (polyH K F) ≠ 0)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (q : Fin 3 → Polynomial K) :
    v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)) ≤
      max (exp (placeP F₀ v)) (v (sliceSigma F F₀)) := by
  set x0 := sliceProj F₀ (MvPolynomial.X 0)
  have hcoord : ∀ j, v (sliceCoord F₀ j) ≤ exp (placeP F₀ v) := by
    intro j
    refine (v_le_exp_vpole v _).trans ?_
    rw [exp_le_exp, placeP]
    fin_cases j
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_max_right _ _)
  have hDa : ∀ p : Polynomial K, sliceDerivation F F₀ hdvd (Polynomial.aeval x0 p) =
      Polynomial.aeval x0 (Polynomial.derivative p) := by
    intro p
    rw [Derivation.map_aeval, sliceDerivation_X0 F F₀ hdvd hH, smul_eq_mul, mul_one]
  rw [sliceLinearL, map_sum]
  refine v.map_sum_le fun m _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDa]
  refine (v.map_add _ _).trans (max_le ?_ ?_)
  · rw [v.map_mul]
    refine (mul_le_of_le_one_left' (v_aeval_le_one F₀ v hK hX0 _)).trans ?_
    fin_cases m
    · show v (sliceDerivation F F₀ hdvd (sliceCoord F₀ 0)) ≤ _
      rw [sliceDerivation_coord0 F F₀ hdvd hH]; exact le_max_of_le_left (hcoord 1)
    · show v (sliceDerivation F F₀ hdvd (sliceCoord F₀ 1)) ≤ _
      rw [sliceDerivation_coord1 F F₀ hdvd hH]; exact le_max_right _ _
    · show v (sliceDerivation F F₀ hdvd (sliceCoord F₀ 2)) ≤ _
      rw [sliceDerivation_coord2 F F₀ hdvd hH, v.map_zero]; exact zero_le
  · rw [v.map_mul]
    exact (mul_le_of_le_one_right' (v_aeval_le_one F₀ v hK hX0 _)).trans
      (le_max_of_le_left (hcoord m))

/-- **Per-place bound on `L0`.** -/
theorem place_bound (hH : sliceProj F₀ (polyH K F) ≠ 0)
    (hnorm : ∃ x, v x = exp (-1))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1)
    (ℓ : SliceField F₀)
    (hℓ : v (sliceDerivation F F₀ hdvd ℓ) ≤ max (exp (placeP F₀ v)) (v (sliceSigma F F₀)))
    (C : ℤ) (hcrude : CrudeBound v (sliceDerivation F F₀ hdvd) C)
    (hsep : ResiduallySeparable v (sliceDerivation F F₀ hdvd)
      (exp (vpole v (sliceDerivation F F₀ hdvd ℓ))))
    (h2 : (2 : K) ≠ 0)
    (hchar : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (placeP F₀ v) (placeH F F₀ v) → (n : K) ≠ 0)
    (hgen : placeP F₀ v = 0 → ∃ a b : MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a) < 1 ∧ v (sliceProj F₀ b) < 1 ∧
      ∀ g, v (sliceProj F₀ g) < 1 → ∃ s x y : MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s) = 1 ∧ s * g = x * a + y * b)
    (m : ℕ) :
    3 * vpole v ((⇑(sliceDerivation F F₀ hdvd))^[m] (sliceCoord F₀ 1)) ≤
      m * (4 * placeT F F₀ v + 2 * placeH F F₀ v) + 3 * placeP F₀ v := by
  classical
  haveI : v.IsTrivialOn K := ⟨hK⟩
  set Dd := sliceDerivation F F₀ hdvd with hDd
  set P := placeP F₀ v with hPdef
  set T := placeT F F₀ v with hTdef
  set h := placeH F F₀ v with hhdef
  set pσ := vpole v (sliceSigma F F₀) with hpσdef
  set s := vpole v (Dd ℓ) with hsdef
  set p0 := vpole v (sliceCoord F₀ 0)
  set p1 := vpole v (sliceCoord F₀ 1)
  set p2 := vpole v (sliceCoord F₀ 2)
  have hp0 : 0 ≤ p0 := vpole_nonneg _ _
  have hp1 : 0 ≤ p1 := vpole_nonneg _ _
  have hp2 : 0 ≤ p2 := vpole_nonneg _ _
  have hPeq : P = max p1 (max p0 p2) := rfl
  have hTeq : T = max (2 * P) (max p0 p2 + pσ) := rfl
  have hP0 : 0 ≤ P := by rw [hPeq]; exact le_max_of_le_left hp1
  have hh0 : 0 ≤ h := vzero_nonneg _ _
  have hpσ0 : 0 ≤ pσ := vpole_nonneg _ _
  have hs0 : 0 ≤ s := vpole_nonneg _ _
  have hTP : 2 * P ≤ T := by rw [hTeq]; exact le_max_left _ _
  have hTσ : pσ ≤ T := by
    rw [hTeq]; exact le_max_of_le_right (by have := le_max_left p0 p2; omega)
  have hsP : s ≤ max P pσ := by
    rw [hsdef, vpole_le_iff _ _ _ (le_max_of_le_left hP0)]
    refine hℓ.trans (max_le ?_ ?_)
    · rw [exp_le_exp]; exact le_max_left _ _
    · exact (v_le_exp_vpole v _).trans (by rw [exp_le_exp]; exact le_max_right _ _)
  obtain ⟨π₀, hπ₀⟩ := hnorm
  have hmθ : ∀ θ : ℤ, 0 ≤ θ → 3 * θ ≤ 4 * T + 2 * h →
      3 * ((m : ℤ) * θ) ≤ m * (4 * T + 2 * h) := by
    intro θ _ hθ
    have := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg (α := ℤ) m)
    linarith
  rcases eq_or_lt_of_le hP0 with hPz | hPpos
  · -- affine places
    have hPz' : P = 0 := hPz.symm
    have hq0 : p0 = 0 := by have := le_max_left p0 p2; have := le_max_right p1 (max p0 p2); omega
    have hq1 : p1 = 0 := by have := le_max_left p1 (max p0 p2); omega
    have hq2 : p2 = 0 := by have := le_max_right p0 p2; have := le_max_right p1 (max p0 p2); omega
    have hcint : ∀ j : Fin 3, v (sliceCoord F₀ j) ≤ 1 := by
      intro j
      have hj : vpole v (sliceCoord F₀ j) ≤ 0 := by
        fin_cases j
        · exact hq0.le
        · exact hq1.le
        · exact hq2.le
      have := (vpole_le_iff v _ 0 le_rfl).1 hj
      rwa [exp_zero] at this
    have hint_all : ∀ g : MvPolynomial (Fin 4) K, v (sliceProj F₀ g) ≤ 1 := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a =>
        rw [sliceProj_C]
        exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v a
      | add p q hp hq => rw [map_add]; exact (v.map_add _ _).trans (max_le hp hq)
      | mul_X p i hp =>
        rw [map_mul, v.map_mul]
        refine mul_le_one' hp ?_
        fin_cases i
        · exact hX0
        · exact hcint 0
        · exact hcint 1
        · exact hcint 2
    have hfrac : ∀ x : SliceField F₀, ∃ f g : MvPolynomial (Fin 4) K,
        sliceProj F₀ g ≠ 0 ∧ x = sliceProj F₀ f / sliceProj F₀ g := by
      intro x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := SliceRing F₀) x
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨f, g, ?_, rfl⟩
      exact (map_ne_zero_iff _ (IsFractionRing.injective (SliceRing F₀) (SliceField F₀))).2
        (nonZeroDivisors.ne_zero hb)
    have h2v : v (2 : SliceField F₀) = 1 := by
      rw [← map_ofNat (algebraMap K (SliceField F₀)) 2]
      exact hK 2 h2
    have hFz : sliceProj F₀ F₀ = 0 := (sliceProj_eq_zero_iff F₀ F₀).2 dvd_rfl
    obtain ⟨a, b, ha, hb, hgen'⟩ := hgen hPz'
    -- the minimal order `n₁` of the centre
    obtain ⟨g₀, hg₀, hg₀0⟩ := center_nonzero v (sliceProj F₀) hint_all ⟨π₀, hπ₀⟩ hfrac
    have hex : ∃ n : ℕ, 0 < n ∧ ∃ g, v (sliceProj F₀ g) = exp (-(n : ℤ)) := by
      have hne : v (sliceProj F₀ g₀) ≠ 0 := (Valuation.ne_zero_iff v).2 hg₀0
      have hl : (v (sliceProj F₀ g₀)).log < 0 := by
        rw [log_lt_iff_lt_exp hne, exp_zero]; exact hg₀
      exact ⟨(-(v (sliceProj F₀ g₀)).log).toNat, by omega, g₀,
        (exp_log hne).symm.trans (by congr 1; omega)⟩
    set n₁ := Nat.find hex with hn₁def
    obtain ⟨hn₁pos, f₀, hf₀⟩ := Nat.find_spec hex
    have hn₁ : ∀ g, v (sliceProj F₀ g) < 1 → v (sliceProj F₀ g) ≤ exp (-(n₁ : ℤ)) := by
      intro g hg
      by_cases hz : v (sliceProj F₀ g) = 0
      · rw [hz]; exact zero_le
      have hl : (v (sliceProj F₀ g)).log < 0 := by
        rw [log_lt_iff_lt_exp hz, exp_zero]; exact hg
      have hmin := Nat.find_min' hex (m := (-(v (sliceProj F₀ g)).log).toNat)
        ⟨by omega, g, (exp_log hz).symm.trans (by congr 1; omega)⟩
      rw [← exp_log hz, exp_le_exp]
      omega
    have hdich := local_dichotomy v (sliceProj F₀) (MvPolynomial.pderiv (2 : Fin 4)) hint_all
      ⟨π₀, hπ₀⟩ hfrac h2v F₀ hFz a b ha hb hgen' n₁ hn₁
    obtain ⟨F₁, hHF⟩ := sliceProj_H_eq F F₀ hdvd
    have hHne : v (sliceProj F₀ (polyH K F)) ≠ 0 := (Valuation.ne_zero_iff v).2 hH
    have hdich' : n₁ ≤ 1 ∨ 3 * (n₁ : ℤ) ≤ 2 * h := by
      rcases hdich with h1 | h1
      · exact Or.inl h1
      right
      have hle : v (sliceProj F₀ (polyH K F)) ≤ v (sliceProj F₀ (pderiv 2 F₀)) := by
        rw [hHF, v.map_mul]; exact mul_le_of_le_one_left' (hint_all F₁)
      have h2' : v (sliceProj F₀ (polyH K F)) ^ 2 ≤ exp (-(3 * n₁ : ℤ)) :=
        (pow_le_pow_left₀ zero_le hle 2).trans h1
      rw [← exp_log hHne, ← exp_nsmul, exp_le_exp] at h2'
      have : h = max 0 (-(v (sliceProj F₀ (polyH K F))).log) := rfl
      simp only [nsmul_eq_mul] at h2'
      push_cast at h2'
      omega
    have hn₁K : (n₁ : K) ≠ 0 := by
      rcases hdich' with h1 | h1
      · have : n₁ = 1 := by omega
        rw [this, Nat.cast_one]; exact one_ne_zero
      · exact hchar n₁ hn₁pos (by rw [hPz']; omega)
    -- the affine target is `pσ`
    have hTa : T = pσ := by rw [hTeq, hPz', hq0, hq2]; omega
    have hsσ : s ≤ pσ := by have := hsP; rw [hPz'] at this; omega
    have hDf : v (Dd (sliceProj F₀ f₀)) ≤ exp pσ := by
      rw [hDd, sliceDerivation_proj_eq F F₀ hdvd hH]
      refine (v.map_add _ _).trans (max_le ?_ ?_)
      · exact (hint_all _).trans (by rw [← exp_zero, exp_le_exp]; exact hpσ0)
      · rw [v.map_mul]
        refine (mul_le_of_le_one_left' (hint_all _)).trans ?_
        exact v_le_exp_vpole v _
    have hθ := theta_of_element v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceProj F₀ f₀) n₁ hn₁K
      hf₀ pσ hDf
    have hmax : max s (pσ + n₁) = pσ + n₁ := max_eq_right (by omega)
    rw [hmax] at hθ
    by_cases hA : pσ = 0 ∧ n₁ = 1
    · -- no pole at all
      have hπ := pi_bound_general v Dd π₀ hπ₀ s pσ
        (integral_bound v Dd π₀ hπ₀ s hs0 C hcrude hsep) (sliceProj F₀ f₀) n₁ hn₁K hf₀ hDf
      have hs00 : s = 0 := by omega
      have hmx : max s (pσ + n₁) - 1 = 0 := by rw [hmax]; omega
      rw [hmx, exp_zero] at hπ
      have hD1 : ∀ u, v u ≤ 1 → v (Dd u) ≤ 1 := by
        intro u hu
        refine (integral_bound v Dd π₀ hπ₀ s hs0 C hcrude hsep u hu).trans (max_le ?_ hπ)
        rw [hs00, exp_zero]
      have hit := integral_iterate v Dd hD1 m _ (hcint 1)
      have hz : vpole v ((⇑Dd)^[m] (sliceCoord F₀ 1)) ≤ 0 :=
        (vpole_le_iff v _ 0 le_rfl).2 (by rwa [exp_zero])
      have := vpole_nonneg v ((⇑Dd)^[m] (sliceCoord F₀ 1))
      have : 0 ≤ (m : ℤ) * (4 * T + 2 * h) :=
        mul_nonneg (Nat.cast_nonneg m) (by omega)
      omega
    · -- the per-place law
      have hσh : pσ ≤ h := by
        rw [hpσdef, vpole_le_iff _ _ _ hh0, sliceSigma, map_div₀]
        by_cases hG0 : v (sliceProj F₀ (polyG K F)) = 0
        · rw [hG0, zero_div]; exact zero_le
        · rw [div_le_iff₀ (zero_lt_iff.2 hHne)]
          calc v (sliceProj F₀ (polyG K F)) ≤ 1 := hint_all _
            _ ≤ exp h * v (sliceProj F₀ (polyH K F)) := by
              rw [← exp_log hHne, ← exp_add, ← exp_zero, exp_le_exp]
              have : h = max 0 (-(v (sliceProj F₀ (polyH K F))).log) := rfl
              omega
      have hlaw : 3 * (pσ + n₁) ≤ 4 * T + 2 * h := by
        rw [hTa]
        rcases hdich' with h1 | h1
        · have : n₁ = 1 := by omega
          have : pσ ≠ 0 := fun h0 => hA ⟨h0, by omega⟩
          omega
        · omega
      have hit := pole_iterate_of_bound v Dd (pσ + n₁) (by omega) hθ m (sliceCoord F₀ 1)
      have := hmθ (pσ + n₁) (by omega) hlaw
      have hc1 : vpole v (sliceCoord F₀ 1) = 0 := hq1
      rw [hc1, zero_add] at hit
      rw [hPz']
      omega
  · -- places at infinity
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, vpole v (sliceCoord F₀ j) = P := by
      rcases max_choice p1 (max p0 p2) with h1 | h1
      · exact ⟨1, by rw [hPeq, h1]⟩
      · rcases max_choice p0 p2 with h2 | h2
        · exact ⟨0, by rw [hPeq, h1, h2]⟩
        · exact ⟨2, by rw [hPeq, h1, h2]⟩
    have hcj0 : v (sliceCoord F₀ j) ≠ 0 := by
      intro h0
      have : vpole v (sliceCoord F₀ j) = 0 := by simp [vpole, h0]
      omega
    have hcj : v (sliceCoord F₀ j) = exp ((P.toNat : ℕ) : ℤ) := by
      rw [← exp_log hcj0]
      congr 1
      have : vpole v (sliceCoord F₀ j) = max 0 (v (sliceCoord F₀ j)).log := rfl
      omega
    have hPK : ((P.toNat : ℕ) : K) ≠ 0 :=
      hchar P.toNat (by omega) (by rw [Int.toNat_of_nonneg hP0]; exact le_max_left _ _)
    have hQ : v (Dd (sliceCoord F₀ j)) ≤ exp (max P pσ) := by
      fin_cases j
      · show v (Dd (sliceCoord F₀ 0)) ≤ _
        rw [hDd, sliceDerivation_coord0 F F₀ hdvd hH]
        exact (v_le_exp_vpole v _).trans (by
          rw [exp_le_exp]; have := le_max_left p1 (max p0 p2); exact le_max_of_le_left (by omega))
      · show v (Dd (sliceCoord F₀ 1)) ≤ _
        rw [hDd, sliceDerivation_coord1 F F₀ hdvd hH]
        exact (v_le_exp_vpole v _).trans (by rw [exp_le_exp]; exact le_max_right _ _)
      · show v (Dd (sliceCoord F₀ 2)) ≤ _
        rw [hDd, sliceDerivation_coord2 F F₀ hdvd hH, v.map_zero]; exact zero_le
    have hθ := infinity_theta v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceCoord F₀ j) P.toNat hPK
      hcj (max P pσ) hQ
    set θ := max s (max 0 (max P pσ - 2 * ((P.toNat : ℕ) : ℤ)) + ((P.toNat : ℕ) : ℤ)) with hθdef
    have hPn : ((P.toNat : ℕ) : ℤ) = P := Int.toNat_of_nonneg hP0
    have hθT : θ ≤ T := by
      rw [hθdef, hPn]
      refine max_le (hsP.trans (max_le (by omega) hTσ)) ?_
      rcases le_total P pσ with h1 | h1
      · rw [max_eq_right h1]; omega
      · rw [max_eq_left h1]; omega
    have hθ0 : 0 ≤ θ := le_max_of_le_left hs0
    have hit := pole_iterate_of_bound v Dd θ hθ0 hθ m (sliceCoord F₀ 1)
    have hc1 : vpole v (sliceCoord F₀ 1) ≤ P := by rw [hPeq]; exact le_max_left _ _
    have h1 : (m : ℤ) * θ ≤ m * T := mul_le_mul_of_nonneg_left hθT (Nat.cast_nonneg m)
    have h3 : 0 ≤ (m : ℤ) * T := mul_nonneg (Nat.cast_nonneg m) (by omega)
    have h4 : 0 ≤ (m : ℤ) * h := mul_nonneg (Nat.cast_nonneg m) hh0
    nlinarith

end Slice

end ProximityPrize.SubmissionLower.HFree6812


