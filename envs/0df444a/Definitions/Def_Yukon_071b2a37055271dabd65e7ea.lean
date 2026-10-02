-- Prove2me | Definitions.Def_Yukon_071b2a37055271dabd65e7ea
-- name    : Yukon_071b2a37055271dabd65e7ea
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:33:05.955005+00:00
-- url     : https://prove2.me/theorems/13d7e8ce-152c-40db-a8fa-151bcbe32c80
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeInfLaw6813.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeInfLaw6813.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeInfLaw6813.lean
--
--   yukon-proof-operation:foundation-direct-03aa085ab49ca878c6d5481beec16d7bb24109b0268ff3a9bd831869e679e20f-parser-retry
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTEwYzdkOGJhNWI4ZTg5NmYxOGU1Zjg0ZmRhNGZlODAzZjY2Yzk1MDg5ZDk1NWM0YTI1NGVhMDE4MjhmMThiZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTAzYWEwODVhYjQ5Y2E4NzhjNmQ1NDgxYmVlYzE2ZDdiYjI0MTA5YjAyNjhmZjNhOWJkODMxODY5ZTY3OWUyMGYtcGFyc2VyLXJldHJ5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMDcxYjJhMzcwNTUyNzFkYWJkNjVlN2VhIiwidiI6Mn0]

import Definitions.Def_Yukon_88acd699d7b2611ef3b71a58
































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free first cut: the per-direction law at infinity

At a place over infinity let `P` be the largest pole of `Y, Y', Γ`, `t = max (pole Y, pole Γ)`,
`pσ = pole σ`, `T = max (2P, t + pσ)` and `s = pole (D ℓ)` for the slice form `ℓ`.

* `infinity_theta_signed`: `infinity_theta` without the truncation `max 0`; with a coordinate of
  pole `P` it gives `θ = max (s, pσ - P)`.
* The slice form bounds `s` by direction (`sliceLinearL_dir`): `s = 0` for `ℓ = Γ`,
  `s ≤ P` for `ℓ = Y + λΓ`, and `s ≤ max (P, pσ)` for `ℓ = Y' + μY + μλΓ`.
* Together (`place_bound_dir`): `3θ ≤ 4T - capPole d`, with `capPole = 3t + 5P, 5P, 3t + 2P`
  (the flags `infCap d`).  Affine places (`P = t = 0`) keep `place_bound`.

Summed over a finite set of places (`hfree_slice_budget_dir`), the H-free budget gains the term
`(w+1) · flagPole (infCap d)`.
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204

section Signed

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)

/-- Places at infinity, signed form: if a coordinate `c` has a pole of order `P` (`P` a unit in
`K`) and `pole (D c) ≤ Q`, then `θ := max (s, Q - P)` works.  `Q - P` may be negative. -/
theorem infinity_theta_signed [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s : ℤ)
    (hs : 0 ≤ s) (C : ℤ) (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s))
    (c : L) (P : ℕ) (hP : (P : K) ≠ 0) (hc : v c = exp (P : ℤ)) (Q : ℤ)
    (hQ : v (D c) ≤ exp Q) :
    ∀ g : L, v (D g) ≤ exp (max s (Q - P)) * v g := by
  have hc0 : c ≠ 0 := by intro h; rw [h, v.map_zero] at hc; exact exp_ne_zero hc.symm
  have hu : v c⁻¹ = exp (-(P : ℤ)) := by rw [map_inv₀, hc, exp_neg]
  have hDu : v (D c⁻¹) ≤ exp (Q - 2 * P) := by
    rw [Derivation.leibniz_inv, smul_eq_mul, v.map_mul, v.map_neg, v.map_pow, hu]
    calc exp (-(P : ℤ)) ^ 2 * v (D c) ≤ exp (-(P : ℤ)) ^ 2 * exp Q := mul_le_mul_right hQ _
      _ = exp (Q - 2 * P) := by rw [sq, ← exp_add, ← exp_add]; congr 1; ring
  have h := theta_of_element v D π hπ s hs C hcont hsep c⁻¹ P hP hu _ hDu
  intro g
  have hg := h g
  rwa [show Q - 2 * (P : ℤ) + P = Q - P by ring] at hg

end Signed

/-- The cap at infinity, per slice direction, as a flag: `3t + 5P` (`ℓ = Γ`), `5P`
(`ℓ = Y + λΓ`) and `3t + 2P` (`ℓ = Y' + μY + μλΓ`). -/
def infCap (d : Fin 3) : FlagDegree := ![⟨0,3,5⟩, ⟨0,0,5⟩, ⟨0,3,2⟩] d

theorem infCap_zOnly (d : Fin 3) : (infCap d).zOnly = 0 := by fin_cases d <;> rfl

/-- `flagPole (infCap d)` in terms of `P` and `t`. -/
def capPole (d : Fin 3) (P t : ℤ) : ℤ := ((infCap d).yz : ℤ) * t + ((infCap d).all : ℤ) * P

/-- The tame exponent of the slice form, per direction. -/
def dirS (d : Fin 3) (P pσ : ℤ) : ℤ := ![0, P, max P pσ] d

/-- The slice form `ℓ = Σ q_m c_m` of direction `d`: `ℓ = q₂ Γ` with `q₂` constant, `ℓ` free of
`Y'`, or arbitrary. -/
def DirShape {K : Type} [Field K] (d : Fin 3) (q : Fin 3 → Polynomial K) : Prop :=
  ![q 0 = 0 ∧ q 1 = 0 ∧ Polynomial.derivative (q 2) = 0, q 1 = 0, True] d

section Slice

variable {K : Type} [Field K] (F F₀ : MvPolynomial (Fin 4) K) [hF₀ : Fact (Irreducible F₀)]
  (hdvd : F₀ ∣ F)
set_option linter.unusedSectionVars false

/-- `t = max (pole Y, pole Γ)` (`flagPole` of `unitYZFlag`). -/
noncomputable def placeYZ (v : Valuation (SliceField F₀) ℤᵐ⁰) : ℤ :=
  max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))

variable (v : Valuation (SliceField F₀) ℤᵐ⁰)

/-- The derivative of the slice form of direction `d` has pole at most `dirS d P pσ`. -/
theorem sliceLinearL_dir (hH : sliceProj F₀ (polyH K F) ≠ 0)
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1) (d : Fin 3) (q : Fin 3 → Polynomial K)
    (hq : DirShape d q) :
    vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)) ≤
      dirS d (placeP F₀ v) (vpole v (sliceSigma F F₀)) := by
  set x0 := sliceProj F₀ (MvPolynomial.X 0)
  set Dd := sliceDerivation F F₀ hdvd
  have hP0 : 0 ≤ placeP F₀ v := le_max_of_le_left (vpole_nonneg _ _)
  have hcoord : ∀ j, v (sliceCoord F₀ j) ≤ exp (placeP F₀ v) := by
    intro j
    refine (v_le_exp_vpole v _).trans ?_
    rw [exp_le_exp, placeP]
    fin_cases j
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_max_right _ _)
  have hDa : ∀ p : Polynomial K, Dd (Polynomial.aeval x0 p) =
      Polynomial.aeval x0 (Polynomial.derivative p) := by
    intro p
    rw [Derivation.map_aeval, sliceDerivation_X0 F F₀ hdvd hH, smul_eq_mul, mul_one]
  have hterm : ∀ m, Dd (Polynomial.aeval x0 (q m) * sliceCoord F₀ m) =
      Polynomial.aeval x0 (q m) * Dd (sliceCoord F₀ m) +
        sliceCoord F₀ m * Polynomial.aeval x0 (Polynomial.derivative (q m)) := by
    intro m; rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDa]
  have hDc0 : Dd (sliceCoord F₀ 0) = sliceCoord F₀ 1 := sliceDerivation_coord0 F F₀ hdvd hH
  have hDc2 : Dd (sliceCoord F₀ 2) = 0 := sliceDerivation_coord2 F F₀ hdvd hH
  have hℓ : Dd (sliceLinearL F₀ q) = ∑ m, (Polynomial.aeval x0 (q m) * Dd (sliceCoord F₀ m) +
      sliceCoord F₀ m * Polynomial.aeval x0 (Polynomial.derivative (q m))) := by
    rw [sliceLinearL, map_sum]; exact Finset.sum_congr rfl fun m _ => hterm m
  fin_cases d
  · obtain ⟨h0, h1, h2⟩ : q 0 = 0 ∧ q 1 = 0 ∧ Polynomial.derivative (q 2) = 0 := hq
    have hz : Dd (sliceLinearL F₀ q) = 0 := by
      rw [hℓ, Fin.sum_univ_three, h0, h1, h2]
      simp [hDc2]
    change vpole v _ ≤ 0
    rw [hz]; simp [vpole]
  · have h1 : q 1 = 0 := hq
    change vpole v _ ≤ placeP F₀ v
    rw [vpole_le_iff _ _ _ hP0, hℓ, Fin.sum_univ_three, h1, hDc0, hDc2]
    simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add]
    refine (v.map_add _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) ?_) <;>
      rw [v.map_mul]
    · exact (mul_le_of_le_one_left' (v_aeval_le_one F₀ v hK hX0 _)).trans (hcoord 1)
    · exact (mul_le_of_le_one_right' (v_aeval_le_one F₀ v hK hX0 _)).trans (hcoord 0)
    · exact (mul_le_of_le_one_right' (v_aeval_le_one F₀ v hK hX0 _)).trans (hcoord 2)
  · change vpole v _ ≤ max (placeP F₀ v) (vpole v (sliceSigma F F₀))
    rw [vpole_le_iff _ _ _ (le_max_of_le_left hP0)]
    refine (sliceLinearL_bound F F₀ hdvd v hH hK hX0 q).trans (max_le ?_ ?_)
    · rw [exp_le_exp]; exact le_max_left _ _
    · exact (v_le_exp_vpole v _).trans (by rw [exp_le_exp]; exact le_max_right _ _)

/-- **Per-place bound on `L0`, per direction.**  As `place_bound`, with the cap at infinity:
`3 pole (D^m Y') + m · capPole d P t ≤ m (4T + 2h) + 3P`. -/
theorem place_bound_dir (d : Fin 3) (hH : sliceProj F₀ (polyH K F) ≠ 0)
    (hnorm : ∃ x, v x = exp (-1))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1)
    (hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1)
    (ℓ : SliceField F₀)
    (hℓ : v (sliceDerivation F F₀ hdvd ℓ) ≤ max (exp (placeP F₀ v)) (v (sliceSigma F F₀)))
    (hdir : vpole v (sliceDerivation F F₀ hdvd ℓ) ≤
      dirS d (placeP F₀ v) (vpole v (sliceSigma F F₀)))
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
    3 * vpole v ((⇑(sliceDerivation F F₀ hdvd))^[m] (sliceCoord F₀ 1)) +
        m * capPole d (placeP F₀ v) (placeYZ F₀ v) ≤
      m * (4 * placeT F F₀ v + 2 * placeH F F₀ v) + 3 * placeP F₀ v := by
  classical
  haveI : v.IsTrivialOn K := ⟨hK⟩
  set Dd := sliceDerivation F F₀ hdvd with hDd
  set P := placeP F₀ v with hPdef
  set T := placeT F F₀ v with hTdef
  set h := placeH F F₀ v with hhdef
  set pσ := vpole v (sliceSigma F F₀) with hpσdef
  set s := vpole v (Dd ℓ) with hsdef
  set t := placeYZ F₀ v with htdef
  set p0 := vpole v (sliceCoord F₀ 0)
  set p1 := vpole v (sliceCoord F₀ 1)
  set p2 := vpole v (sliceCoord F₀ 2)
  have hp0 : 0 ≤ p0 := vpole_nonneg _ _
  have hp1 : 0 ≤ p1 := vpole_nonneg _ _
  have hp2 : 0 ≤ p2 := vpole_nonneg _ _
  have hPeq : P = max p1 (max p0 p2) := rfl
  have hteq : t = max p0 p2 := rfl
  have hTeq : T = max (2 * P) (max p0 p2 + pσ) := rfl
  have ht0 : 0 ≤ t := le_max_of_le_left hp0
  have htP : t ≤ P := le_max_right _ _
  have hh0 : 0 ≤ h := vzero_nonneg _ _
  have hs0 : 0 ≤ s := vpole_nonneg _ _
  have hTP : 2 * P ≤ T := le_max_left _ _
  have hTσ : t + pσ ≤ T := le_max_right _ _
  have hold := place_bound F F₀ hdvd v hH hnorm hK hX0 ℓ hℓ C hcrude hsep h2 hchar hgen m
  rcases eq_or_lt_of_le (le_max_of_le_left hp1 : 0 ≤ P) with hPz | hPpos
  · -- affine places: `P = t = 0`, the cap vanishes
    have hcap : capPole d P t = 0 := by
      have hPz' : P = 0 := hPz.symm
      have htz : t = 0 := by omega
      rw [capPole, htz, hPz']; ring
    rw [hcap, mul_zero, add_zero]
    exact hold
  · -- places at infinity
    have hPpos : 0 < P := hPpos
    obtain ⟨π₀, hπ₀⟩ := hnorm
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
      hchar P.toNat (by omega) (by rw [Int.toNat_of_nonneg hPpos.le]; exact le_max_left _ _)
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
    have hθ := infinity_theta_signed v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceCoord F₀ j) P.toNat
      hPK hcj (max P pσ) hQ
    have hPn : ((P.toNat : ℕ) : ℤ) = P := Int.toNat_of_nonneg hPpos.le
    rw [hPn] at hθ
    set θ := max s (max P pσ - P) with hθdef
    have hθ0 : 0 ≤ θ := le_max_of_le_left hs0
    -- the per-direction law `3θ + capPole ≤ 4T`
    have hlaw : 3 * θ + capPole d P t ≤ 4 * T := by
      rw [hθdef]
      fin_cases d <;> simp only [capPole, infCap, dirS] at hdir ⊢ <;> simp at hdir ⊢ <;> omega
    have hit := pole_iterate_of_bound v Dd θ hθ0 hθ m (sliceCoord F₀ 1)
    have hc1 : vpole v (sliceCoord F₀ 1) ≤ P := by rw [hPeq]; exact le_max_left _ _
    have h1 : (m : ℤ) * (3 * θ + capPole d P t) ≤ m * (4 * T) :=
      mul_le_mul_of_nonneg_left hlaw (Nat.cast_nonneg m)
    have h4 : 0 ≤ (m : ℤ) * h := mul_nonneg (Nat.cast_nonneg m) hh0
    nlinarith

end Slice

section Budget

variable {K : Type} [Field K] {E : Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

local notation "w" => RCN326.w

omit [IsAlgClosed E] in
/-- `flagPole (infCap d)` is at most `4T`, since `t ≤ P` and `2P ≤ T`. -/
theorem infCap_le_target (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (H G : MvPolynomial (Fin 3) E) (ν : RCN026.Place E (CoordinateField E D)) (d : Fin 3) :
    flagPole ν.val (coordinate E D) (infCap d) ≤ 4 * RCN064.movingPoleTarget D H G ν := by
  have hT := le_max_left (2 * max (RCN187.poleOrder ν.val (coordinate E D 1))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2))))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2)) +
      RCN187.poleOrder ν.val (RCN064.movingRatio D H G))
  have ht := le_max_right (RCN187.poleOrder ν.val (coordinate E D 1))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2)))
  have ht0 : 0 ≤ max (RCN187.poleOrder ν.val (coordinate E D 0))
      (RCN187.poleOrder ν.val (coordinate E D 2)) :=
    le_max_of_le_left (le_max_left _ _)
  unfold RCN064.movingPoleTarget
  fin_cases d <;> simp only [flagPole, infCap] <;> simp <;> omega

/-- **Per-place bound at a slice place, per direction**, in the consumer's quantities:
`nu_place_bound` with `(w+1) · flagPole (infCap d)` on the left. -/
theorem nu_place_bound_dir (d : Fin 3) (F : MvPolynomial (Fin 4) K)
    (D : Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
    (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (q : Fin 3 → Polynomial K) (hqd : DirShape d q)
    (hq : ∀ m, polynomialEmbedding K (q m) = c m)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E
        (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (h2 : (2 : K) ≠ 0)
    (ν : RCN026.Place E (CoordinateField E D))
    (hchar : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
      (RCN026.zeroOrder E (CoordinateField E D) ν
        (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0)
    (hdefer : ∀ (e : ℕ) (v : Valuation (SliceField F₀) ℤᵐ⁰), 1 ≤ e → (∃ x, v x = exp (-1)) →
      (∀ x, ν.val (sliceEmbedding D F₀ hker x) = v x ^ e) →
      (∃ C, CrudeBound v (sliceDerivation F F₀ hdvd) C) ∧
      ResiduallySeparable v (sliceDerivation F F₀ hdvd)
        (exp (vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q))))) :
    3 * RCN187.poleOrder ν.val
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1)) +
      ((w+1 : ℕ) : ℤ) * flagPole ν.val (coordinate E D) (infCap d) ≤
    ((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν +
        2*RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) +
      3*flagPole ν.val (coordinate E D) unitAllFlag := by
  classical
  set ψ := sliceEmbedding D F₀ hker with hψdef
  set Dd := sliceDerivation F F₀ hdvd with hDd
  set wv : Valuation (SliceField F₀) ℤᵐ⁰ := ν.val.comap ψ with hwvdef
  have hwv : ∀ x, wv x = ν.val (ψ x) := fun _ => rfl
  have hHψ : ψ (sliceProj F₀ (polyH K F)) ≠ 0 := by
    rw [hψdef, sliceEmbedding_proj]
    intro h
    exact hHD ((coordEval_eq_zero_iff D _).1 h)
  have hH : sliceProj F₀ (polyH K F) ≠ 0 := fun h => hHψ (by rw [h, map_zero])
  have hτ : SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
      SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1) =
      ψ ((⇑Dd)^[w] (sliceCoord F₀ 1)) := by
    have h := sliceDerivation_iterate F F₀ hdvd hH (w - 1)
    have hw1 : w - 1 + 1 = w := rfl
    have hw2 : 2 * (w - 1) + 1 = 2 * w - 1 := rfl
    rw [hw1, hw2] at h
    rw [show sliceCoord F₀ 1 = sliceProj F₀ (MvPolynomial.X 2) from rfl, h, map_div₀, map_pow,
      hψdef, sliceEmbedding_proj, sliceEmbedding_proj]
    rfl
  rw [hτ]
  have hcap4 := infCap_le_target D (surfaceMap (phiE K E) (polyH K F))
    (surfaceMap (phiE K E) (polyG K F)) ν d
  have hRHS0 : ((w+1 : ℕ) : ℤ) * flagPole ν.val (coordinate E D) (infCap d) ≤
      ((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν +
        2*RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) +
      3*flagPole ν.val (coordinate E D) unitAllFlag := by
    have h2 := RCN026.zeroOrder_nonneg E (CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))
    have h3 := flagPole_nonneg ν.val (coordinate E D) unitAllFlag
    have hw : (0 : ℤ) ≤ ((w+1 : ℕ) : ℤ) := by positivity
    have h4 := mul_le_mul_of_nonneg_left hcap4 hw
    have h5 := mul_nonneg hw (mul_nonneg (show (0 : ℤ) ≤ 2 by norm_num) h2)
    rw [mul_add]
    linarith
  by_cases hnt : ∃ x, wv x ≠ 0 ∧ wv x ≠ 1
  swap
  · have hpole : RCN187.poleOrder ν.val (ψ ((⇑Dd)^[w] (sliceCoord F₀ 1))) = 0 := by
      set x := (⇑Dd)^[w] (sliceCoord F₀ 1)
      have hx : wv x = 0 ∨ wv x = 1 := by
        by_contra h; rw [not_or] at h; exact hnt ⟨x, h.1, h.2⟩
      show max 0 (ν.val (ψ x)).log = 0
      rw [← hwv]
      rcases hx with h | h <;> simp [h]
    rw [hpole, mul_zero, zero_add]
    exact hRHS0
  obtain ⟨e, v, he, hvn, hwve⟩ := exists_normalization wv hnt
  have he0 : e ≠ 0 := by omega
  have hν : ∀ x, ν.val (ψ x) = v x ^ e := fun x => hwve x
  have hpole : ∀ x, RCN187.poleOrder ν.val (ψ x) = e * vpole v x :=
    fun x => poleOrder_pow v wv e hwve x
  have hzeroν : ∀ x, RCN026.zeroOrder E (CoordinateField E D) ν (ψ x) = e * vzero v x :=
    fun x => zeroOrder_pow v wv e hwve x
  have hνE : ∀ a : E, a ≠ 0 → ν.val (algebraMap E (CoordinateField E D) a) = 1 :=
    fun a ha => (ν.property.2).eq_one a ha
  have hφinj : Function.Injective (phiE K E) :=
    (algebraMap (GenericField K) E).injective.comp (polynomialEmbedding_injective K)
  have hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1 := by
    intro a ha
    have h1 : ν.val (ψ (algebraMap K _ a)) = 1 := by
      rw [hψdef, psi_const]
      exact hνE _ (fun h => ha (Polynomial.C_eq_zero.mp (hφinj (h.trans (map_zero _).symm))))
    rw [hν] at h1
    exact le_antisymm ((zm_pow_le_one he0).1 h1.le)
      (not_lt.1 fun hlt => absurd h1 (ne_of_lt ((zm_pow_lt_one he0).2 hlt)))
  have hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1 := by
    have h1 : ν.val (ψ (sliceProj F₀ (MvPolynomial.X 0))) ≤ 1 := by
      rw [hψdef, psi_X0]
      haveI := ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    rw [hν] at h1
    exact (zm_pow_le_one he0).1 h1
  obtain ⟨⟨C, hcrude⟩, hsep⟩ := hdefer e v he hvn hwve
  have hℓ := sliceLinearL_bound F F₀ hdvd v hH hK hX0 q
  have hdir := sliceLinearL_dir F F₀ hdvd v hH hK hX0 d q hqd
  -- the consumer quantities scale by `e`
  have hcoordν : ∀ j, RCN187.poleOrder ν.val (coordinate E D j) =
      e * vpole v (sliceCoord F₀ j) := by
    intro j; rw [← psi_coord D F₀ hker j, ← hψdef, hpole]
  have hPν : flagPole ν.val (coordinate E D) unitAllFlag = e * placeP F₀ v := by
    simp only [flagPole, unitAllFlag, Nat.cast_zero, zero_mul, Nat.cast_one, one_mul, zero_add]
    rw [hcoordν, hcoordν, hcoordν, placeP, scale_flag (e : ℤ) (by positivity)]
  have hcapν : flagPole ν.val (coordinate E D) (infCap d) =
      e * capPole d (placeP F₀ v) (placeYZ F₀ v) := by
    simp only [flagPole, infCap_zOnly, Nat.cast_zero, zero_mul, zero_add]
    rw [hcoordν, hcoordν, hcoordν, capPole, placeP, placeYZ, scale_flag (e : ℤ) (by positivity),
      ← mul_max_of_nonneg _ _ (by positivity : (0 : ℤ) ≤ e)]
    ring
  have hhν : RCN026.zeroOrder E (CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)) =
        e * placeH F F₀ v := by
    have : SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F) =
        ψ (sliceProj F₀ (polyH K F)) := by rw [hψdef, sliceEmbedding_proj]; rfl
    rw [this, hzeroν]
    rfl
  have hTν : RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
      (surfaceMap (phiE K E) (polyG K F)) ν = e * placeT F F₀ v := by
    unfold RCN064.movingPoleTarget
    rw [hcoordν, hcoordν, hcoordν, ← psi_sigma D F₀ hker F, ← hψdef, hpole, placeT, placeP,
      scale_target (e : ℤ) (by positivity)]
  have hPv0 : 0 ≤ placeP F₀ v := le_max_of_le_left (vpole_nonneg _ _)
  have hhv0 : 0 ≤ placeH F F₀ v := vzero_nonneg _ _
  have hcharv : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (placeP F₀ v) (placeH F F₀ v) → (n : K) ≠ 0 := by
    intro n hn hle
    refine hchar n hn ?_
    rw [hPν, hhν]
    have h1 : placeP F₀ v ≤ e * placeP F₀ v := le_mul_of_one_le_left hPv0 (by exact_mod_cast he)
    have h2 : placeH F F₀ v ≤ e * placeH F F₀ v := le_mul_of_one_le_left hhv0 (by exact_mod_cast he)
    exact hle.trans (max_le_max h1 h2)
  have hgen : placeP F₀ v = 0 → ∃ a b : MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a) < 1 ∧ v (sliceProj F₀ b) < 1 ∧
      ∀ g, v (sliceProj F₀ g) < 1 → ∃ s x y : MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s) = 1 ∧ s * g = x * a + y * b := by
    intro hP0
    have hint := place_hint F₀ v hK hX0 hP0
    set 𝔓 := valCentre (sliceProj F₀) v hint with h𝔓def
    set y : Fin 3 → CoordinateField E D := coordinate E D
    have hev : ∀ P : MvPolynomial (Fin 3) (GenericField K),
        aeval y P = coordinateEvaluation E D (scalarPolynomialMap (GenericField K) E P) := by
      intro P
      rw [coordinateEvaluation_eq_aeval, scalarPolynomialMap, aeval_map_algebraMap]
    have hνΩ : ∀ a : GenericField K,
        ν.val (algebraMap (GenericField K) (CoordinateField E D) a) ≤ 1 := by
      intro a
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D)]
      haveI := ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    have hyint : ∀ j, ν.val (y j) ≤ 1 := by
      intro j
      rw [show y j = ψ (sliceCoord F₀ j) from (psi_coord D F₀ hker j).symm, hν]
      exact pow_le_one' (hint _) e
    let fy : MvPolynomial (Fin 3) (GenericField K) →+* CoordinateField E D := (aeval y).toRingHom
    have hintΩ : ∀ P : MvPolynomial (Fin 3) (GenericField K), ν.val (fy P) ≤ 1 := by
      intro P
      change ν.val (aeval y P) ≤ 1
      induction P using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact hνΩ a
      | add p r hp hr => rw [map_add]; exact (ν.val.map_add _ _).trans (max_le hp hr)
      | mul_X p j hp =>
        rw [map_mul, ν.val.map_mul, aeval_X]; exact mul_le_one' hp (hyint j)
    set 𝔮 := valCentre fy ν.val hintΩ with h𝔮def
    have hP𝔮 : originalPrime 𝔮 = 𝔓 := by
      ext g
      rw [mem_originalPrime_iff, h𝔮def, h𝔓def, mem_valCentre, mem_valCentre]
      change ν.val (aeval y _) < 1 ↔ _
      rw [hev, ← surfaceMap_generic_eq]
      change ν.val (sliceMap D g) < 1 ↔ _
      rw [← sliceEmbedding_proj D F₀ hker, ← hψdef, hν, zm_pow_lt_one he0]
    have hcω : ∀ a : GenericField K, a ≠ 0 →
        ν.val (algebraMap (GenericField K) (CoordinateField E D) a) = 1 := by
      intro a ha
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D)]
      exact hνE _ ((map_ne_zero_iff _ (algebraMap (GenericField K) E).injective).2 ha)
    have hsl : ∑ m, algebraMap (GenericField K) (CoordinateField E D) (c m) * y m =
        algebraMap E (CoordinateField E D) (sliceValue (GenericField K) E) := by
      have h1 := (coordEval_eq_zero_iff D _).2 hslice
      rw [map_sub, sub_eq_zero, ← hev] at h1
      have h2 : coordinateEvaluation E D (MvPolynomial.C (sliceValue (GenericField K) E)) =
          algebraMap E (CoordinateField E D) (sliceValue (GenericField K) E) :=
        (coordinateEvaluation E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum, map_mul, aeval_C, aeval_X]
    have hℓ' : ∀ a : Fin 3 → GenericField K,
        ν.val (∑ m, algebraMap (GenericField K) (CoordinateField E D) (c m) * y m -
          algebraMap (GenericField K) (CoordinateField E D) (∑ m, c m * a m)) = 1 := by
      intro a
      rw [hsl, IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D),
        ← map_sub]
      apply hνE
      intro h
      apply sliceValue_transcendental (Ω := GenericField K) (E := E)
      rw [sub_eq_zero] at h
      rw [h]
      exact isAlgebraic_algebraMap _
    have h𝔮h : 𝔮.height ≤ 2 :=
      centre_height_le_two ν.val y 𝔮 (fun P => mem_valCentre _ _ _ P) c hcω hℓ'
    have h𝔓h : 𝔓.height ≤ 2 := hP𝔮 ▸ (originalPrime_height_le 𝔮).trans h𝔮h
    haveI := RCN230.mvPolynomial_atPrime_isRegularLocalRing 𝔓
    obtain ⟨a, ha, b, hb, hgen'⟩ := exists_two_local_generators 𝔓 h𝔓h
    refine ⟨a, b, ha, hb, fun g hg => ?_⟩
    obtain ⟨s, hs, x, y, hsg⟩ := hgen' g hg
    exact ⟨s, x, y, le_antisymm (hint s) (not_lt.1 hs), hsg⟩
  have hmain := place_bound_dir F F₀ hdvd v d hH hvn hK hX0 (sliceLinearL F₀ q) hℓ hdir C hcrude
    hsep h2 hcharv hgen w
  rw [hpole, hTν, hhν, hPν, hcapν]
  rw [hcapν, hTν] at hcap4
  have hk := mul_le_mul_of_nonneg_left hmain (show (0 : ℤ) ≤ e by positivity)
  have heh : 0 ≤ (e : ℤ) * placeH F F₀ v := mul_nonneg (by positivity) hhv0
  push_cast at hk ⊢
  linarith

/-- **The H-free per-slice budget, per direction**: `hfree_slice_budget` with
`Σ (w+1) · flagPole (infCap d)` subtracted, for a slice of direction `d` (`DirShape d q`). -/
theorem hfree_slice_budget_dir (d : Fin 3) (F : MvPolynomial (Fin 4) K)
    (D : Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hFD : surfaceMap (phiE K E) F ∈ D) (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1) (q : Fin 3 → Polynomial K)
    (hqd : DirShape d q) (hq : ∀ m, polynomialEmbedding K (q m) = c m)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E
        (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (h2 : (2 : K) ≠ 0)
    (hchar : ∀ ν : RCN026.Place E (CoordinateField E D), ∀ n : ℕ, 0 < n →
      (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0)
    (hdefer : ∀ (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
      (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
      (ν : RCN026.Place E (CoordinateField E D)) (e : ℕ) (v : Valuation (SliceField F₀) ℤᵐ⁰),
      1 ≤ e → (∃ x, v x = exp (-1)) →
      (∀ x, ν.val (sliceEmbedding D F₀ hker x) = v x ^ e) →
      (∃ C, CrudeBound v (sliceDerivation F F₀ hdvd) C) ∧
      ResiduallySeparable v (sliceDerivation F F₀ hdvd)
        (exp (vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)))))
    (W : Finset (RCN026.Place E (CoordinateField E D))) :
    3 * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1))) ≤
    ∑ nu ∈ W, (((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) nu +
        2*RCN026.zeroOrder E (CoordinateField E D) nu
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)) -
        flagPole nu.val (coordinate E D) (infCap d)) +
      3*flagPole nu.val (coordinate E D) unitAllFlag) := by
  have hF : F ≠ 0 := by
    rintro rfl
    apply hHD
    simp [polyH]
  obtain ⟨F₀, hirr, hdvd, hker⟩ := slice_descent D sep F hF hFD c i hci hslice
  haveI : Fact (Irreducible F₀) := ⟨hirr⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ν _ => ?_
  have h := nu_place_bound_dir d F D F₀ hdvd hker hHD c q hqd hq hslice h2 ν (hchar ν)
    (hdefer F₀ hdvd hker ν)
  linarith

end Budget

end ProximityPrize.SubmissionLower.HFree6812


