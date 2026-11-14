-- Prove2me | Definitions.Def_RPLib_S3_ConjClassesD
-- name    : RPLib_S3_ConjClassesD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:00:26.55747+00:00
-- url     : https://prove2.me/theorems/858b1749-ff0b-477e-9f63-5325a202635d
-- title:
--   The Eichler-Selberg trace formula, conjugacy classes part D: orientation and imprimitive classes
-- statement:
--   Elliptic classes with lower-left entry $c < 0$ give the same class sum as those with $c > 0$; the imprimitive forms (matrix in $p M_2(\mathbb{Z})$) contribute the class sum at $(t/p, n/p^2)$; and small numerical values of the class sums.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_ConjClassesB

/-!
# Conjugacy classes (unit S3-ConjClasses, part D): negative orientation, imprimitive classes, sanity values

* `classSum_congr`: class sums are invariant under an equivariant bijection along a group isomorphism.
* `classSum_EllNeg`: the elliptic classes with lower-left entry `c < 0` (conjugate by `ε = diag(1, -1)`) also sum to
  `ellCount M δ' t n`.
* `ellCount_imprimitive`: the reduced forms whose matrix `γ_Q` lies in `p M₂(ℤ)` (`p` a unit mod `M`) contribute
  `ellCount M (δ' p⁻¹) (t/p) (n/p²)`.
* `level1Ell` (`Level1Ell` of `Statements.lean`) and small numeric values of `ellCount`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Conj

open Matrix MatrixGroups RamanujanPetersson.Hurwitz CongruenceSubgroup

/-! ## Transfer of class sums -/

/-- An equivariant bijection `φ` along a group isomorphism `σ` preserves the orbit relation. -/
theorem orbitRel_congr_iff {G G' X X' : Type*} [Group G] [Group G'] [MulAction G X] [MulAction G' X']
    (σ : G ≃* G') (φ : X ≃ X') (hφ : ∀ (g : G) (x : X), φ (g • x) = σ g • φ x) (a b : X) :
    (MulAction.orbitRel G X) a b ↔ (MulAction.orbitRel G' X') (φ a) (φ b) := by
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩; exact ⟨σ g, (hφ g b).symm⟩
  · rintro ⟨g', hg'⟩
    refine ⟨σ.symm g', φ.injective ?_⟩
    rw [hφ, MulEquiv.apply_symm_apply, hg']

/-- The induced bijection of orbit spaces. -/
def quotCongr {G G' X X' : Type*} [Group G] [Group G'] [MulAction G X] [MulAction G' X']
    (σ : G ≃* G') (φ : X ≃ X') (hφ : ∀ (g : G) (x : X), φ (g • x) = σ g • φ x) :
    MulAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient G' X' :=
  Quotient.congr φ (orbitRel_congr_iff σ φ hφ)

/-- An equivariant bijection `φ` along a group isomorphism `σ` preserves `classSum`. -/
theorem classSum_congr {G G' X X' : Type*} [Group G] [Group G'] [MulAction G X] [MulAction G' X']
    (σ : G ≃* G') (φ : X ≃ X') (hφ : ∀ (g : G) (x : X), φ (g • x) = σ g • φ x) :
    classSum G X = classSum G' X' := by
  have hrel := orbitRel_congr_iff σ φ hφ
  have hstab : ∀ x : X,
      Nat.card (MulAction.stabilizer G' (φ x)) = Nat.card (MulAction.stabilizer G x) := by
    intro x
    symm
    refine Nat.card_congr (Equiv.subtypeEquiv σ.toEquiv fun g => ?_)
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    show g • x = x ↔ σ g • φ x = φ x
    rw [← hφ, φ.injective.eq_iff]
  let e : MulAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient G' X' := Quotient.congr φ hrel
  unfold classSum
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun C => ?_
  induction C using Quotient.inductionOn with
  | h x =>
    have he : e (Quotient.mk _ x) = Quotient.mk _ (φ x) := Quotient.congr_mk φ hrel x
    rw [he, card_stab_out, card_stab_out, hstab]

/-! ## B2. The negative orientation `c < 0` -/

/-- `ε γ ε` for `ε = diag(1, -1)`: `[[a, b], [c, d]] ↦ [[a, -b], [-c, d]]`. -/
def flip (γ : Mat) : Mat := !![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1]

@[simp] theorem flip_apply_00 (γ : Mat) : flip γ 0 0 = γ 0 0 := by simp [flip]
@[simp] theorem flip_apply_01 (γ : Mat) : flip γ 0 1 = -γ 0 1 := by simp [flip]
@[simp] theorem flip_apply_10 (γ : Mat) : flip γ 1 0 = -γ 1 0 := by simp [flip]
@[simp] theorem flip_apply_11 (γ : Mat) : flip γ 1 1 = γ 1 1 := by simp [flip]

theorem flip_flip (γ : Mat) : flip (flip γ) = γ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem flip_mul (x y : Mat) : flip (x * y) = flip x * flip y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_flip (γ : Mat) : (flip γ).det = γ.det := by
  simp [Matrix.det_fin_two]

theorem trace_flip (γ : Mat) : (flip γ).trace = γ.trace := by
  simp [Matrix.trace_fin_two]

/-- Conjugation by `ε` on `SL(2, ℤ)`. -/
def flipSL : SL(2, ℤ) ≃* SL(2, ℤ) where
  toFun g := ⟨flip g, by rw [det_flip]; exact g.2⟩
  invFun g := ⟨flip g, by rw [det_flip]; exact g.2⟩
  left_inv g := Subtype.ext (flip_flip g)
  right_inv g := Subtype.ext (flip_flip g)
  map_mul' g h := Subtype.ext (by
    show flip ((g : Mat) * h) = flip g * flip h
    exact flip_mul _ _)

theorem coe_flipSL (g : SL(2, ℤ)) : ((flipSL g : SL(2, ℤ)) : Mat) = flip g := rfl

theorem flipSL_flipSL (g : SL(2, ℤ)) : flipSL (flipSL g) = g := Subtype.ext (flip_flip g)

theorem flip_conj (g : SL(2, ℤ)) (γ : Mat) : flip (conj g γ) = conj (flipSL g) (flip γ) := by
  rw [conj, conj, flip_mul, flip_mul, ← map_inv]
  rfl

theorem flipSL_mem_Gamma1 {M : ℕ} {g : SL(2, ℤ)} (hg : g ∈ Gamma1 M) : flipSL g ∈ Gamma1 M := by
  rw [Gamma1_mem] at hg ⊢
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨h1, h2, ?_⟩
  show (((-(g : Mat) 1 0 : ℤ)) : ZMod M) = 0
  push_cast
  rw [show (((g : Mat) 1 0 : ℤ) : ZMod M) = 0 from h3, neg_zero]

/-- Conjugation by `ε` on `Γ₁(M)`. -/
def flipG1 (M : ℕ) : Gamma1 M ≃* Gamma1 M where
  toFun h := ⟨flipSL h, flipSL_mem_Gamma1 h.2⟩
  invFun h := ⟨flipSL h, flipSL_mem_Gamma1 h.2⟩
  left_inv h := Subtype.ext (flipSL_flipSL h)
  right_inv h := Subtype.ext (flipSL_flipSL h)
  map_mul' g h := Subtype.ext (map_mul flipSL (g : SL(2, ℤ)) h)

/-- Elliptic `γ ∈ Δ^{(δ')}_n(M)` of trace `t` with lower-left entry `c < 0`. -/
def EllNeg (M : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) : Set Mat := {γ | flip γ ∈ EllPos M δ' t n}

/-- Explicit membership in `EllPos`. -/
theorem mem_EllPos_iff' {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} {γ : Mat} :
    γ ∈ EllPos M δ' t n ↔ γ.det = n ∧ γ.trace = t ∧ 0 < γ 1 0 ∧ t ^ 2 < 4 * n ∧
      ((γ 0 0 : ℤ) : ZMod M) = δ' ∧ ((γ 1 0 : ℤ) : ZMod M) = 0 := by
  show (γ.det = n ∧ γ.trace = t ∧ (formOf γ).PosDef ∧ ((γ 0 0 : ℤ) : ZMod M) = δ' ∧
    ((γ 1 0 : ℤ) : ZMod M) = 0) ↔ _
  rw [BQF.PosDef, disc_formOf]
  constructor
  · rintro ⟨h1, h2, ⟨h3, h4⟩, h5, h6⟩
    rw [h1, h2] at h4
    exact ⟨h1, h2, h3, by linarith, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, ⟨h3, by rw [h1, h2]; linarith⟩, h5, h6⟩

/-- Explicit membership in `EllNeg`. -/
theorem mem_EllNeg_iff' {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} {γ : Mat} :
    γ ∈ EllNeg M δ' t n ↔ γ.det = n ∧ γ.trace = t ∧ γ 1 0 < 0 ∧ t ^ 2 < 4 * n ∧
      ((γ 0 0 : ℤ) : ZMod M) = δ' ∧ ((γ 1 0 : ℤ) : ZMod M) = 0 := by
  show flip γ ∈ EllPos M δ' t n ↔ _
  rw [mem_EllPos_iff', det_flip, trace_flip, flip_apply_00, flip_apply_10]
  push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, by linarith, h4, h5, neg_eq_zero.1 h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, by linarith, h4, h5, by rw [h6, neg_zero]⟩

theorem conj_mem_EllNeg {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} {h : SL(2, ℤ)} (hh : h ∈ Gamma1 M)
    {γ : Mat} (hγ : γ ∈ EllNeg M δ' t n) : conj h γ ∈ EllNeg M δ' t n := by
  show flip (conj h γ) ∈ EllPos M δ' t n
  rw [flip_conj]
  exact ((⟨flipSL h, flipSL_mem_Gamma1 hh⟩ : Gamma1 M) • (⟨flip γ, hγ⟩ : EllPos M δ' t n)).2

/-- `Γ₁(M)` acts on `EllNeg` by conjugation. -/
instance ellNegAction (M : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    MulAction (Gamma1 M) (EllNeg M δ' t n) where
  smul h γ := ⟨conj (h : SL(2, ℤ)) γ.1, conj_mem_EllNeg h.2 γ.2⟩
  one_smul γ := Subtype.ext (conj_one γ.1)
  mul_smul g h γ := Subtype.ext (conj_mul g h γ.1)

theorem ellNeg_smul_val {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} (h : Gamma1 M) (γ : EllNeg M δ' t n) :
    ((h • γ : EllNeg M δ' t n) : Mat) = conj (h : SL(2, ℤ)) γ := rfl

/-- `γ ↦ ε γ ε` from `EllNeg` to `EllPos`. -/
def negEquiv (M : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) : EllNeg M δ' t n ≃ EllPos M δ' t n where
  toFun γ := ⟨flip γ, γ.2⟩
  invFun γ := ⟨flip γ, by show flip (flip γ.1) ∈ EllPos M δ' t n; rw [flip_flip]; exact γ.2⟩
  left_inv γ := Subtype.ext (flip_flip γ.1)
  right_inv γ := Subtype.ext (flip_flip γ.1)

/-- **Main theorem (negative orientation).** -/
theorem classSum_EllNeg (M : ℕ) [NeZero M] (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    classSum (Gamma1 M) (EllNeg M δ' t n) = ellCount M δ' t n := by
  rw [classSum_congr (flipG1 M) (negEquiv M δ' t n)
    (fun h γ => Subtype.ext (flip_conj (h : SL(2, ℤ)) γ.1)), classSum_EllPos]

theorem finite_EllNeg_quot (M : ℕ) [NeZero M] (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    Finite (MulAction.orbitRel.Quotient (Gamma1 M) (EllNeg M δ' t n)) := by
  have := finite_EllPos_quot (M := M) δ' t n
  exact Finite.of_equiv _ (quotCongr (flipG1 M) (negEquiv M δ' t n)
    (fun h γ => Subtype.ext (flip_conj (h : SL(2, ℤ)) γ.1))).symm

/-! ## A3. Imprimitive classes -/

/-- `p Q = (p a, p b, p c)`. -/
def scaleQ (p : ℤ) (Q : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (p * Q.1, p * Q.2.1, p * Q.2.2)

/-- `Q / p` (exact when `p` divides the three coefficients). -/
def unscaleQ (p : ℤ) (Q : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (Q.1 / p, Q.2.1 / p, Q.2.2 / p)

theorem disc_scaleQ (p : ℤ) (Q : ℤ × ℤ × ℤ) : (toBQF (scaleQ p Q)).disc = p ^ 2 * (toBQF Q).disc := by
  simp only [toBQF, scaleQ, BQF.disc]; ring

theorem isReduced_scaleQ_iff {p : ℤ} (hp : 0 < p) (Q : ℤ × ℤ × ℤ) :
    (toBQF (scaleQ p Q)).IsReduced ↔ (toBQF Q).IsReduced := by
  simp only [toBQF, scaleQ, BQF.IsReduced]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith, fun e => ?_⟩
    have := h4 (by rw [e])
    nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith, fun e => ?_⟩
    have := h4 (mul_left_cancel₀ hp.ne' e)
    positivity

theorem stabOrd_scaleQ {p : ℤ} (hp : p ≠ 0) (Q : ℤ × ℤ × ℤ) : stabOrd (scaleQ p Q) = stabOrd Q := by
  have e1 : ∀ x y : ℤ, p * x = p * y ↔ x = y := fun x y => mul_right_inj' hp
  have e0 : ∀ x : ℤ, p * x = 0 ↔ x = 0 := fun x => by simp [hp]
  simp only [stabOrd, scaleQ, e1, e0]

theorem unscaleQ_scaleQ {p : ℤ} (hp : p ≠ 0) (Q : ℤ × ℤ × ℤ) : unscaleQ p (scaleQ p Q) = Q := by
  simp only [unscaleQ, scaleQ, Int.mul_ediv_cancel_left _ hp]

theorem scaleQ_unscaleQ {p : ℤ} {Q : ℤ × ℤ × ℤ} (h1 : p ∣ Q.1) (h2 : p ∣ Q.2.1) (h3 : p ∣ Q.2.2) :
    scaleQ p (unscaleQ p Q) = Q := by
  simp only [unscaleQ, scaleQ, Int.mul_ediv_cancel' h1, Int.mul_ediv_cancel' h2, Int.mul_ediv_cancel' h3]

theorem gammaQ_scaleQ {Q : ℤ × ℤ × ℤ} {t : ℤ} {n : ℕ} (h : (toBQF Q).disc = t ^ 2 - 4 * n) (p : ℤ) :
    gammaQ (scaleQ p Q) (p * t) = p • gammaQ Q t := by
  obtain ⟨k, hk⟩ := two_dvd_of_disc h
  have hk' : p * t - (scaleQ p Q).2.1 = 2 * (p * k) := by
    simp only [scaleQ]; linear_combination p * hk
  rw [gammaQ_eq hk, gammaQ_eq hk']
  ext i j; fin_cases i <;> fin_cases j <;> simp [scaleQ] <;> ring

/-- `γ ∈ p M₂(ℤ)`. -/
def DvdMat (p : ℤ) (γ : Mat) : Prop := ∀ i j, p ∣ γ i j

instance decDvdMat (p : ℤ) (γ : Mat) : Decidable (DvdMat p γ) :=
  decidable_of_iff (p ∣ γ 0 0 ∧ p ∣ γ 0 1 ∧ p ∣ γ 1 0 ∧ p ∣ γ 1 1) (by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩ i j
      fin_cases i <;> fin_cases j
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · intro h; exact ⟨h 0 0, h 0 1, h 1 0, h 1 1⟩)

/-- The coefficients of `Q` are entries (or differences of entries) of `γ_Q`. -/
theorem dvd_of_dvd_gammaQ {t : ℤ} {n : ℕ} {Q : ℤ × ℤ × ℤ} (hQ : Q ∈ redForms (t ^ 2 - 4 * n)) {p : ℤ}
    (hdv : DvdMat p (gammaQ Q t)) : p ∣ Q.1 ∧ p ∣ Q.2.1 ∧ p ∣ Q.2.2 := by
  have hf := (gammaQ_props (mem_redForms.1 hQ).1).2.2
  have ea : gammaQ Q t 1 0 = Q.1 := congrArg BQF.a hf
  have eb : gammaQ Q t 1 1 - gammaQ Q t 0 0 = Q.2.1 := congrArg BQF.b hf
  have ec : -gammaQ Q t 0 1 = Q.2.2 := congrArg BQF.c hf
  refine ⟨ea ▸ hdv 1 0, eb ▸ dvd_sub (hdv 1 1) (hdv 0 0), ec ▸ (hdv 0 1).neg_right⟩

theorem map_natCast_smul (M p : ℕ) (γ : Mat) :
    ((p : ℤ) • γ).map (Int.castRingHom (ZMod M)) = (p : ZMod M) • γ.map (Int.castRingHom (ZMod M)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast]

/-- Scaling `γ` by a unit `p` mod `M` divides the eigenvalue by `p`. -/
theorem levelCount_natCast_smul (M : ℕ) [NeZero M] (δ' : ZMod M) {p : ℕ} (hpM : IsUnit (p : ZMod M))
    (γ : Mat) : levelCount M δ' ((p : ℤ) • γ) = levelCount M (δ' * (p : ZMod M)⁻¹) γ := by
  have hc : (p : ZMod M)⁻¹ * p = 1 := ZMod.inv_mul_of_unit _ hpM
  unfold levelCount
  congr 1
  refine Finset.filter_congr fun v _ => and_congr_right fun _ => ?_
  rw [map_natCast_smul, Matrix.smul_mulVec]
  constructor
  · intro h
    calc (γ.map (Int.castRingHom (ZMod M))).mulVec v
        = ((p : ZMod M)⁻¹ * p) • (γ.map (Int.castRingHom (ZMod M))).mulVec v := by rw [hc, one_smul]
      _ = (p : ZMod M)⁻¹ • ((p : ZMod M) • (γ.map (Int.castRingHom (ZMod M))).mulVec v) := mul_smul _ _ _
      _ = (δ' * (p : ZMod M)⁻¹) • v := by rw [h, smul_smul, mul_comm]
  · intro h
    rw [h, smul_smul, mul_comm δ', ← mul_assoc, mul_comm _ ((p : ZMod M)⁻¹), hc, one_mul]

/-- **Imprimitive classes.** For `p > 0` a unit mod `M`, the reduced forms `Q` of discriminant `t² - 4n` whose
matrix `γ_Q` lies in `p M₂(ℤ)` contribute `ellCount M (δ' p⁻¹) (t/p) (n/p²)` (nothing unless `p ∣ t`, `p² ∣ n`). -/
theorem ellCount_imprimitive (M : ℕ) [NeZero M] (δ' : ZMod M) (t : ℤ) (n : ℕ) {p : ℕ} (hp : 0 < p)
    (hpM : IsUnit (p : ZMod M)) :
    ∑ Q ∈ (redForms (t ^ 2 - 4 * n)).filter (fun Q => DvdMat p (gammaQ Q t)),
        (levelCount M δ' (gammaQ Q t) : ℚ) / stabOrd Q =
      if (p : ℤ) ∣ t ∧ p ^ 2 ∣ n then ellCount M (δ' * (p : ZMod M)⁻¹) (t / p) (n / p ^ 2) else 0 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpp : (0 : ℤ) < p := by exact_mod_cast hp
  split_ifs with hdiv
  · obtain ⟨⟨t', rfl⟩, ⟨n', rfl⟩⟩ := hdiv
    rw [Int.mul_ediv_cancel_left _ hp0, Nat.mul_div_cancel_left _ (pow_pos hp 2), ellCount]
    have hD : ((p : ℤ) * t') ^ 2 - 4 * (((p ^ 2 * n' : ℕ)) : ℤ) = (p : ℤ) ^ 2 * (t' ^ 2 - 4 * n') := by
      push_cast; ring
    symm
    refine Finset.sum_nbij' (scaleQ p) (unscaleQ p) ?_ ?_ ?_ ?_ ?_
    · intro Q hQ
      have hQ' := mem_redForms.1 hQ
      rw [Finset.mem_filter, mem_redForms, disc_scaleQ, hQ'.1, hD, isReduced_scaleQ_iff hpp]
      refine ⟨⟨rfl, hQ'.2⟩, ?_⟩
      intro i j
      rw [gammaQ_scaleQ hQ'.1, Matrix.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    · intro Q hQ
      rw [Finset.mem_filter] at hQ
      obtain ⟨h1, h2, h3⟩ := dvd_of_dvd_gammaQ hQ.1 hQ.2
      have hs := scaleQ_unscaleQ h1 h2 h3
      have hQ' := mem_redForms.1 hQ.1
      rw [← hs, disc_scaleQ, hD, isReduced_scaleQ_iff hpp] at hQ'
      exact mem_redForms.2 ⟨mul_left_cancel₀ (pow_ne_zero 2 hp0) hQ'.1, hQ'.2⟩
    · intro Q _
      exact unscaleQ_scaleQ hp0 Q
    · intro Q hQ
      rw [Finset.mem_filter] at hQ
      obtain ⟨h1, h2, h3⟩ := dvd_of_dvd_gammaQ hQ.1 hQ.2
      exact scaleQ_unscaleQ h1 h2 h3
    · intro Q hQ
      rw [gammaQ_scaleQ (mem_redForms.1 hQ).1, stabOrd_scaleQ hp0, levelCount_natCast_smul M δ' hpM]
  · refine Finset.sum_eq_zero fun Q hQ => ?_
    exfalso
    rw [Finset.mem_filter] at hQ
    obtain ⟨htr, hdet, -⟩ := gammaQ_props (mem_redForms.1 hQ.1).1
    have hd := hQ.2
    apply hdiv
    constructor
    · rw [← htr, Matrix.trace_fin_two]; exact dvd_add (hd 0 0) (hd 1 1)
    · have h2 : (p : ℤ) ^ 2 ∣ (n : ℤ) := by
        rw [← hdet, Matrix.det_fin_two, sq]
        exact dvd_sub (mul_dvd_mul (hd 0 0) (hd 1 1)) (mul_dvd_mul (hd 0 1) (hd 1 0))
      exact_mod_cast h2

/-! ## B3. Sanity values -/

theorem levelCount_one (γ : Mat) : levelCount 1 1 γ = 1 := by
  unfold levelCount
  rw [Finset.filter_true_of_mem]
  · rfl
  · intro v _
    refine ⟨fun d hd hd0 => ?_, Subsingleton.elim _ _⟩
    rw [Finset.mem_range] at hd
    omega

/-- `Level1Ell` of `Statements.lean`: `2 · ellCount_1(1, t, n) = H(4n - t²)`. -/
theorem level1Ell : Level1Ell := by
  intro n t ht
  have hN : (4 * (n : ℤ) - t ^ 2).toNat ≠ 0 := by omega
  have hD : -(((4 * (n : ℤ) - t ^ 2).toNat : ℕ) : ℤ) = t ^ 2 - 4 * n := by omega
  rw [hurwitzH, if_neg hN, hD, ellCount, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [levelCount_one]
  push_cast
  ring

theorem redForms_eq_image (D : ℤ) : redForms D = (reducedForms D).image fun f => (f.a, f.b, f.c) := by
  ext Q
  rw [Finset.mem_image, mem_redForms]
  constructor
  · intro h; exact ⟨toBQF Q, mem_reducedForms.2 h, rfl⟩
  · rintro ⟨f, hf, rfl⟩; exact mem_reducedForms.1 hf

theorem redForms_neg4 : redForms (-4) = {(1, 0, 1)} := by
  rw [redForms_eq_image, reducedForms_sanity.2.1, Finset.image_singleton]

theorem redForms_neg7 : redForms (-7) = {(1, 1, 2)} := by
  rw [redForms_eq_image, show reducedForms (-7) = {⟨1, 1, 2⟩} by decide, Finset.image_singleton]

theorem redForms_neg11 : redForms (-11) = {(1, 1, 3)} := by
  rw [redForms_eq_image, show reducedForms (-11) = {⟨1, 1, 3⟩} by decide, Finset.image_singleton]

/-- `ellCount 5 2 0 1 = 1` (Python mirror of the definitions). -/
theorem ellCount_5_2_0_1 : ellCount 5 2 0 1 = 1 := by
  rw [ellCount, show (0 : ℤ) ^ 2 - 4 * ((1 : ℕ) : ℤ) = -4 by norm_num, redForms_neg4, Finset.sum_singleton,
    show levelCount 5 2 (gammaQ (1, 0, 1) 0) = 4 by decide]
  norm_num [stabOrd]

/-- `ellCount 4 1 0 1 = 0`: `[[0, -1], [1, 0]]` fixes no vector of exact order `4`. -/
theorem ellCount_4_1_0_1 : ellCount 4 1 0 1 = 0 := by
  rw [ellCount, show (0 : ℤ) ^ 2 - 4 * ((1 : ℕ) : ℤ) = -4 by norm_num, redForms_neg4, Finset.sum_singleton,
    show levelCount 4 1 (gammaQ (1, 0, 1) 0) = 0 by decide]
  norm_num

theorem ellCount_4_1_neg1_2 : ellCount 4 1 (-1) 2 = 1 := by
  rw [ellCount, show (-1 : ℤ) ^ 2 - 4 * ((2 : ℕ) : ℤ) = -7 by norm_num, redForms_neg7, Finset.sum_singleton,
    show levelCount 4 1 (gammaQ (1, 1, 2) (-1)) = 2 by decide]
  norm_num [stabOrd]

theorem ellCount_5_1_neg1_3 : ellCount 5 1 (-1) 3 = 2 := by
  rw [ellCount, show (-1 : ℤ) ^ 2 - 4 * ((3 : ℕ) : ℤ) = -11 by norm_num, redForms_neg11, Finset.sum_singleton,
    show levelCount 5 1 (gammaQ (1, 1, 3) (-1)) = 4 by decide]
  norm_num [stabOrd]

end RamanujanPetersson.S3.Conj


