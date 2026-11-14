-- Prove2me | Definitions.Def_RPLib_S3_ConjClassesA
-- name    : RPLib_S3_ConjClassesA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:53:05.188434+00:00
-- url     : https://prove2.me/theorems/94ae0073-91d3-4be6-b826-109d1353a04a
-- title:
--   The Eichler-Selberg trace formula, conjugacy classes part A: fixed-point forms and level vectors
-- statement:
--   To $\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ attach the form $[c, d - a, -b]$, which is equivariant under conjugation; the action of $SL_2(\mathbb{Z})$ on $(\mathbb{Z}/M)^2$, $\Gamma_1(M)$ as the stabiliser of $e_1$, and transitivity on vectors of exact order $M$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); D. A. Buell, Binary Quadratic Forms: Classical Theory and Modern Computations, Springer 1989

import Mathlib
import Definitions.Def_RPLib_S3_Statements
import Definitions.Def_RPLib_S3_HurwitzA

/-!
# Conjugacy classes of `Δ^{(δ)}_n(M)` (unit S3-ConjClasses, part A, part A: fixed-point forms, level vectors, transitivity)
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Conj

open Matrix MatrixGroups RamanujanPetersson.Hurwitz

/-- Integer `2 × 2` matrices. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

/-- The fixed-point form `[c, d - a, -b]` of `γ = [[a, b], [c, d]]`, i.e. `v ↦ det [v, γ v]`. -/
def formOf (γ : Mat) : BQF := ⟨γ 1 0, γ 1 1 - γ 0 0, -γ 0 1⟩

theorem disc_formOf (γ : Mat) : (formOf γ).disc = γ.trace ^ 2 - 4 * γ.det := by
  simp only [formOf, BQF.disc, Matrix.trace_fin_two, Matrix.det_fin_two]; ring

/-- Conjugation `g γ g⁻¹` by `g ∈ SL(2, ℤ)`. -/
def conj (g : SL(2, ℤ)) (γ : Mat) : Mat := (g : Mat) * γ * ((g⁻¹ : SL(2, ℤ)) : Mat)

theorem coe_mul_coe_inv (g : SL(2, ℤ)) : (g : Mat) * ((g⁻¹ : SL(2, ℤ)) : Mat) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_inv_mul_coe (g : SL(2, ℤ)) : ((g⁻¹ : SL(2, ℤ)) : Mat) * (g : Mat) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

@[simp] theorem conj_one (γ : Mat) : conj 1 γ = γ := by simp [conj]

theorem conj_mul (g h : SL(2, ℤ)) (γ : Mat) : conj (g * h) γ = conj g (conj h γ) := by
  simp only [conj, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem conj_inv_conj (g : SL(2, ℤ)) (γ : Mat) : conj g⁻¹ (conj g γ) = γ := by
  rw [← conj_mul, inv_mul_cancel, conj_one]

theorem conj_conj_inv (g : SL(2, ℤ)) (γ : Mat) : conj g (conj g⁻¹ γ) = γ := by
  rw [← conj_mul, mul_inv_cancel, conj_one]

theorem trace_conj (g : SL(2, ℤ)) (γ : Mat) : (conj g γ).trace = γ.trace := by
  rw [conj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, coe_inv_mul_coe, Matrix.one_mul]

theorem det_conj (g : SL(2, ℤ)) (γ : Mat) : (conj g γ).det = γ.det := by
  rw [conj, Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]

/-- Conjugation acts on fixed-point forms by the `SL(2, ℤ)` action of `Hurwitz_A` (`g • f = act g⁻¹ f`). -/
theorem formOf_conj (g : SL(2, ℤ)) (γ : Mat) : formOf (conj g γ) = g • formOf γ := by
  rw [RamanujanPetersson.Hurwitz.smul_def]
  have h00 := inv_apply_00 g
  have h01 := inv_apply_01 g
  have h10 := inv_apply_10 g
  have h11 := inv_apply_11 g
  ext <;> simp only [formOf, conj, act, BQF.subst, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11] <;> ring

/-- Same fixed-point form and same trace force equality. -/
theorem eq_of_formOf_eq {γ γ' : Mat} (h : formOf γ = formOf γ') (ht : γ.trace = γ'.trace) : γ = γ' := by
  simp only [formOf, BQF.mk.injEq] at h
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at ht
  obtain ⟨h1, h2, h3⟩ := h
  have e00 : γ 0 0 = γ' 0 0 := by omega
  have e01 : γ 0 1 = γ' 0 1 := by omega
  have e11 : γ 1 1 = γ' 1 1 := by omega
  rw [Matrix.eta_fin_two γ, Matrix.eta_fin_two γ', e00, e01, h1, e11]

/-- A triple `(a, b, c)` as a form. -/
def toBQF (Q : ℤ × ℤ × ℤ) : BQF := ⟨Q.1, Q.2.1, Q.2.2⟩

theorem two_dvd_of_disc {Q : ℤ × ℤ × ℤ} {t : ℤ} {n : ℕ} (h : (toBQF Q).disc = t ^ 2 - 4 * n) :
    2 ∣ t - Q.2.1 := by
  simp only [toBQF, BQF.disc] at h
  have hsq : (2 : ℤ) ∣ (t - Q.2.1) ^ 2 :=
    ⟨2 * ((n : ℤ) - Q.1 * Q.2.2) - Q.2.1 * (t - Q.2.1), by linear_combination (-1 : ℤ) * h⟩
  exact Int.prime_two.dvd_of_dvd_pow hsq

theorem gammaQ_eq {Q : ℤ × ℤ × ℤ} {t k : ℤ} (hk : t - Q.2.1 = 2 * k) :
    gammaQ Q t = !![k, -Q.2.2; Q.1, k + Q.2.1] := by
  have e1 : (t - Q.2.1) / 2 = k := by rw [hk]; omega
  have e2 : (t + Q.2.1) / 2 = k + Q.2.1 := by
    have : t + Q.2.1 = 2 * (k + Q.2.1) := by linarith
    rw [this]; omega
  simp only [gammaQ, e1, e2]

theorem gammaQ_props {Q : ℤ × ℤ × ℤ} {t : ℤ} {n : ℕ} (h : (toBQF Q).disc = t ^ 2 - 4 * n) :
    (gammaQ Q t).trace = t ∧ (gammaQ Q t).det = n ∧ formOf (gammaQ Q t) = toBQF Q := by
  obtain ⟨k, hk⟩ := two_dvd_of_disc h
  rw [gammaQ_eq hk]
  simp only [toBQF, BQF.disc] at h
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.trace_fin_two]; linarith
  · simp only [Matrix.det_fin_two_of]
    have ht : t = 2 * k + Q.2.1 := by linarith
    subst ht
    nlinarith [h]
  · simp only [formOf, toBQF, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, BQF.mk.injEq]
    refine ⟨trivial, by ring, by ring⟩


/-- Membership in the enumerated `redForms` of `Statements.lean` is `disc = D` plus `Hurwitz` reducedness. -/
theorem mem_redForms {D : ℤ} {Q : ℤ × ℤ × ℤ} :
    Q ∈ redForms D ↔ (toBQF Q).disc = D ∧ (toBQF Q).IsReduced := by
  rw [redForms, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨-, h1, hD, h2, h3, h4, h5⟩
    refine ⟨by simp only [toBQF, BQF.disc]; exact hD, ?_⟩
    simp only [toBQF, BQF.IsReduced]
    exact ⟨by omega, h3, h4, fun h => by omega⟩
  · rintro ⟨hD, h1, h2, h3, h4⟩
    simp only [toBQF, BQF.disc] at hD
    simp only [toBQF] at h1 h2 h3 h4
    have hc : Q.2.2 ≤ -D := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (by omega : (0 : ℤ) ≤ Q.1 + Q.2.1),
        mul_nonneg (by omega : (0 : ℤ) ≤ Q.1) (sub_nonneg.2 h3),
        mul_nonneg (by omega : (0 : ℤ) ≤ Q.2.2) (by omega : (0 : ℤ) ≤ Q.1 - 1)]
    refine ⟨⟨⟨Q.1.toNat, (Q.2.1 + D.natAbs).toNat, Q.2.2.toNat⟩, ?_, ?_⟩, by omega, hD, by omega, h2, h3,
      by omega⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show ((Q.1.toNat : ℕ) : ℤ) = Q.1; omega
      · show (((Q.2.1 + D.natAbs).toNat : ℕ) : ℤ) - (D.natAbs : ℤ) = Q.2.1; omega
      · show ((Q.2.2.toNat : ℕ) : ℤ) = Q.2.2; omega

/-- `stabOrd` is the order of the `SL(2, ℤ)`-stabiliser of a reduced form. -/
theorem stabOrd_eq_card {Q : ℤ × ℤ × ℤ} (hQ : (toBQF Q).IsReduced) :
    (stabOrd Q : ℕ) = Nat.card (MulAction.stabilizer SL(2, ℤ) (toBQF Q)) := by
  rw [card_stabilizer_of_isReduced hQ]
  have ha := hQ.a_pos
  unfold stabOrd
  split_ifs <;> simp only [toBQF] at * <;> omega

theorem levelCount_test : levelCount 5 2 !![0, -1; 1, 0] = 4 := by decide

/-! ## A2. The level-vector action of `SL(2, ℤ)` on `(ℤ/M)²` -/

/-- Reduction mod `M` (the shape used by `levelCount`). -/
def redMat (M : ℕ) (γ : Mat) : Matrix (Fin 2) (Fin 2) (ZMod M) := γ.map (Int.castRingHom (ZMod M))

theorem redMat_mul (M : ℕ) (γ γ' : Mat) : redMat M (γ * γ') = redMat M γ * redMat M γ' :=
  Matrix.map_mul

theorem redMat_one (M : ℕ) : redMat M 1 = 1 := by simp [redMat]

/-- `SL(2, ℤ)` acts on `(ℤ/M)²` through reduction mod `M`. -/
scoped instance vecAction (M : ℕ) : MulAction SL(2, ℤ) (Fin 2 → ZMod M) where
  smul g v := redMat M (g : Mat) *ᵥ v
  one_smul v := by
    show redMat M ((1 : SL(2, ℤ)) : Mat) *ᵥ v = v
    rw [Matrix.SpecialLinearGroup.coe_one, redMat_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show redMat M ((g * h : SL(2, ℤ)) : Mat) *ᵥ v = redMat M (g : Mat) *ᵥ (redMat M (h : Mat) *ᵥ v)
    rw [Matrix.SpecialLinearGroup.coe_mul, redMat_mul, Matrix.mulVec_mulVec]

theorem vsmul_def {M : ℕ} (g : SL(2, ℤ)) (v : Fin 2 → ZMod M) : g • v = redMat M (g : Mat) *ᵥ v := rfl

/-- The level vector `e₁ = (1, 0)`. -/
def e1 (M : ℕ) : Fin 2 → ZMod M := ![1, 0]

theorem redMat_mulVec_e1 (M : ℕ) (γ : Mat) :
    redMat M γ *ᵥ e1 M = ![((γ 0 0 : ℤ) : ZMod M), ((γ 1 0 : ℤ) : ZMod M)] := by
  ext i; fin_cases i <;> simp [redMat, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `γ v = δ' v` mod `M`. -/
def Eig (M : ℕ) (δ' : ZMod M) (γ : Mat) (v : Fin 2 → ZMod M) : Prop := redMat M γ *ᵥ v = δ' • v

theorem eig_e1_iff (M : ℕ) (δ' : ZMod M) (γ : Mat) :
    Eig M δ' γ (e1 M) ↔ ((γ 0 0 : ℤ) : ZMod M) = δ' ∧ ((γ 1 0 : ℤ) : ZMod M) = 0 := by
  rw [Eig, redMat_mulVec_e1, funext_iff, Fin.forall_fin_two]
  simp [e1]

theorem smul_smul_comm' {M : ℕ} (g : SL(2, ℤ)) (c : ZMod M) (v : Fin 2 → ZMod M) :
    g • (c • v) = c • (g • v) := by
  rw [vsmul_def, vsmul_def, Matrix.mulVec_smul]

theorem smul_nsmul_comm {M : ℕ} (g : SL(2, ℤ)) (d : ℕ) (v : Fin 2 → ZMod M) :
    g • (d • v) = d • (g • v) := by
  rw [vsmul_def, vsmul_def, Matrix.mulVec_smul]

theorem redMat_conj_mulVec (M : ℕ) (g : SL(2, ℤ)) (γ : Mat) (w : Fin 2 → ZMod M) :
    redMat M (conj g γ) *ᵥ (g • w) = g • (redMat M γ *ᵥ w) := by
  have h1 : redMat M ((g⁻¹ : SL(2, ℤ)) : Mat) * redMat M (g : Mat) = 1 := by
    rw [← redMat_mul, coe_inv_mul_coe, redMat_one]
  rw [vsmul_def, vsmul_def, conj, redMat_mul, redMat_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc (redMat M (g : Mat) * redMat M γ), h1, Matrix.mul_one]

theorem eig_conj_iff {M : ℕ} (δ' : ZMod M) (g : SL(2, ℤ)) (γ : Mat) (w : Fin 2 → ZMod M) :
    Eig M δ' (conj g γ) (g • w) ↔ Eig M δ' γ w := by
  rw [Eig, Eig, redMat_conj_mulVec, ← smul_smul_comm', smul_left_cancel_iff]

/-- `Γ₁(M)` is the stabiliser of `e₁`. -/
theorem mem_Gamma1_iff (M : ℕ) (g : SL(2, ℤ)) : g ∈ CongruenceSubgroup.Gamma1 M ↔ g • e1 M = e1 M := by
  rw [CongruenceSubgroup.Gamma1_mem, vsmul_def, redMat_mulVec_e1, funext_iff, Fin.forall_fin_two]
  have hdet := det_eq g
  simp only [e1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]
  constructor
  · rintro ⟨h0, -, h2⟩; exact ⟨h0, h2⟩
  · rintro ⟨h0, h2⟩
    refine ⟨h0, ?_, h2⟩
    have : (((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℤ)) : ZMod M) = 1 := by rw [hdet]; simp
    push_cast at this
    rw [h0, h2] at this
    simpa using this

/-- Exact order `M` (the condition of `levelCount`). -/
def IsExact (M : ℕ) (v : Fin 2 → ZMod M) : Prop := ∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0

theorem isExact_smul {M : ℕ} {v : Fin 2 → ZMod M} (hv : IsExact M v) (g : SL(2, ℤ)) : IsExact M (g • v) := by
  intro d hd hd0 h
  apply hv d hd hd0
  rw [← inv_smul_smul g (d • v), smul_nsmul_comm, h, vsmul_def, Matrix.mulVec_zero]

theorem isExact_e1 (M : ℕ) : IsExact M (e1 M) := by
  intro d hd hd0 h
  have h0 := congr_fun h 0
  simp only [e1, Pi.smul_apply, Matrix.cons_val_zero, Pi.zero_apply, nsmul_eq_mul, mul_one] at h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd hd0 h0
  rw [Finset.mem_range] at hd
  omega

theorem not_dvd_of_isExact {M : ℕ} [NeZero M] {v : Fin 2 → ZMod M} (hv : IsExact M v) {p : ℕ}
    (hp : p.Prime) (hpM : p ∣ M) (h0 : p ∣ (v 0).val) (h1 : p ∣ (v 1).val) : False := by
  obtain ⟨m, hm⟩ := hpM
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hp2 := hp.two_le
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  have hmM : m < M := by rw [hm]; nlinarith
  apply hv m (Finset.mem_range.2 hmM) hm0
  have key : ∀ i, p ∣ (v i).val → m • v i = 0 := by
    rintro i ⟨k, hk⟩
    rw [← ZMod.natCast_zmod_val (v i), hk, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, hm]
    exact ⟨k, by ring⟩
  funext i
  rw [Pi.smul_apply, Pi.zero_apply]
  fin_cases i
  · exact key 0 h0
  · exact key 1 h1

theorem coprime_lift (M X Y0 : ℕ) (hX : X ≠ 0) (h : ∀ p : ℕ, p.Prime → p ∣ X → p ∣ Y0 → p ∣ M → False) :
    Nat.Coprime X (Y0 + (∏ p ∈ X.primeFactors.filter (fun p => ¬ p ∣ Y0), p) * M) := by
  apply Nat.coprime_of_dvd
  intro p hp hpX hpY
  by_cases hp0 : p ∣ Y0
  · have hpk : ¬ p ∣ ∏ q ∈ X.primeFactors.filter (fun q => ¬ q ∣ Y0), q := by
      intro hdvd
      obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).1 hdvd
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.1.1).1 hpq
      exact hq.2 (this ▸ hp0)
    have hkM : p ∣ (∏ q ∈ X.primeFactors.filter (fun q => ¬ q ∣ Y0), q) * M := (Nat.dvd_add_right hp0).1 hpY
    rcases (Nat.Prime.dvd_mul hp).1 hkM with h1 | h1
    · exact hpk h1
    · exact h p hp hpX hp0 h1
  · have hpk : p ∣ ∏ q ∈ X.primeFactors.filter (fun q => ¬ q ∣ Y0), q :=
      Finset.dvd_prod_of_mem _ (by rw [Finset.mem_filter, Nat.mem_primeFactors]; exact ⟨⟨hp, hpX, hX⟩, hp0⟩)
    exact hp0 ((Nat.dvd_add_left (dvd_mul_of_dvd_left hpk M)).1 hpY)

/-- `SL(2, ℤ)` is transitive on vectors of exact order `M`. -/
theorem exists_smul_e1 {M : ℕ} [NeZero M] {v : Fin 2 → ZMod M} (hv : IsExact M v) :
    ∃ g : SL(2, ℤ), g • e1 M = v := by
  set X0 := (v 0).val with hX0
  set Y0 := (v 1).val with hY0
  set X : ℕ := if X0 = 0 then M else X0 with hXdef
  have hX : X ≠ 0 := by
    rw [hXdef]; split_ifs with h
    · exact NeZero.ne M
    · exact h
  have hXX0 : ∀ p : ℕ, p ∣ X → p ∣ X0 := by
    intro p hp; rw [hXdef] at hp; split_ifs at hp with h
    · rw [h]; exact dvd_zero p
    · exact hp
  have hXc : (X : ZMod M) = v 0 := by
    rw [hXdef]; split_ifs with h
    · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero (v 0)).1 h).symm
    · exact ZMod.natCast_zmod_val (v 0)
  set k := ∏ p ∈ X.primeFactors.filter (fun p => ¬ p ∣ Y0), p with hk
  set Y := Y0 + k * M with hYdef
  have hYc : (Y : ZMod M) = v 1 := by
    rw [hYdef]; push_cast; rw [ZMod.natCast_self, mul_zero, add_zero, hY0, ZMod.natCast_zmod_val]
  have hcop : Nat.Coprime X Y :=
    coprime_lift M X Y0 hX (fun p hp hpX hpY hpM => not_dvd_of_isExact hv hp hpM (hXX0 p hpX) hpY)
  have hb : (X : ℤ) * Nat.gcdA X Y + (Y : ℤ) * Nat.gcdB X Y = 1 := by
    have := Nat.gcd_eq_gcd_ab X Y
    rw [hcop.gcd_eq_one] at this; push_cast at this; linarith
  refine ⟨(⟨!![(X : ℤ), -Nat.gcdB X Y; (Y : ℤ), Nat.gcdA X Y], ?_⟩ : SL(2, ℤ)), ?_⟩
  · rw [Matrix.det_fin_two_of]; linarith
  · show redMat M !![(X : ℤ), -Nat.gcdB X Y; (Y : ℤ), Nat.gcdA X Y] *ᵥ e1 M = v
    rw [redMat_mulVec_e1]
    ext i; fin_cases i
    · simp [hXc]
    · simp [hYc]

end RamanujanPetersson.S3.Conj


