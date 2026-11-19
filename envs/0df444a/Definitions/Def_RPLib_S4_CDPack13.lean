-- Prove2me | Definitions.Def_RPLib_S4_CDPack13
-- name    : RPLib_S4_CDPack13
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:25:28.950359+00:00
-- url     : https://prove2.me/theorems/239df7e8-4936-41cb-8fdc-19c690deec7b
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 13 of 71
-- statement:
--   Part 13 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CoreA_Det`: S4-CoreA part S3: kernels of endomorphisms of the divisible group through the Tate matrix
--   * `Def_RP_CoreA_Rank`: S4-CoreA part Rank: helpers for the main assembly
--   * `Def_RP_CoreA_Main`: S4-CoreA part Main: the Tate module of an `l`-primary group with a Frobenius
--   * `Def_RP_CoreA_ValZ`: S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`
--   * `Def_RP_PicDescent_E1`: S4-PicDescent, part E1: the pair `(L_n, F_n) ⊂ (L_N, F_N)` for `n ∣ N`, and extensionality tools
--   * `Def_RP_PicDescent_E2`: S4-PicDescent, part E2: the levels `F_n ⊂ F_N` (`n ∣ N`) with conorm and Frobenius
--   * `Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack11
import Definitions.Def_RPLib_S4_CDPack12

/-!
# Curve-duality library package, part 13 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CoreA_Det`: S4-CoreA part S3: kernels of endomorphisms of the divisible group through the Tate matrix
* `Def_RP_CoreA_Rank`: S4-CoreA part Rank: helpers for the main assembly
* `Def_RP_CoreA_Main`: S4-CoreA part Main: the Tate module of an `l`-primary group with a Frobenius
* `Def_RP_CoreA_ValZ`: S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`
* `Def_RP_PicDescent_E1`: S4-PicDescent, part E1: the pair `(L_n, F_n) ⊂ (L_N, F_N)` for `n ∣ N`, and extensionality tools
* `Def_RP_PicDescent_E2`: S4-PicDescent, part E2: the levels `F_n ⊂ F_N` (`n ∣ N`) with conorm and Frobenius
* `Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CoreA_Det =====
section

/-!
# S4-CoreA part S3: kernels of endomorphisms of the divisible group through the Tate matrix

For `φ` with Tate matrix `B` (`IsTateMat`), on an `l`-primary divisible `G`:
* `det B ≠ 0` ⇒ the kernel of `φ` is killed by `l ^ v(det B)` and has `l ^ v(det B)` elements;
* a finite kernel forces `det B ≠ 0`.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {G : Type*} [AddCommGroup G] {l : ℕ} [Fact l.Prime]

section Det

variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)
  (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i)
  (h1span : ∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x)

include h1inj h1span in
theorem IsTateMat.smul_eq_zero_of_map_eq_zero (htors : ∀ x : G, ∃ k, l ^ k • x = 0)
    {φ : AddMonoid.End G} {B : Matrix (Fin s) (Fin s) ℤ_[l]} (h : IsTateMat hdiv b1 hb1 φ B)
    (hdet : B.det ≠ 0) (x : G) (hx : φ x = 0) : l ^ B.det.valuation • x = 0 := by
  obtain ⟨K, hK⟩ := htors x
  obtain ⟨cb, rfl⟩ := exists_tateMap_eq hdiv b1 hb1 h1span K x hK
  have h0 : B.map (PadicInt.toZModPow K) *ᵥ cb = 0 := by
    apply tateMap_injective hdiv b1 hb1 h1inj K
    rw [← h K cb, hx, map_zero]
  have h1 : (B.map (PadicInt.toZModPow K)).det • cb = 0 := by
    have := congrArg (fun A => A *ᵥ cb) (Matrix.adjugate_mul (B.map (PadicInt.toZModPow K)))
    simp only [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this.symm
  have hdB : (B.map (PadicInt.toZModPow K)).det = PadicInt.toZModPow K (PadicInt.unitCoeff hdet : ℤ_[l]) *
      ((l : ZMod (l ^ K)) ^ B.det.valuation) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    conv_lhs => rw [PadicInt.unitCoeff_spec hdet]
    rw [map_mul, map_pow, map_natCast]
  have hu : PadicInt.toZModPow K (↑(PadicInt.unitCoeff hdet)⁻¹ : ℤ_[l]) *
      PadicInt.toZModPow K (PadicInt.unitCoeff hdet : ℤ_[l]) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((l : ZMod (l ^ K)) ^ B.det.valuation) • cb = 0 := by
    rw [hdB, mul_smul] at h1
    have := congrArg (fun v => PadicInt.toZModPow K (↑(PadicInt.unitCoeff hdet)⁻¹ : ℤ_[l]) • v) h1
    simpa only [smul_zero, smul_smul, ← mul_assoc, hu, one_mul] using this
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ K)), Nat.cast_pow, h2, map_zero]

include h1inj h1span in
/-- Kernel count: `#ker φ = l ^ v(det B)`. -/
theorem IsTateMat.card_ker (htors : ∀ x : G, ∃ k, l ^ k • x = 0)
    {φ : AddMonoid.End G} {B : Matrix (Fin s) (Fin s) ℤ_[l]} (h : IsTateMat hdiv b1 hb1 φ B)
    (hdet : B.det ≠ 0) : Nat.card {x : G // φ x = 0} = l ^ B.det.valuation := by
  rw [← JacAlg.card_ker_mod B hdet B.det.valuation le_rfl]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun cb => ⟨tateMap hdiv b1 hb1 _ cb.1, by rw [h, cb.2, map_zero]⟩) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (tateMap_injective hdiv b1 hb1 h1inj _ (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    obtain ⟨cb, hcb⟩ := exists_tateMap_eq hdiv b1 hb1 h1span _ x
      (h.smul_eq_zero_of_map_eq_zero hdiv b1 hb1 h1inj h1span htors hdet x hx)
    refine ⟨⟨cb, ?_⟩, Subtype.ext hcb⟩
    apply tateMap_injective hdiv b1 hb1 h1inj
    rw [← h, hcb, hx, map_zero]

include h1inj in
/-- A finite kernel forces a nonzero determinant. -/
theorem IsTateMat.det_ne_zero {φ : AddMonoid.End G} {B : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ B) (hfin : Finite {x : G // φ x = 0}) : B.det ≠ 0 := by
  intro hdet
  haveI := hfin
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (funext hcon)
  have hHfin : Finite (AddMonoidHom.ker (φ : G →+ G)) :=
    Finite.of_equiv {x : G // φ x = 0}
      (Equiv.subtypeEquivRight (fun x => (AddMonoidHom.mem_ker (f := (φ : G →+ G))).symm))
  have hm0 : Nat.card (AddMonoidHom.ker (φ : G →+ G)) ≠ 0 := Nat.card_pos.ne'
  have hz : ((Nat.card (AddMonoidHom.ker (φ : G →+ G)) : ℤ_[l]) * v i0) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hm0) hi0
  obtain ⟨N, hN⟩ : ∃ N, N = ((Nat.card (AddMonoidHom.ker (φ : G →+ G)) : ℤ_[l]) * v i0).valuation + 1 :=
    ⟨_, rfl⟩
  have hcb : B.map (PadicInt.toZModPow N) *ᵥ (PadicInt.toZModPow N ∘ v) = 0 := by
    ext i
    rw [← RingHom.map_mulVec, hv]
    simp
  have hx : φ (tateMap hdiv b1 hb1 N (PadicInt.toZModPow N ∘ v)) = 0 := by rw [h, hcb, map_zero]
  have hmx : Nat.card (AddMonoidHom.ker (φ : G →+ G)) • tateMap hdiv b1 hb1 N (PadicInt.toZModPow N ∘ v) = 0 := by
    have := congrArg Subtype.val
      (card_nsmul_eq_zero' (G := AddMonoidHom.ker (φ : G →+ G)) (x := ⟨_, AddMonoidHom.mem_ker.mpr hx⟩))
    exact this
  rw [← map_nsmul] at hmx
  have h3 := congrFun (tateMap_injective hdiv b1 hb1 h1inj N (hmx.trans (map_zero _).symm)) i0
  have h4 : PadicInt.toZModPow N ((Nat.card (AddMonoidHom.ker (φ : G →+ G)) : ℤ_[l]) * v i0) = 0 := by
    simpa [nsmul_eq_mul] using h3
  have h5 := (PadicInt.mem_span_pow_iff_le_valuation _ hz N).mp
    (by rw [← PadicInt.ker_toZModPow]; exact RingHom.mem_ker.mpr h4)
  omega

end Det

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_Rank =====
section

/-!
# S4-CoreA part Rank: helpers for the main assembly

`D = n • A` with the restriction `endD pi n` of `pi`; fixed points of `pi ^ m` on `D` versus `A`
(`#Fix_D ≤ #Fix_A ≤ #Fix_D * #A[n]`); the `l`-rank of an elementary abelian group; a common period
killing `A[l^k]`; and the rank identity `s = e` from the growth of fixed-point counts.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {A : Type*} [AddCommGroup A]

/-- `pi` restricted to `n • A`. -/
def endD (pi : A →+ A) (n : ℕ) : AddMonoid.End (smulHom A n).range :=
  (pi.comp (smulHom A n).range.subtype).codRestrict _ (fun x => map_mem_range_smulHom pi x.2)

theorem endD_pow_apply (pi : A →+ A) (n m : ℕ) (x : (smulHom A n).range) :
    ((endD pi n ^ m) x : A) = pi^[m] (x : A) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ_apply]
    exact ih (endD pi n x)

theorem endD_fix_iff (pi : A →+ A) (n m : ℕ) (x : (smulHom A n).range) :
    (1 - endD pi n ^ m) x = 0 ↔ pi^[m] (x : A) = x := by
  show x - (endD pi n ^ m) x = 0 ↔ pi^[m] (x : A) = x
  rw [sub_eq_zero, eq_comm, Subtype.ext_iff, endD_pow_apply]

theorem iterate_nsmul (pi : A →+ A) (m k : ℕ) (x : A) : pi^[m] (k • x) = k • pi^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_nsmul, ih]

/-- Fixed points on `D` are fixed points on `A`. -/
def fixVal (pi : A →+ A) (n m : ℕ) (x : {y : (smulHom A n).range // (1 - endD pi n ^ m) y = 0}) :
    {y : A // pi^[m] y = y} :=
  ⟨x.1, (endD_fix_iff pi n m x.1).mp x.2⟩

theorem fixVal_injective (pi : A →+ A) (n m : ℕ) : Function.Injective (fixVal pi n m) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem card_fix_le (pi : A →+ A) (n m : ℕ) [Finite {x : A // pi^[m] x = x}] :
    Finite {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} ∧
    Nat.card {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} ≤ Nat.card {x : A // pi^[m] x = x} :=
  ⟨Finite.of_injective _ (fixVal_injective pi n m), Nat.card_le_card_of_injective _ (fixVal_injective pi n m)⟩

/-- `x ↦ n • x` from fixed points on `A` to fixed points on `n • A`. -/
def fixSmul (pi : A →+ A) (n m : ℕ) (x : {y : A // pi^[m] y = y}) :
    {y : (smulHom A n).range // (1 - endD pi n ^ m) y = 0} :=
  ⟨⟨n • x.1, mem_range_smulHom.mpr ⟨x.1, rfl⟩⟩, (endD_fix_iff pi n m _).mpr (by
    show pi^[m] (n • x.1) = n • x.1
    rw [iterate_nsmul, x.2])⟩

theorem fixSmul_val (pi : A →+ A) (n m : ℕ) (x : {y : A // pi^[m] y = y}) :
    ((fixSmul pi n m x).1 : A) = n • x.1 := rfl

theorem card_fix_le_mul (pi : A →+ A) (n m : ℕ)
    [Finite {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0}] [Finite {x : A // n • x = 0}] :
    Nat.card {x : A // pi^[m] x = x} ≤
      Nat.card {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} * Nat.card {x : A // n • x = 0} := by
  have : Nonempty {x : A // pi^[m] x = x} := ⟨⟨0, Function.iterate_fixed (map_zero pi) m⟩⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : {y : (smulHom A n).range // (1 - endD pi n ^ m) y = 0} → {x : A // pi^[m] x = x},
      ∀ x, fixSmul pi n m (σ (fixSmul pi n m x)) = fixSmul pi n m x :=
    ⟨Function.invFun _, fun x => Function.invFun_eq ⟨x, rfl⟩⟩
  have hker : ∀ x : {x : A // pi^[m] x = x}, n • (x.1 - (σ (fixSmul pi n m x)).1) = 0 := by
    intro x
    have h := congrArg (fun y => ((y.1 : (smulHom A n).range) : A)) (hσ x)
    simp only [fixSmul_val] at h
    rw [smul_sub, h, sub_self]
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x => (fixSmul pi n m x, (⟨x.1 - (σ (fixSmul pi n m x)).1, hker x⟩ : {x : A // n • x = 0}))) ?_
  intro x y hxy
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  rw [h1] at h2
  exact Subtype.ext (sub_left_inj.mp h2)

/-- An elementary abelian `l`-group has order a power of `l`. -/
theorem exists_card_eq_pow_aux {l : ℕ} [Fact l.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod l) V]
    [Finite V] : ∃ s, Nat.card V = l ^ s := by
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  let _ : Fintype V := Fintype.ofFinite V
  have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
  exact ⟨Module.finrank (ZMod l) V, by rw [Nat.card_eq_fintype_card, hc, ZMod.card]⟩

theorem exists_card_eq_pow {l : ℕ} [Fact l.Prime] {V : Type*} [AddCommGroup V] [Finite V]
    (hV : ∀ x : V, l • x = 0) : ∃ s, Nat.card V = l ^ s := by
  let _ : Module (ZMod l) V := AddCommGroup.zmodModule hV
  exact exists_card_eq_pow_aux

/-- `D[l] → A[l]`. -/
def kerToTors (n l : ℕ) (x : (smulHom (smulHom A n).range l).ker) : {y : A // l • y = 0} :=
  ⟨((x : (smulHom A n).range) : A), by
    have h := x.2
    rw [AddMonoidHom.mem_ker, smulHom_apply] at h
    rw [← AddSubgroup.coe_nsmul, h, AddSubgroup.coe_zero]⟩

theorem kerToTors_injective (n l : ℕ) : Function.Injective (kerToTors (A := A) n l) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem exists_card_ker_eq_pow {l : ℕ} [Fact l.Prime] (hfin : {x : A | l • x = 0}.Finite) (n : ℕ) :
    Finite (smulHom (smulHom A n).range l).ker ∧ ∃ s, Nat.card (smulHom (smulHom A n).range l).ker = l ^ s := by
  have : Finite {y : A // l • y = 0} := hfin.to_subtype
  have hK : Finite (smulHom (smulHom A n).range l).ker := Finite.of_injective _ (kerToTors_injective n l)
  refine ⟨hK, exists_card_eq_pow (fun x => Subtype.ext ?_)⟩
  have h := x.2
  rw [AddMonoidHom.mem_ker, smulHom_apply] at h
  rw [AddSubgroup.coe_nsmul, h, AddSubgroup.coe_zero]

/-- A common period of `pi` on the finite set `A[l^k]`. -/
theorem exists_period_torsion {l : ℕ} (pi : A →+ A) (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x) (k : ℕ)
    (hfin : {x : A | l ^ k • x = 0}.Finite) : ∃ m0, 0 < m0 ∧ ∀ x : A, l ^ k • x = 0 → pi^[m0] x = x := by
  classical
  choose per hper0 hper1 using hper
  refine ⟨∏ x ∈ hfin.toFinset, per x, Finset.prod_pos (fun x _ => hper0 x), fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem per (hfin.mem_toFinset.mpr hx)
  rw [hc]
  exact Function.IsPeriodicPt.mul_const (f := pi) (hper1 x) c

section Mat

variable {G : Type*} [AddCommGroup G] {l : ℕ} (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G)
  (hb1 : ∀ i, l • b1 i = 0) (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) [Fact l.Prime]

include h1inj in
/-- If `φ` is the identity on `G[l^k]`, its Tate matrix is `1` modulo `l^k`. -/
theorem IsTateMat.map_eq_one {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (k : ℕ) (hφ : ∀ x : G, l ^ k • x = 0 → φ x = x) :
    M.map (PadicInt.toZModPow k) = 1 := by
  have hc : ∀ cb : Fin s → ZMod (l ^ k), M.map (PadicInt.toZModPow k) *ᵥ cb = cb := fun cb =>
    tateMap_injective hdiv b1 hb1 h1inj k ((h k cb).symm.trans (hφ _ (tateMap_smul_eq_zero hdiv b1 hb1 k cb)))
  ext i j
  have := congrFun (hc (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

end Mat

/-- **Rank identity.** Two-sided control `w n ≤ nu n ≤ w n + K0` of the fixed-point exponents by
`w n = v det (1 - M^n)`, together with linear growth `nu (d l^j) = C' + e j`, forces `s = e`. -/
theorem rank_eq_of_growth {l : ℕ} [hl : Fact l.Prime] {s : ℕ} (M F : Matrix (Fin s) (Fin s) ℤ_[l]) (m0 : ℕ)
    (hm0 : 0 < m0) (hM : M ^ m0 = 1 + (l ^ 2) • F) (nu : ℕ → ℕ) (e K0 : ℕ)
    (hw : ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ nu n ∧
      nu n ≤ (1 - M ^ n).det.valuation + K0)
    (hgrow : ∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d → ∃ C', ∀ j, nu (d * l ^ j) = C' + e * j) : s = e := by
  obtain ⟨d0, hd0, hg⟩ := hgrow
  obtain ⟨C', hC'⟩ := hg (d0 * m0) (Nat.mul_pos hd0 hm0) (dvd_mul_right d0 m0)
  obtain ⟨Fk, hFk⟩ := pow_eq_one_add_nsmul l hM d0
  have hX : M ^ (d0 * m0) = 1 + (l ^ 2) • Fk := by
    rw [show d0 * m0 = m0 * d0 from mul_comm _ _, pow_mul, hFk]
  have hdet := (hw (d0 * m0) (Nat.mul_pos hd0 hm0)).1
  have key : ∀ j, (1 - M ^ (d0 * m0 * l ^ j)).det.valuation = (1 - M ^ (d0 * m0)).det.valuation + s * j := by
    intro j
    rw [show M ^ (d0 * m0 * l ^ j) = (M ^ (d0 * m0)) ^ (l ^ j) from pow_mul M (d0 * m0) (l ^ j)]
    exact (det_one_sub_pow_prime_pow l hX hdet j).2
  have hb : ∀ j, (1 - M ^ (d0 * m0)).det.valuation + s * j ≤ C' + e * j ∧
      C' + e * j ≤ (1 - M ^ (d0 * m0)).det.valuation + s * j + K0 := by
    intro j
    have hpos : 0 < d0 * m0 * l ^ j := Nat.mul_pos (Nat.mul_pos hd0 hm0) (pow_pos hl.out.pos j)
    obtain ⟨-, h1, h2⟩ := hw _ hpos
    rw [key, hC'] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨h0a, h0b⟩ := hb 0
  obtain ⟨h1a, h1b⟩ := hb (K0 + 1)
  rcases lt_trichotomy s e with h | h | h
  · have h2 : (s + 1) * (K0 + 1) ≤ e * (K0 + 1) := by gcongr; omega
    nlinarith
  · exact h
  · have h2 : (e + 1) * (K0 + 1) ≤ s * (K0 + 1) := by gcongr; omega
    nlinarith

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_Main =====
section

/-!
# S4-CoreA part Main: the Tate module of an `l`-primary group with a Frobenius

Abstract form of Core A. `A` is `l`-primary torsion, `pi : A →+ A` has finite orbits, the fixed points of
`pi ^ m` number `l ^ nu m`, `nu m ≤ C + e v_l(m)`, and `nu (d l^j) = C' + e j` along `d0 ∣ d`. Then
`D = l^k0 A` is divisible with `A ⧸ D` finite (the part `Phi`), `T_l D` is free of rank `e` over `ℤ_[l]`
(coordinates `tateMap`, Frobenius matrix `M`), `v det (1 - M^n)` equals `nu n` up to the bounded `Phi`
contribution and exactly when `Phi = 0`, and `Phi = 0` iff `A` is `l`-divisible iff `#A[l] = l ^ e`.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {A : Type*} [AddCommGroup A]

theorem torsD {l : ℕ} (htors : ∀ x : A, ∃ k, l ^ k • x = 0) (n : ℕ) :
    ∀ x : (smulHom A n).range, ∃ k, l ^ k • x = 0 := fun x => by
  obtain ⟨k, hk⟩ := htors x
  exact ⟨k, Subtype.ext (by rw [AddSubgroup.coe_nsmul, hk, AddSubgroup.coe_zero])⟩

/-- On `D = n • A` every fixed point of `pi ^ m` on `A` is one on `D` when `D = A`. -/
theorem card_fix_eq_of_top (pi : A →+ A) (n m : ℕ) (htop : (smulHom A n).range = ⊤) :
    Nat.card {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} = Nat.card {x : A // pi^[m] x = x} := by
  refine Nat.card_congr (Equiv.ofBijective _ ⟨fixVal_injective pi n m, fun y => ?_⟩)
  have hy : y.1 ∈ (smulHom A n).range := by rw [htop]; exact AddSubgroup.mem_top _
  exact ⟨⟨⟨y.1, hy⟩, (endD_fix_iff pi n m _).mpr y.2⟩, rfl⟩

section Top

variable {l k0 : ℕ}
  (hk0 : ∀ j : ℕ, ∀ y : A, l • y = 0 → (∃ a, l ^ k0 • a = y) → ∃ b, l ^ (k0 + j) • b = y)
  (htors : ∀ x : A, ∃ k, l ^ k • x = 0)
include hk0 htors

theorem divD : ∀ y : (smulHom A (l ^ k0)).range, ∃ z, l • z = y := by
  intro y
  obtain ⟨z, hz, hzy⟩ := divisible hk0 htors 1 y y.2
  exact ⟨⟨z, hz⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul, ← hzy, pow_one])⟩

/-- `Phi = 0` (that is, `D = A`) iff `A` is `l`-divisible. -/
theorem range_eq_top_iff_divisible : (smulHom A (l ^ k0)).range = ⊤ ↔ ∀ y : A, ∃ z, l • z = y := by
  constructor
  · intro htop y
    obtain ⟨z, -, hz⟩ := divisible hk0 htors 1 y (by rw [htop]; exact AddSubgroup.mem_top y)
    exact ⟨z, by rw [← hz, pow_one]⟩
  · intro hd
    have hpow : ∀ k (y : A), ∃ z, l ^ k • z = y := by
      intro k
      induction k with
      | zero => exact fun y => ⟨y, by rw [pow_zero, one_smul]⟩
      | succ k ih =>
        intro y
        obtain ⟨z, hz⟩ := hd y
        obtain ⟨w, hw⟩ := ih z
        exact ⟨w, by rw [pow_succ', mul_smul, hw, hz]⟩
    exact (AddSubgroup.eq_top_iff' _).mpr fun x => mem_range_smulHom.mpr (hpow k0 x)

/-- `Phi = 0` iff `#A[l] = l ^ s`, where `#D[l] = l ^ s`. -/
theorem card_tors_iff [Fact l.Prime] (hfin : {x : A | l • x = 0}.Finite) {s : ℕ}
    (hs : Nat.card (smulHom (smulHom A (l ^ k0)).range l).ker = l ^ s) :
    Nat.card {x : A // l • x = 0} = l ^ s ↔ (smulHom A (l ^ k0)).range = ⊤ := by
  have : Finite {y : A // l • y = 0} := hfin.to_subtype
  constructor
  · intro hc
    have hbij := (kerToTors_injective (A := A) (l ^ k0) l).bijective_of_nat_card_le (by rw [hc, hs])
    rw [AddSubgroup.eq_top_iff']
    refine mem_of_torsion_le hk0 htors (fun x hx => ?_)
    obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
    have hyx : ((y : (smulHom A (l ^ k0)).range) : A) = x := congrArg Subtype.val hy
    rw [← hyx]
    exact (y : (smulHom A (l ^ k0)).range).2
  · intro htop
    rw [← hs]
    refine (Nat.card_congr (Equiv.ofBijective _ ⟨kerToTors_injective (l ^ k0) l, fun y => ?_⟩)).symm
    have hy : y.1 ∈ (smulHom A (l ^ k0)).range := by rw [htop]; exact AddSubgroup.mem_top _
    refine ⟨⟨⟨y.1, hy⟩, ?_⟩, rfl⟩
    rw [AddMonoidHom.mem_ker, smulHom_apply]
    exact Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact y.2)

end Top

/-- **Core A (abstract form).** See the module docstring. -/
theorem tate_rank {l : ℕ} [hl : Fact l.Prime] (pi : A →+ A) (nu : ℕ → ℕ) (C e : ℕ)
    (htors : ∀ x : A, ∃ k, l ^ k • x = 0)
    (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x)
    (hfix : ∀ m, 0 < m → Nat.card {x : A // pi^[m] x = x} = l ^ nu m)
    (hnu : ∀ m, 0 < m → nu m ≤ C + e * padicValNat l m)
    (hgrow : ∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d → ∃ C', ∀ j, nu (d * l ^ j) = C' + e * j) :
    ∃ (k0 : ℕ) (hdiv : ∀ y : (smulHom A (l ^ k0)).range, ∃ z, l • z = y)
      (b1 : Fin e → (smulHom A (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0) (M : Matrix (Fin e) (Fin e) ℤ_[l]),
      (∀ d : Fin e → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : (smulHom A (l ^ k0)).range, l • x = 0 → ∃ d : Fin e → ℤ, ∑ i, d i • b1 i = x) ∧
      IsTateMat hdiv b1 hb1 (endD pi (l ^ k0)) M ∧
      Finite (A ⧸ (smulHom A (l ^ k0)).range) ∧
      (∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ nu n ∧
        nu n ≤ (1 - M ^ n).det.valuation + K0) ∧
      ((smulHom A (l ^ k0)).range = ⊤ ↔ ∀ y : A, ∃ z, l • z = y) ∧
      (Nat.card {x : A // l • x = 0} = l ^ e ↔ (smulHom A (l ^ k0)).range = ⊤) ∧
      ((smulHom A (l ^ k0)).range = ⊤ → ∀ n, 0 < n → (1 - M ^ n).det.valuation = nu n) := by
  have hfin := finite_torsion_of_fix_card pi nu C e hper hfix hnu
  obtain ⟨k0, hk0⟩ := exists_stable_torsion hfin
  obtain ⟨-, s, hs⟩ := exists_card_ker_eq_pow hfin (l ^ k0)
  obtain ⟨b1, hb1, h1inj, h1span⟩ := exists_level_one_basis hs
  have hdiv := divD hk0 htors
  obtain ⟨M, hM⟩ := exists_isTateMat hdiv b1 hb1 h1inj h1span (endD pi (l ^ k0))
  have htorsD := torsD htors (l ^ k0)
  have : Finite {x : A // l ^ k0 • x = 0} := (finite_torsion_pow hfin k0).to_subtype
  obtain ⟨K0, hw⟩ : ∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ nu n ∧
      nu n ≤ (1 - M ^ n).det.valuation + K0 := by
    refine ⟨Nat.card {x : A // l ^ k0 • x = 0}, fun n hn => ?_⟩
    have hA := hfix n hn
    have : Finite {x : A // pi^[n] x = x} :=
      Nat.finite_of_card_ne_zero (by rw [hA]; exact pow_ne_zero _ hl.out.ne_zero)
    obtain ⟨hDfin, hDle⟩ := card_fix_le pi (l ^ k0) n
    have hdet := (hM.one_sub_pow hdiv b1 hb1 n).det_ne_zero hdiv b1 hb1 h1inj hDfin
    have hcard := (hM.one_sub_pow hdiv b1 hb1 n).card_ker hdiv b1 hb1 h1inj h1span htorsD hdet
    have hup := card_fix_le_mul pi (l ^ k0) n
    rw [hcard, hA] at hup
    rw [hcard, hA] at hDle
    refine ⟨hdet, (Nat.pow_le_pow_iff_right hl.out.one_lt).mp hDle, ?_⟩
    refine (Nat.pow_le_pow_iff_right hl.out.one_lt).mp (hup.trans ?_)
    rw [pow_add]
    exact Nat.mul_le_mul le_rfl (Nat.lt_pow_self hl.out.one_lt).le
  obtain ⟨m0, hm0, hm0x⟩ := exists_period_torsion pi hper 2 (finite_torsion_pow hfin 2)
  have hmap := (hM.pow hdiv b1 hb1 m0).map_eq_one hdiv b1 hb1 h1inj 2 (fun x hx => Subtype.ext (by
    rw [endD_pow_apply]
    exact hm0x _ (by rw [← AddSubgroup.coe_nsmul, hx, AddSubgroup.coe_zero])))
  obtain ⟨F, hF⟩ := exists_eq_one_add_nsmul l (M ^ m0) 2 hmap
  have hse : s = e := rank_eq_of_growth M F m0 hm0 hF nu e K0 hw hgrow
  subst hse
  refine ⟨k0, hdiv, b1, hb1, M, h1inj, h1span, hM, finite_quotient hk0 htors hfin, ⟨K0, hw⟩,
    range_eq_top_iff_divisible hk0 htors, card_tors_iff hk0 htors hfin hs, fun htop n hn => ?_⟩
  have hcard := (hM.one_sub_pow hdiv b1 hb1 n).card_ker hdiv b1 hb1 h1inj h1span htorsD (hw n hn).1
  rw [card_fix_eq_of_top pi (l ^ k0) n htop, hfix n hn] at hcard
  exact (Nat.pow_right_injective hl.out.two_le hcard).symm

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_ValZ =====
section

/-!
# S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`

`K` an algebraically closed ultrametric normed field of characteristic `0` with `‖l‖ < 1` (e.g. `PadicAlgCl l`).
`c ⊆ ℂ` a multiset with `Π_i c_i = Q` (`l ∤ Q`) and `Π_i (1 - c_i X)` the image of an integer polynomial `L`.
Let `P := reflect (#c) L`, so `P ↦ Π_i (X - c_i)` in `ℂ[X]`; `P` is monic over `ℤ`. Its roots `β_i` in `K` satisfy
`‖β_i‖ = 1`, `‖β_i ^ M - 1‖ < 1` for some `M ≥ 1` (pigeonhole on `X ^ k %ₘ P` mod `l`), and
`Π_i (1 - β_i ^ N) = Res(P, 1 - X ^ N) = Π_i (1 - c_i ^ N)` (resultant transfer).
* **`valuation_growth`**: for `h : ℕ → ℕ` with `h N = Π_i (1 - c_i ^ N) ≠ 0` (`N ≥ 1`):
  `v_l(h N) ≤ C₀ + #c v_l(N)`, and `v_l(h (d l^j)) = C' + #c j` for all `d` divisible by some `d0 ≥ 1`.
* `valuation_growth_padic`: the same with `K = PadicAlgCl l` and `Q = q ^ g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CoreA

open Polynomial

section Ultra

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_aeval_int_le_one (S : ℤ[X]) {x : K} (hx : ‖x‖ ≤ 1) : ‖aeval x S‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
  rw [zsmul_eq_mul, norm_mul, norm_pow]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _) (by positivity)
    (pow_le_one₀ (norm_nonneg _) hx)

theorem norm_le_one_of_monic {P : ℤ[X]} (hP : P.Monic) {x : K} (hx : aeval x P = 0) : ‖x‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hsum : x ^ P.natDegree = -∑ i ∈ Finset.range P.natDegree, (P.coeff i : K) * x ^ i := by
    have h1 := hx
    rw [hP.as_sum] at h1
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, algebraMap_int_eq,
      Int.coe_castRingHom] at h1
    exact eq_neg_of_add_eq_zero_left h1
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
  · rw [h0] at hsum
    simp at hsum
  obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  have hle : ‖x ^ P.natDegree‖ ≤ ‖x‖ ^ n := by
    rw [hsum, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) (fun i hi => ?_)
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n := by rw [Finset.mem_range] at hi; omega
    calc ‖(P.coeff i : K)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ n :=
          mul_le_mul (IsUltrametricDist.norm_intCast_le_one K _) (pow_le_pow_right₀ h.le hi')
            (by positivity) zero_le_one
      _ = ‖x‖ ^ n := one_mul _
  rw [norm_pow, hn, pow_succ] at hle
  have hpos : 0 < ‖x‖ ^ n := pow_pos (by linarith) n
  nlinarith

/-- Pigeonhole on the remainders `X ^ k %ₘ P` modulo `l`. -/
theorem exists_norm_pow_sub_one_lt {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {P : ℤ[X]} (hP : P.Monic)
    {x : K} (hx : aeval x P = 0) (hx1 : ‖x‖ = 1) : ∃ M, 0 < M ∧ ‖x ^ M - 1‖ < 1 := by
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun (k : ℕ) (i : Fin P.natDegree) => (((X ^ k %ₘ P).coeff i : ℤ) : ZMod l))
  have key : ∀ a b : ℕ, a < b → (∀ i : Fin P.natDegree,
      (((X ^ a %ₘ P).coeff i : ℤ) : ZMod l) = (((X ^ b %ₘ P).coeff i : ℤ) : ZMod l)) →
      ‖x ^ (b - a) - 1‖ < 1 := by
    intro a b hab hfab
    have hdvd : ∀ i, (l : ℤ) ∣ (X ^ b %ₘ P - X ^ a %ₘ P).coeff i := by
      intro i
      rw [coeff_sub]
      by_cases hi : i < P.natDegree
      · exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hfab ⟨i, hi⟩)
      · have hz : ∀ k : ℕ, (X ^ k %ₘ P).coeff i = 0 := fun k =>
          coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (degree_modByMonic_lt _ hP)
            (by rw [degree_eq_natDegree hP.ne_zero]; exact_mod_cast not_lt.mp hi))
        rw [hz, hz, sub_zero]
        exact dvd_zero _
    obtain ⟨S, hS⟩ := (C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have heval : x ^ b - x ^ a = (l : K) * aeval x S := by
      have h1 := congrArg (aeval x) hS
      rw [map_sub, aeval_modByMonic_eq_self_of_root hx, aeval_modByMonic_eq_self_of_root hx] at h1
      simp only [map_pow, aeval_X, map_mul, aeval_C] at h1
      rw [h1]
      simp
    have hxa : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    have hnorm : ‖x ^ b - x ^ a‖ < 1 := by
      rw [heval, norm_mul]
      calc ‖(l : K)‖ * ‖aeval x S‖ ≤ ‖(l : K)‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_aeval_int_le_one S hx1.le) (norm_nonneg _)
        _ < 1 := by rwa [mul_one]
    rwa [hxa, norm_mul, norm_pow, hx1, one_pow, one_mul] at hnorm
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨b - a, by omega, key a b h (fun i => congrFun hfab i)⟩
  · exact ⟨a - b, by omega, key b a h (fun i => (congrFun hfab i).symm)⟩

theorem norm_multiset_prod_map {ι : Type*} (s : Multiset ι) (f : ι → K) :
    ‖(s.map f).prod‖ = (s.map fun i => ‖f i‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

theorem norm_eq_one_of_prod {B : Multiset K} (h1 : ∀ β ∈ B, ‖β‖ ≤ 1) (hp : ‖B.prod‖ = 1) :
    ∀ β ∈ B, ‖β‖ = 1 := by
  intro β hβ
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hβ
  rw [Multiset.prod_cons, norm_mul] at hp
  have ht : ‖t.prod‖ ≤ 1 := by
    have h2 := norm_multiset_prod_map t id
    rw [Multiset.map_id] at h2
    rw [h2]
    calc (t.map fun i => ‖id i‖).prod ≤ (t.map fun _ => (1 : ℝ)).prod :=
          Multiset.prod_map_le_prod_map₀ _ _ (fun i _ => norm_nonneg _)
            (fun i hi => h1 i (Multiset.mem_cons.mpr (Or.inr hi)))
      _ = 1 := by simp
  exact le_antisymm (h1 β hβ) (by nlinarith [mul_nonneg (norm_nonneg β) (sub_nonneg.mpr ht)])

end Ultra

section Res

theorem prod_roots_one_sub_pow {F : Type*} [Field F] {P : ℤ[X]} (hP : P.Monic)
    (hs : (P.map (Int.castRingHom F)).Splits) (N : ℕ) :
    ((P.map (Int.castRingHom F)).roots.map fun β => 1 - β ^ N).prod =
      ((resultant P (1 - X ^ N) P.natDegree N : ℤ) : F) := by
  have hdeg : ((1 : ℤ[X]) - X ^ N).natDegree ≤ N := (natDegree_sub_le _ _).trans (by simp)
  have h := resultant_eq_prod_eval (P.map (Int.castRingHom F)) (((1 : ℤ[X]) - X ^ N).map (Int.castRingHom F))
    N (natDegree_map_le.trans hdeg) hs
  rw [hP.natDegree_map, resultant_map_map, (hP.map _).leadingCoeff, one_pow, one_mul, eq_intCast] at h
  rw [h]
  congr 1
  refine Multiset.map_congr rfl (fun β _ => ?_)
  simp

theorem reflect_one_sub_C_mul_X {R : Type*} [CommRing R] (a : R) : reflect 1 (1 - C a * X) = X - C a := by
  rw [reflect_sub, show (1 : R[X]) = C 1 * X ^ 0 by simp, show C a * X = C a * X ^ 1 by simp,
    reflect_C_mul_X_pow, reflect_C_mul_X_pow, revAt_le (by norm_num), revAt_le (by norm_num)]
  simp

theorem reflect_prod_one_sub {R : Type*} [CommRing R] (c : Multiset R) :
    reflect (Multiset.card c) (c.map fun r => 1 - C r * X).prod = (c.map fun r => X - C r).prod ∧
      (c.map fun r => 1 - C r * X).prod.natDegree ≤ Multiset.card c := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
    have h1 : (1 - C a * X : R[X]).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    refine ⟨?_, ?_⟩
    · rw [show Multiset.card c + 1 = 1 + Multiset.card c by omega, reflect_mul _ _ h1 ih.2, ih.1,
        reflect_one_sub_C_mul_X]
    · have h2 := ih.2
      exact natDegree_mul_le.trans (by omega)

end Res

section Main

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] [CharZero K]

/-- **V2.** Valuation bounds and exact growth for `h N = Π_i (1 - c_i ^ N)`. -/
theorem valuation_growth {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {Q : ℕ} (hQ : ¬ l ∣ Q)
    (c : Multiset ℂ) (hprod : c.prod = (Q : ℂ)) (L : ℤ[X])
    (hL : L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - C r * X).prod)
    (h : ℕ → ℕ) (hh : ∀ N, 0 < N → (h N : ℂ) = (c.map fun z => 1 - z ^ N).prod)
    (hh0 : ∀ N, 0 < N → h N ≠ 0) :
    (∃ C₀ : ℕ, ∀ N, 0 < N → padicValNat l (h N) ≤ C₀ + Multiset.card c * padicValNat l N) ∧
    (∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d →
      ∃ C', ∀ j, padicValNat l (h (d * l ^ j)) = C' + Multiset.card c * j) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : ℤ[X], P = reflect (Multiset.card c) L := ⟨_, rfl⟩
  have hPC : P.map (Int.castRingHom ℂ) = (c.map fun r => X - C r).prod := by
    rw [hPdef, ← reflect_map, hL, (reflect_prod_one_sub c).1]
  have hinjC : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hmonC : (P.map (Int.castRingHom ℂ)).Monic :=
    hPC ▸ monic_multiset_prod_of_monic _ _ (fun r _ => monic_X_sub_C r)
  have hP : P.Monic := by
    have h1 := (leadingCoeff_map_of_injective hinjC P).symm.trans hmonC.leadingCoeff
    exact hinjC (h1.trans (map_one _).symm)
  have hdeg : P.natDegree = Multiset.card c := by
    rw [← hP.natDegree_map (Int.castRingHom ℂ), hPC, natDegree_multiset_prod_X_sub_C_eq_card]
  have hrootsC : (P.map (Int.castRingHom ℂ)).roots = c := by rw [hPC, roots_multiset_prod_X_sub_C]
  have hZ : ∀ N, 0 < N → ((h N : ℕ) : ℤ) = resultant P (1 - X ^ N) P.natDegree N := by
    intro N hN
    have h1 := prod_roots_one_sub_pow (F := ℂ) hP (IsAlgClosed.splits _) N
    rw [hrootsC, ← hh N hN] at h1
    apply Int.cast_injective (α := ℂ)
    rw [← h1]
    simp
  obtain ⟨B, hB⟩ : ∃ B, B = (P.map (Int.castRingHom K)).roots := ⟨_, rfl⟩
  have hsK : (P.map (Int.castRingHom K)).Splits := IsAlgClosed.splits _
  have hcardB : Multiset.card B = Multiset.card c := by
    rw [hB, ← hsK.natDegree_eq_card_roots, hP.natDegree_map, hdeg]
  have htrans : ∀ N, 0 < N → (B.map fun β => 1 - β ^ N).prod = (h N : K) := by
    intro N hN
    rw [hB, prod_roots_one_sub_pow hP hsK N, ← hZ N hN]
    simp
  have haeval : ∀ β ∈ B, aeval β P = 0 := by
    intro β hβ
    rw [hB] at hβ
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
    exact (mem_roots (hP.map _).ne_zero).mp hβ
  have hC0 : ((P.eval 0 : ℤ) : ℂ) = (-1) ^ Multiset.card c * (Q : ℂ) := by
    have h1 := (IsAlgClosed.splits (P.map (Int.castRingHom ℂ))).eval_eq_prod_roots_of_monic (hP.map _) 0
    rw [eval_zero_map, hrootsC, eq_intCast] at h1
    rw [h1, ← hprod]
    simp
  have hP0 : P.eval 0 = (-1) ^ Multiset.card c * (Q : ℤ) :=
    Int.cast_injective (α := ℂ) (hC0.trans (by simp))
  have hBprod : B.prod = (Q : K) := by
    have h1 := hsK.eval_eq_prod_roots_of_monic (hP.map _) 0
    rw [eval_zero_map, eq_intCast, hP0, ← hB] at h1
    simp only [zero_sub, Multiset.prod_map_neg, hcardB, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast] at h1
    exact (mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h1).symm
  have hle1 : ∀ β ∈ B, ‖β‖ ≤ 1 := fun β hβ => norm_le_one_of_monic hP (haeval β hβ)
  have hQ1 : ‖(Q : K)‖ = 1 := norm_natCast_eq_one_of_not_dvd hl hl1 hQ
  have hnorm1 : ∀ β ∈ B, ‖β‖ = 1 := norm_eq_one_of_prod hle1 (by rw [hBprod, hQ1])
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hpow : ∀ β ∈ B, ∀ N, 0 < N → β ^ N ≠ 1 := by
    intro β hβ N hN hβN
    have h1 := htrans N hN
    rw [Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨β, hβ, by rw [hβN, sub_self]⟩)] at h1
    exact Nat.cast_ne_zero.mpr (hh0 N hN) h1.symm
  have hdata : ∀ β : K, ∃ d0 : ℕ, ∃ r : ℝ, β ∈ B → (0 < d0 ∧ 0 < r ∧
      (∀ n : ℕ, 0 < n → ‖β ^ (d0 * n) - 1‖ = r * ‖(n : K)‖) ∧
      (∀ N : ℕ, 0 < N → r * ‖(N : K)‖ ≤ ‖β ^ N - 1‖)) := by
    intro β
    by_cases hβ : β ∈ B
    · obtain ⟨M, hM, hM1⟩ := exists_norm_pow_sub_one_lt hl hl1 hP (haeval β hβ) (hnorm1 β hβ)
      obtain ⟨d0, hd0, r, hr, h1, h2⟩ := exists_norm_pow_sub_one_eq hl hl0 hl1 (hpow β hβ) hM hM1
      exact ⟨d0, r, fun _ => ⟨hd0, hr, h1, h2⟩⟩
    · exact ⟨1, 1, fun h' => absurd h' hβ⟩
  choose d0 r hdr using hdata
  have hρ0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hnormh : ∀ N, 0 < N →
      ‖(l : K)‖ ^ padicValNat l (h N) = (B.map fun β => ‖β ^ N - 1‖).prod := by
    intro N hN
    rw [← norm_natCast_eq_pow_padicValNat hl hl1 (hh0 N hN), ← htrans N hN, norm_multiset_prod_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl (fun β _ => norm_sub_rev _ _))
  refine ⟨?_, ?_⟩
  · have hR : 0 < (B.map r).prod := Multiset.prod_pos (fun a ha => by
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp ha
      exact (hdr β hβ).2.1)
    obtain ⟨C₀, hC₀⟩ := exists_pow_lt_of_lt_one hR hl1
    refine ⟨C₀, fun N hN => ?_⟩
    have hlow : (B.map r).prod * (‖(l : K)‖ ^ padicValNat l N) ^ Multiset.card c ≤
        ‖(l : K)‖ ^ padicValNat l (h N) := by
      rw [hnormh N hN, ← norm_natCast_eq_pow_padicValNat hl hl1 hN.ne', ← hcardB]
      calc (B.map r).prod * ‖(N : K)‖ ^ Multiset.card B
          = (B.map fun β => r β * ‖(N : K)‖).prod := by
            rw [Multiset.prod_map_mul]
            simp
        _ ≤ (B.map fun β => ‖β ^ N - 1‖).prod :=
            Multiset.prod_map_le_prod_map₀ _ _
              (fun β hβ => mul_nonneg (hdr β hβ).2.1.le (norm_nonneg _))
              (fun β hβ => (hdr β hβ).2.2.2 N hN)
    by_contra hcon
    rw [not_le] at hcon
    have h1 : ‖(l : K)‖ ^ padicValNat l (h N) ≤
        ‖(l : K)‖ ^ (C₀ + Multiset.card c * padicValNat l N) :=
      pow_le_pow_of_le_one hρ0.le hl1.le hcon.le
    rw [pow_add, pow_mul'] at h1
    have h2 : ‖(l : K)‖ ^ C₀ * (‖(l : K)‖ ^ padicValNat l N) ^ Multiset.card c <
        (B.map r).prod * (‖(l : K)‖ ^ padicValNat l N) ^ Multiset.card c :=
      mul_lt_mul_of_pos_right hC₀ (pow_pos (pow_pos hρ0 _) _)
    linarith
  · refine ⟨(B.map d0).prod, Multiset.prod_pos (fun a ha => by
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp ha
      exact (hdr β hβ).1), fun d hd hdvd => ?_⟩
    have hdβ : ∀ β ∈ B, d0 β ∣ d := fun β hβ =>
      (Multiset.dvd_prod (Multiset.mem_map_of_mem d0 hβ)).trans hdvd
    have hkey : ∀ j : ℕ, ‖(l : K)‖ ^ padicValNat l (h (d * l ^ j)) =
        (B.map fun β => r β * ‖((d / d0 β : ℕ) : K)‖).prod * (‖(l : K)‖ ^ j) ^ Multiset.card c := by
      intro j
      have hpos : 0 < d * l ^ j := Nat.mul_pos hd (pow_pos hl.pos j)
      rw [hnormh _ hpos, ← hcardB]
      calc (B.map fun β => ‖β ^ (d * l ^ j) - 1‖).prod
          = (B.map fun β => r β * ‖((d / d0 β : ℕ) : K)‖ * ‖(l : K)‖ ^ j).prod := by
            refine congrArg Multiset.prod (Multiset.map_congr rfl (fun β hβ => ?_))
            have hn : 0 < d / d0 β * l ^ j :=
              Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hd (hdβ β hβ)) (hdr β hβ).1) (pow_pos hl.pos j)
            have he : d * l ^ j = d0 β * (d / d0 β * l ^ j) := by
              rw [← mul_assoc, Nat.mul_div_cancel' (hdβ β hβ)]
            rw [he, (hdr β hβ).2.2.1 _ hn, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, mul_assoc]
        _ = _ := by
            rw [Multiset.prod_map_mul]
            simp
    refine ⟨padicValNat l (h d), fun j => ?_⟩
    have h0 := hkey 0
    simp only [pow_zero, mul_one, one_pow] at h0
    have hj := hkey j
    rw [← h0, ← pow_mul, ← pow_add] at hj
    rw [pow_right_injective₀ hρ0 hl1.ne hj, mul_comm]

end Main

/-- `‖l‖ < 1` in `PadicAlgCl l`. -/
theorem norm_prime_padicAlgCl_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p]
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have h2 : ((1 / (l : NNReal) : NNReal) : ℝ) = 1 / (l : ℝ) := by simp
  rw [h2, div_lt_one (by linarith)]
  exact h1

/-- **V2** over `PadicAlgCl l`, with `Π_i c_i = q ^ g` and `l ∤ q`. -/
theorem valuation_growth_padic {l : ℕ} [hl : Fact l.Prime] {q : ℕ} (hq : ¬ l ∣ q) (g : ℕ)
    (c : Multiset ℂ) (hprod : c.prod = (q : ℂ) ^ g) (L : ℤ[X])
    (hL : L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - C r * X).prod)
    (h : ℕ → ℕ) (hh : ∀ N, 0 < N → (h N : ℂ) = (c.map fun z => 1 - z ^ N).prod)
    (hh0 : ∀ N, 0 < N → h N ≠ 0) :
    (∃ C₀ : ℕ, ∀ N, 0 < N → padicValNat l (h N) ≤ C₀ + Multiset.card c * padicValNat l N) ∧
    (∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d →
      ∃ C', ∀ j, padicValNat l (h (d * l ^ j)) = C' + Multiset.card c * j) :=
  valuation_growth (K := PadicAlgCl l) hl.out (norm_prime_padicAlgCl_lt_one l) (Q := q ^ g)
    (fun hd => hq (hl.out.dvd_of_dvd_pow hd)) c (by rw [hprod, Nat.cast_pow]) L hL h hh hh0

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_PicDescent_E1 =====
section

/-!
# S4-PicDescent, part E1: the pair `(L_n, F_n) ⊂ (L_N, F_N)` for `n ∣ N`, and extensionality tools

* `hos_ext_ord`, `place_ext_ord`: a place is determined by its order function (and its side);
* `ringHom_ext_of_constExt`: a ring map out of `F' = L ⊗ F` is determined on `F` and on `L`;
* for `n ∣ N` (instance `Fact (n ∣ N)`): `Lc_le`, `Fc_le`, the inclusion algebras `L_n → L_N`, `F_n → F_N`,
  `L_n → F_N` with their towers, `pbLL : PowerBasis L_n L_N`, and
  **`isConstExt_pair hk : RR.IsConstExt L_n F_n L_N F_N (pbLL ..).basis`** (`F_N / F_n` is again a constant
  field extension, so all of parts C and D apply to it);
* Frobenius bookkeeping: `frobL_LL_apply` (`x ↦ x ^ (q ^ n)`), `frobL_pow_apply`, `frobL_algebraMap_LL`.
-/

set_option autoImplicit false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section ExtTools

/-- A height-one prime is determined by its order function. -/
theorem hos_ext_ord {S K : Type*} [CommRing S] [IsDedekindDomain S] [Places.FiniteQuot S] [Field K] [Algebra S K]
    [IsFractionRing S K] {P1 P2 : HeightOneSpectrum S}
    (h : ∀ f : K, Places.ord P1 f = Places.ord P2 f) : P1 = P2 := by
  have key : ∀ (P : HeightOneSpectrum S) (r : S), r ≠ 0 →
      (r ∈ P.asIdeal ↔ 0 < Places.ord P (algebraMap S K r)) := by
    intro P r hr
    have hs : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    rw [Places.ord_algebraMap P hr, Nat.cast_pos, Places.cnt, Nat.pos_iff_ne_zero,
      Associates.count_ne_zero_iff_dvd hs P.irreducible, Ideal.dvd_span_singleton]
  ext r
  by_cases hr : r = 0
  · simp [hr]
  · rw [key P1 r hr, key P2 r hr, h]

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- A place is determined by its side and its order function. -/
theorem place_ext_ord {P1 P2 : Place Fq F} (hs : P1.isLeft = P2.isLeft)
    (h : ∀ f : F, P1.ord f = P2.ord f) : P1 = P2 := by
  rcases P1 with P1 | P1 <;> rcases P2 with P2 | P2
  · exact congrArg Sum.inl (hos_ext_ord (K := F) h)
  · simp at hs
  · simp at hs
  · exact congrArg Sum.inr (hos_ext_ord (K := F) h)

variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

/-- A ring map out of `F'` is determined by its values on `F` and on `L`. -/
theorem ringHom_ext_of_constExt (h : RR.IsConstExt Fq F L F' c) {R : Type*} [Semiring R] {φ ψ : F' →+* R}
    (hF : ∀ a : F, φ (algebraMap F F' a) = ψ (algebraMap F F' a))
    (hL : ∀ l : L, φ (algebraMap L F' l) = ψ (algebraMap L F' l)) : φ = ψ := by
  ext f
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (h.span (Submodule.mem_top (x := f)))
  simp only [map_sum, Algebra.smul_def, map_mul, hF, hL]

end ExtTools

section Pair

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable {n N : ℕ}

variable {Fq Ω} in
theorem Lc_le (hnN : n ∣ N) : Lc Fq Ω n ≤ Lc Fq Ω N := by
  intro x hx
  rw [mem_Lc] at hx ⊢
  obtain ⟨k, rfl⟩ := hnN
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, pow_mul x (Fintype.card Fq ^ (n * k)) (Fintype.card Fq ^ n), ih, hx]

variable {Fq F Ω} in
theorem Fc_le (hnN : n ∣ N) : Fc Fq F Ω n ≤ Fc Fq F Ω N :=
  IntermediateField.adjoin_le_iff.2 fun _ hx => mem_Fc_of_mem_Lc (Lc_le hnN hx)

noncomputable instance algLL [Fact (n ∣ N)] : Algebra (Lc Fq Ω n) (Lc Fq Ω N) :=
  (IntermediateField.inclusion (Lc_le (Fact.out : n ∣ N))).toRingHom.toAlgebra

noncomputable instance algFF [Fact (n ∣ N)] : Algebra (Fc Fq F Ω n) (Fc Fq F Ω N) :=
  (IntermediateField.inclusion (Fc_le (Fact.out : n ∣ N))).toRingHom.toAlgebra

noncomputable instance algLF [Fact (n ∣ N)] : Algebra (Lc Fq Ω n) (Fc Fq F Ω N) :=
  ((algebraMap (Lc Fq Ω N) (Fc Fq F Ω N)).comp (algebraMap (Lc Fq Ω n) (Lc Fq Ω N))).toAlgebra

variable [Fact (n ∣ N)]

theorem coe_algebraMap_LL (x : Lc Fq Ω n) : ((algebraMap (Lc Fq Ω n) (Lc Fq Ω N) x : Lc Fq Ω N) : Ω) = x :=
  rfl

instance tower_LFF : IsScalarTower (Lc Fq Ω n) (Fc Fq F Ω n) (Fc Fq F Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance tower_LLF : IsScalarTower (Lc Fq Ω n) (Lc Fq Ω N) (Fc Fq F Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance tower_FFF : IsScalarTower F (Fc Fq F Ω n) (Fc Fq F Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance tower_qLL : IsScalarTower Fq (Lc Fq Ω n) (Lc Fq Ω N) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

variable (n N) in
/-- A power basis of `L_N` over `L_n`. -/
noncomputable def pbLL [NeZero n] [NeZero N] : PowerBasis (Lc Fq Ω n) (Lc Fq Ω N) :=
  Field.powerBasisOfFiniteOfSeparable (Lc Fq Ω n) (Lc Fq Ω N)

/-- `L_n` has `q ^ n` elements, so its Frobenius over `L_n` on `L_N` is `x ↦ x ^ (q ^ n)`. -/
theorem frobL_LL_apply [IsAlgClosed Ω] [NeZero n] [NeZero N] (x : Lc Fq Ω N) :
    frobL (Lc Fq Ω n) (Lc Fq Ω N) x = x ^ Fintype.card Fq ^ n := by
  rw [frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  show x ^ Fintype.card (Lc Fq Ω n) = _
  rw [← Nat.card_eq_fintype_card, card_Lc Fq Ω (NeZero.ne n)]

theorem frobL_pow_apply {K : Type*} [Field K] [Fintype K] [Algebra Fq K] (m : ℕ) (x : K) :
    (frobL Fq K ^ m) x = x ^ Fintype.card Fq ^ m := by
  rw [AlgEquiv.coe_pow, frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- The Frobenius of `L_N / Fq` restricts to the Frobenius of `L_n / Fq`. -/
theorem frobL_algebraMap_LL [NeZero n] [NeZero N] (x : Lc Fq Ω n) :
    frobL Fq (Lc Fq Ω N) (algebraMap (Lc Fq Ω n) (Lc Fq Ω N) x) =
      algebraMap (Lc Fq Ω n) (Lc Fq Ω N) (frobL Fq (Lc Fq Ω n) x) := by
  rw [frobL, frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic, map_pow]

end Pair

section PairFF

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]

theorem finrank_pair (hk : constField Fq F = ⊥) :
    Module.finrank (Fc Fq F Ω n) (Fc Fq F Ω N) = Module.finrank (Lc Fq Ω n) (Lc Fq Ω N) := by
  have h1 := Module.finrank_mul_finrank F (Fc Fq F Ω n) (Fc Fq F Ω N)
  have h2 := Module.finrank_mul_finrank Fq (Lc Fq Ω n) (Lc Fq Ω N)
  rw [finrank_Fc Fq F Ω hk n, finrank_Fc Fq F Ω hk N, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem hx_pair : algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) (RR.xF (Lc Fq Ω n) (Fc Fq F Ω n)) =
    RR.xF (Lc Fq Ω N) (Fc Fq F Ω N) := by
  rw [← hx_Fc Fq F Ω n, ← hx_Fc Fq F Ω N]
  exact Subtype.ext rfl

/-- **`F_N / F_n` is a constant field extension** (for `n ∣ N`). -/
theorem isConstExt_pair (hk : constField Fq F = ⊥) :
    RR.IsConstExt (Lc Fq Ω n) (Fc Fq F Ω n) (Lc Fq Ω N) (Fc Fq F Ω N) (pbLL Fq Ω n N).basis :=
  isConstExt (pbLL Fq Ω n N) (constField_Fc Fq F Ω hk n) (finrank_pair Fq F Ω hk) (hx_pair Fq F Ω)

end PairFF

end RamanujanPetersson.PicDescent

end

-- ===== S4.Def_RP_PicDescent_E2 =====
section

/-!
# S4-PicDescent, part E2: the levels `F_n ⊂ F_N` (`n ∣ N`) with conorm and Frobenius

Wrappers over parts D and E1 whose only instance binders are `NeZero` and `Fact (n ∣ N)`, so that part E3 can use
them at `n = N` without instance diamonds (never apply a generic part-D lemma to a pair with `n = N`):
* `contractNN`, `conormNN`, `conNN` (conorm on `Pic`), `conNN_trans`, `conNN_self`, `conNN_injective`, `degPic_conNN`;
* `frobN N`: the arithmetic Frobenius of `L_N / Fq` acting on `Pic(F_N)`; `frobN_conNN` (compatibility);
* `actPic_rel`: the Frobenius of `L_N / L_n` acts on `Pic(F_N)` as `(frobN N)^[n]`;
  `exists_conNN_eq` (descent from level `N` to level `n`), `frobN_iterate_conNN`.
-/

set_option autoImplicit false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

theorem isLeft_contract (P : Place L F') : (contract h P).isLeft = P.isLeft := by
  rcases P with w | w <;> rfl

theorem isLeft_plE (τ : L ≃ₐ[Fq] L) (P : Place L F') : (plE h τ P).isLeft = P.isLeft := by
  rcases P with w | w <;> rfl

theorem actPic_one (x : Pic L F') : actPic h 1 x = x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [actPic_mk, actD_one]

theorem actPic_pow (τ : L ≃ₐ[Fq] L) (k : ℕ) (x : Pic L F') : actPic h (τ ^ k) x = (actPic h τ)^[k] x := by
  induction k generalizing x with
  | zero => rw [pow_zero, actPic_one, Function.iterate_zero_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← ih, pow_succ]
    obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [actPic_mk, actPic_mk, actPic_mk, actD_mul]

end Generic

section Levels

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

/-! ### Inclusions `F_n → F_N` -/

theorem coe_algebraMap_FF {n N : ℕ} [Fact (n ∣ N)] (x : Fc Fq F Ω n) :
    ((algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) x : Fc Fq F Ω N) : Ω) = x :=
  IntermediateField.coe_inclusion (Fc_le (Fact.out : n ∣ N)) x

theorem algebraMap_FFF {n N M : ℕ} [Fact (n ∣ N)] [Fact (N ∣ M)] [Fact (n ∣ M)] (x : Fc Fq F Ω n) :
    algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) x) =
      algebraMap (Fc Fq F Ω n) (Fc Fq F Ω M) x :=
  Subtype.ext (by rw [coe_algebraMap_FF, coe_algebraMap_FF, coe_algebraMap_FF])

theorem algebraMap_FF_F {N M : ℕ} [Fact (N ∣ M)] (a : F) :
    algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap F (Fc Fq F Ω N) a) = algebraMap F (Fc Fq F Ω M) a :=
  (IsScalarTower.algebraMap_apply F (Fc Fq F Ω N) (Fc Fq F Ω M) a).symm

theorem algebraMap_FF_L {N M : ℕ} [Fact (N ∣ M)] (l : Lc Fq Ω N) :
    algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l) =
      algebraMap (Lc Fq Ω M) (Fc Fq F Ω M) (algebraMap (Lc Fq Ω N) (Lc Fq Ω M) l) :=
  (IsScalarTower.algebraMap_apply (Lc Fq Ω N) (Fc Fq F Ω N) (Fc Fq F Ω M) l).symm.trans
    (IsScalarTower.algebraMap_apply (Lc Fq Ω N) (Lc Fq Ω M) (Fc Fq F Ω M) l)

variable (Ω) in
/-- Places of one level `F_N` are determined by side and orders (instance binders: `NeZero` only). -/
theorem placeN_ext (N : ℕ) [NeZero N] {P1 P2 : Place (Lc Fq Ω N) (Fc Fq F Ω N)}
    (hs : P1.isLeft = P2.isLeft) (ho : ∀ f, P1.ord f = P2.ord f) : P1 = P2 :=
  place_ext_ord hs ho

/-! ### Wrappers -/

variable (Ω) in
/-- Contraction of places from level `N` to level `n` (`n ∣ N`). -/
noncomputable def contractNN (n N : ℕ) [NeZero n] [NeZero N] [Fact (n ∣ N)] :
    Place (Lc Fq Ω N) (Fc Fq F Ω N) → Place (Lc Fq Ω n) (Fc Fq F Ω n) :=
  contract (isConstExt_pair Fq F Ω hk (n := n) (N := N))

variable (Ω) in
/-- Conorm of divisors from level `n` to level `N` (`n ∣ N`). -/
noncomputable def conormNN (n N : ℕ) [NeZero n] [NeZero N] [Fact (n ∣ N)] :
    Divisor (Lc Fq Ω n) (Fc Fq F Ω n) →+ Divisor (Lc Fq Ω N) (Fc Fq F Ω N) :=
  conorm (isConstExt_pair Fq F Ω hk (n := n) (N := N))

variable (Ω) in
/-- **Conorm of classes** `Pic(F_n) → Pic(F_N)` (`n ∣ N`). -/
noncomputable def conNN (n N : ℕ) [NeZero n] [NeZero N] [Fact (n ∣ N)] :
    Pic (Lc Fq Ω n) (Fc Fq F Ω n) →+ Pic (Lc Fq Ω N) (Fc Fq F Ω N) :=
  conormPic (isConstExt_pair Fq F Ω hk (n := n) (N := N))

variable (Ω) in
/-- **The arithmetic Frobenius** of `L_N / Fq` acting on `Pic(F_N)`. -/
noncomputable def frobN (N : ℕ) [NeZero N] : Pic (Lc Fq Ω N) (Fc Fq F Ω N) →+ Pic (Lc Fq Ω N) (Fc Fq F Ω N) :=
  actPic (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N))

section Pair

variable {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]

theorem isLeft_contractNN (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) :
    (contractNN Ω hk n N P).isLeft = P.isLeft :=
  isLeft_contract (isConstExt_pair Fq F Ω hk (n := n) (N := N)) P

theorem ord_contractNN (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) (f : Fc Fq F Ω n) :
    (contractNN Ω hk n N P).ord f = P.ord (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω N) f) :=
  ord_contract (isConstExt_pair Fq F Ω hk (n := n) (N := N)) P f

theorem conormNN_apply (D : Divisor (Lc Fq Ω n) (Fc Fq F Ω n)) (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) :
    conormNN Ω hk n N D P = D (contractNN Ω hk n N P) :=
  conorm_apply (isConstExt_pair Fq F Ω hk (n := n) (N := N)) D P

theorem conNN_mk (D : Divisor (Lc Fq Ω n) (Fc Fq F Ω n)) :
    conNN Ω hk n N (QuotientAddGroup.mk D) =
      (QuotientAddGroup.mk (conormNN Ω hk n N D) : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) := rfl

theorem conNN_injective : Function.Injective (conNN Ω hk n N) :=
  conormPic_injective (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (constField_Fc Fq F Ω hk n)

theorem degPic_conNN (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    degPic (Lc Fq Ω N) (Fc Fq F Ω N) (conNN Ω hk n N x) = degPic (Lc Fq Ω n) (Fc Fq F Ω n) x :=
  degPic_conormPic (isConstExt_pair Fq F Ω hk (n := n) (N := N)) x

end Pair

theorem frobN_mk (N : ℕ) [NeZero N] (D : Divisor (Lc Fq Ω N) (Fc Fq F Ω N)) :
    frobN Ω hk N (QuotientAddGroup.mk D) =
      (QuotientAddGroup.mk (actD (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N)) D) :
        Pic (Lc Fq Ω N) (Fc Fq F Ω N)) := rfl

/-! ### Transitivity and the identity -/

theorem contractNN_trans {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M] [Fact (n ∣ N)] [Fact (N ∣ M)]
    [Fact (n ∣ M)] (P : Place (Lc Fq Ω M) (Fc Fq F Ω M)) :
    contractNN Ω hk n N (contractNN Ω hk N M P) = contractNN Ω hk n M P := by
  refine placeN_ext Ω n ?_ fun f => ?_
  · simp only [isLeft_contractNN]
  · rw [ord_contractNN, ord_contractNN, ord_contractNN, algebraMap_FFF]

/-- **Transitivity of conorm** for `n ∣ N ∣ M`. -/
theorem conNN_trans {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M] [Fact (n ∣ N)] [Fact (N ∣ M)]
    [Fact (n ∣ M)] (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    conNN Ω hk N M (conNN Ω hk n N x) = conNN Ω hk n M x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conNN_mk, conNN_mk, conNN_mk]
  congr 1
  ext P
  rw [conormNN_apply, conormNN_apply, conormNN_apply, contractNN_trans]

/-- (The `Fact` binder comes after `P`, so that the type of `P` is elaborated without it.) -/
theorem contractNN_self (N : ℕ) [NeZero N] (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) [Fact (N ∣ N)] :
    contractNN Ω hk N N P = P := by
  refine placeN_ext Ω N (isLeft_contractNN hk P) fun f => ?_
  rw [ord_contractNN]
  congr 1

/-- **Conorm to the same level is the identity.** -/
theorem conNN_self (N : ℕ) [NeZero N] (x : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) [Fact (N ∣ N)] :
    conNN Ω hk N N x = x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conNN_mk]
  congr 1
  ext P
  rw [conormNN_apply, contractNN_self]

/-! ### Frobenius compatibility -/

theorem frobF_conNN {N M : ℕ} [NeZero N] [NeZero M] [Fact (N ∣ M)] (f : Fc Fq F Ω N) :
    frobF (isConstExt_Fc Fq F Ω hk M) (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) f) =
      algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (frobF (isConstExt_Fc Fq F Ω hk N) f) := by
  have hF : ∀ a : F, frobF (isConstExt_Fc Fq F Ω hk M)
      (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap F (Fc Fq F Ω N) a)) =
      algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (frobF (isConstExt_Fc Fq F Ω hk N) (algebraMap F (Fc Fq F Ω N) a)) :=
    fun a => by rw [algebraMap_FF_F, AlgEquiv.commutes, AlgEquiv.commutes, algebraMap_FF_F]
  have hL : ∀ l : Lc Fq Ω N, frobF (isConstExt_Fc Fq F Ω hk M)
      (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l)) =
      algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M)
        (frobF (isConstExt_Fc Fq F Ω hk N) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l)) :=
    fun l => by
      rw [algebraMap_FF_L, frobF_algebraMap_L, frobF_algebraMap_L, frobL_algebraMap_LL, algebraMap_FF_L]
  have key := ringHom_ext_of_constExt (isConstExt_Fc Fq F Ω hk N)
    (φ := (frobF (isConstExt_Fc Fq F Ω hk M) : Fc Fq F Ω M →+* Fc Fq F Ω M).comp
      (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M)))
    (ψ := (algebraMap (Fc Fq F Ω N) (Fc Fq F Ω M)).comp
      (frobF (isConstExt_Fc Fq F Ω hk N) : Fc Fq F Ω N →+* Fc Fq F Ω N)) hF hL
  exact RingHom.congr_fun key f

theorem plE_contractNN {N M : ℕ} [NeZero N] [NeZero M] [Fact (N ∣ M)] (P : Place (Lc Fq Ω M) (Fc Fq F Ω M)) :
    contractNN Ω hk N M (plE (isConstExt_Fc Fq F Ω hk M) (frobL Fq (Lc Fq Ω M)) P) =
      plE (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N)) (contractNN Ω hk N M P) := by
  refine placeN_ext Ω N ?_ fun f => ?_
  · simp only [isLeft_contractNN, isLeft_plE]
  · rw [ord_contractNN, ord_plE, ord_plE, ord_contractNN]
    exact congrArg P.ord (frobF_conNN hk f)

/-- **Frobenius commutes with conorm.** -/
theorem frobN_conNN {N M : ℕ} [NeZero N] [NeZero M] [Fact (N ∣ M)] (x : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) :
    frobN Ω hk M (conNN Ω hk N M x) = conNN Ω hk N M (frobN Ω hk N x) := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conNN_mk, frobN_mk, frobN_mk, conNN_mk]
  congr 1
  ext P
  rw [actD_apply, conormNN_apply, conormNN_apply, actD_apply, plE_contractNN]

/-! ### The Frobenius of `L_N / L_n` and descent -/

section Rel

variable [IsAlgClosed Ω] {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]

theorem gal_rel (f : Fc Fq F Ω N) :
    gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N)) f =
      gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) f := by
  have hF : ∀ a : F, gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N))
        (algebraMap F (Fc Fq F Ω N) a) =
      gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) (algebraMap F (Fc Fq F Ω N) a) := fun a => by
    rw [IsScalarTower.algebraMap_apply F (Fc Fq F Ω n) (Fc Fq F Ω N) a, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply F (Fc Fq F Ω n) (Fc Fq F Ω N) a, AlgEquiv.commutes]
  have hL : ∀ l : Lc Fq Ω N, gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N))
        (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l) =
      gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) (algebraMap (Lc Fq Ω N) (Fc Fq F Ω N) l) := fun l => by
    rw [gal_algebraMap_L, gal_algebraMap_L, frobL_LL_apply, frobL_pow_apply]
  have key := ringHom_ext_of_constExt (isConstExt_Fc Fq F Ω hk N)
    (φ := (gal (isConstExt_pair Fq F Ω hk (n := n) (N := N)).linearIndependent
        (isConstExt_pair Fq F Ω hk (n := n) (N := N)).span (frobL (Lc Fq Ω n) (Lc Fq Ω N)) :
          Fc Fq F Ω N →+* Fc Fq F Ω N))
    (ψ := (gal (isConstExt_Fc Fq F Ω hk N).linearIndependent (isConstExt_Fc Fq F Ω hk N).span
        (frobL Fq (Lc Fq Ω N) ^ n) : Fc Fq F Ω N →+* Fc Fq F Ω N)) hF hL
  exact RingHom.congr_fun key f

theorem plE_rel (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) :
    plE (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (frobL (Lc Fq Ω n) (Lc Fq Ω N)) P =
      plE (isConstExt_Fc Fq F Ω hk N) (frobL Fq (Lc Fq Ω N) ^ n) P := by
  refine placeN_ext Ω N ?_ fun f => ?_
  · simp only [isLeft_plE]
  · rw [ord_plE, ord_plE, gal_rel hk f]

/-- **The Frobenius of `L_N / L_n` is the `n`-th power of the Frobenius of `L_N / Fq`.** -/
theorem actPic_rel (x : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) :
    actPic (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (frobL (Lc Fq Ω n) (Lc Fq Ω N)) x =
      (frobN Ω hk N)^[n] x := by
  rw [frobN, ← actPic_pow]
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [actPic_mk, actPic_mk]
  congr 1
  ext P
  rw [actD_apply, actD_apply, plE_rel hk]

/-- **Descent** from level `N` to level `n`: a class fixed by `π ^ n` comes from `Pic(F_n)`. -/
theorem exists_conNN_eq (x' : Pic (Lc Fq Ω N) (Fc Fq F Ω N)) (hx : (frobN Ω hk N)^[n] x' = x') :
    ∃ x, conNN Ω hk n N x = x' :=
  exists_conormPic_eq (isConstExt_pair Fq F Ω hk (n := n) (N := N)) (constField_Fc Fq F Ω hk n) x'
    (by rw [actPic_rel]; exact hx)

theorem frobN_iterate_conNN (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    (frobN Ω hk N)^[n] (conNN Ω hk n N x) = conNN Ω hk n N x := by
  rw [← actPic_rel]
  exact actPic_conormPic (isConstExt_pair Fq F Ω hk (n := n) (N := N)) _ x

end Rel

end Levels

end RamanujanPetersson.PicDescent

end

-- ===== S4.Def_RP_PicDescent_E3 =====
section

/-!
# S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers

`X̄ = F̄ ⊗ K` is modelled inside `Ω` (algebraically closed) as the union of the constant field extensions
`F_n = Fc Fq F Ω n`; the levels `lev j = (j+1)!` are cofinal for divisibility.
* `PicBar Ω hk`: the direct limit of `Pic(F_{lev j})` along the conorm maps `tr` (= `conNN`), i.e. `Pic(X̄)`;
* `piBar`: the arithmetic Frobenius `π` (`x ↦ x ^ q` on the constants) acting on `Pic(X̄)`;
* `degBar`, `PicBar0 = ker degBar` (`Pic⁰(X̄)`);
* `toBar m : Pic(F_m) →+ Pic(X̄)`, injective, with image `fixedBar m = Pic(X̄)^(π^m)`:
  **`picBarEquiv m : Pic(F_m) ≃+ Pic(X̄)^(π^m)`**, **`pic0BarEquiv m : Pic⁰(F_m) ≃+ Pic⁰(X̄)^(π^m)`**;
* the base level: `picBaseEquiv : Pic(F) ≃+ Pic(X̄)^π`, `pic0BaseEquiv : Pic⁰(F) ≃+ Pic⁰(X̄)^π`;
* `classNumber_bar`: `#Pic⁰(X̄)^(π^m) = h_m = L_m(1) = Π (1 - ω_i ^ m)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

/-- The levels `(j+1)!`, cofinal for divisibility. -/
def lev (j : ℕ) : ℕ := Nat.factorial (j + 1)

instance neZero_lev (j : ℕ) : NeZero (lev j) := ⟨Nat.factorial_ne_zero _⟩

theorem lev_dvd {i j : ℕ} (h : i ≤ j) : lev i ∣ lev j :=
  Nat.factorial_dvd_factorial (Nat.succ_le_succ h)

theorem dvd_lev {m j : ℕ} (hm : 0 < m) (h : m ≤ j) : m ∣ lev j :=
  Nat.dvd_factorial hm (Nat.le_succ_of_le h)

section Bar

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

variable (Fq F Ω) in
/-- `Pic(F_{(j+1)!})`. -/
abbrev PicL (j : ℕ) : Type _ := Pic (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))

variable (Ω) in
/-- The transition maps (conorm) of the directed system `j ↦ Pic(F_{(j+1)!})`. -/
noncomputable def tr (i j : ℕ) (h : i ≤ j) : PicL Fq F Ω i →+ PicL Fq F Ω j :=
  haveI : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
  conNN Ω hk (lev i) (lev j)

theorem tr_apply {i j : ℕ} (h : i ≤ j) (x : PicL Fq F Ω i) [Fact (lev i ∣ lev j)] :
    tr Ω hk i j h x = conNN Ω hk (lev i) (lev j) x := rfl

theorem tr_injective {i j : ℕ} (h : i ≤ j) : Function.Injective (tr Ω hk i j h) := by
  have : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
  intro x y hxy
  rw [tr_apply hk h x, tr_apply hk h y] at hxy
  exact conNN_injective hk hxy

instance directedSystem_tr : DirectedSystem (PicL Fq F Ω) (fun i j h => tr Ω hk i j h) where
  map_self i x := by
    have : Fact (lev i ∣ lev i) := ⟨dvd_rfl⟩
    rw [tr_apply hk le_rfl x]
    exact conNN_self hk (lev i) x
  map_map k j i hij hjk x := by
    have : Fact (lev i ∣ lev j) := ⟨lev_dvd hij⟩
    have : Fact (lev j ∣ lev k) := ⟨lev_dvd hjk⟩
    have : Fact (lev i ∣ lev k) := ⟨lev_dvd (hij.trans hjk)⟩
    rw [tr_apply hk hij x, tr_apply hk hjk, tr_apply hk (hij.trans hjk) x]
    exact conNN_trans hk x

variable (Ω) in
/-- **`Pic(X̄)`**, `X̄ = F̄ ⊗ K`: the direct limit of `Pic(F_n)` along the conorm maps. -/
abbrev PicBar : Type _ := AddCommGroup.DirectLimit (PicL Fq F Ω) (tr Ω hk)

variable (Ω) in
/-- The class of a level-`(j+1)!` divisor class in `Pic(X̄)`. -/
noncomputable abbrev ofBar (j : ℕ) : PicL Fq F Ω j →+ PicBar Ω hk :=
  AddCommGroup.DirectLimit.of (PicL Fq F Ω) (tr Ω hk) j

theorem ofBar_injective (j : ℕ) : Function.Injective (ofBar Ω hk j) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨k, hjk, h0⟩ := AddCommGroup.DirectLimit.of.zero_exact j x hx
  exact tr_injective hk hjk (h0.trans (map_zero _).symm)

/-! ### The arithmetic Frobenius on `Pic(X̄)` -/

variable (Ω) in
/-- **The arithmetic Frobenius `π`** (`x ↦ x ^ q` on the constants) acting on `Pic(X̄)`. -/
noncomputable def piBar : PicBar Ω hk →+ PicBar Ω hk :=
  AddCommGroup.DirectLimit.map (fun j => frobN Ω hk (lev j)) fun i j h => by
    refine AddMonoidHom.ext fun x => ?_
    have : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
    show frobN Ω hk (lev j) (tr Ω hk i j h x) = tr Ω hk i j h (frobN Ω hk (lev i) x)
    rw [tr_apply hk h x, tr_apply hk h]
    exact frobN_conNN hk x

theorem piBar_of (j : ℕ) (y : PicL Fq F Ω j) :
    piBar Ω hk (ofBar Ω hk j y) = ofBar Ω hk j (frobN Ω hk (lev j) y) :=
  AddCommGroup.DirectLimit.map_apply_of _ _ y

theorem piBar_iterate_of (k j : ℕ) (y : PicL Fq F Ω j) :
    (piBar Ω hk)^[k] (ofBar Ω hk j y) = ofBar Ω hk j ((frobN Ω hk (lev j))^[k] y) :=
  (Function.Semiconj.iterate_right (f := ofBar Ω hk j) (ga := frobN Ω hk (lev j)) (gb := piBar Ω hk)
    (fun y => (piBar_of hk j y).symm) k y).symm

variable (Ω) in
/-- `Pic(X̄)^(π^m)`. -/
noncomputable def fixedBar (m : ℕ) : AddSubgroup (PicBar Ω hk) where
  carrier := {x | (piBar Ω hk)^[m] x = x}
  add_mem' := fun {a b} (ha : (piBar Ω hk)^[m] a = a) (hb : (piBar Ω hk)^[m] b = b) => by
    show (piBar Ω hk)^[m] (a + b) = a + b
    rw [iterate_map_add, ha, hb]
  zero_mem' := by
    show (piBar Ω hk)^[m] 0 = 0
    exact iterate_map_zero _ _
  neg_mem' := fun {a} (ha : (piBar Ω hk)^[m] a = a) => by
    show (piBar Ω hk)^[m] (-a) = -a
    rw [iterate_map_neg, ha]

theorem mem_fixedBar (m : ℕ) (x : PicBar Ω hk) : x ∈ fixedBar Ω hk m ↔ (piBar Ω hk)^[m] x = x := Iff.rfl

/-! ### Degree and `Pic⁰(X̄)` -/

variable (Ω) in
/-- The degree on `Pic(X̄)`. -/
noncomputable def degBar : PicBar Ω hk →+ ℤ :=
  AddCommGroup.DirectLimit.lift (PicL Fq F Ω) (tr Ω hk) ℤ
    (fun j => degPic (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) fun i j h x => by
      have : Fact (lev i ∣ lev j) := ⟨lev_dvd h⟩
      rw [tr_apply hk h x]
      exact degPic_conNN hk x

theorem degBar_of (j : ℕ) (y : PicL Fq F Ω j) :
    degBar Ω hk (ofBar Ω hk j y) = degPic (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) y :=
  AddCommGroup.DirectLimit.lift_of _ _ _ j y

variable (Ω) in
/-- **`Pic⁰(X̄)`**. -/
noncomputable def PicBar0 : AddSubgroup (PicBar Ω hk) := (degBar Ω hk).ker

theorem mem_PicBar0 (z : PicBar Ω hk) : z ∈ PicBar0 Ω hk ↔ degBar Ω hk z = 0 := AddMonoidHom.mem_ker

/-! ### `Pic(F_m) → Pic(X̄)` and descent -/

variable (Ω) in
/-- `Pic(F_m) →+ Pic(X̄)`: conorm to level `(m+1)!`, then into the limit. -/
noncomputable def toBar (m : ℕ) [NeZero m] : Pic (Lc Fq Ω m) (Fc Fq F Ω m) →+ PicBar Ω hk :=
  haveI : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  (ofBar Ω hk m).comp (conNN Ω hk m (lev m))

theorem toBar_apply (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) [Fact (m ∣ lev m)] :
    toBar Ω hk m x = ofBar Ω hk m (conNN Ω hk m (lev m) x) := rfl

/-- `toBar` computed at any level `j ≥ m`. -/
theorem toBar_eq (m : ℕ) [NeZero m] {j : ℕ} (hj : m ≤ j) (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m))
    [Fact (m ∣ lev j)] : toBar Ω hk m x = ofBar Ω hk j (conNN Ω hk m (lev j) x) := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  have : Fact (lev m ∣ lev j) := ⟨lev_dvd hj⟩
  rw [toBar_apply hk m x, ← conNN_trans (N := lev m) (M := lev j) hk x, ← tr_apply hk hj]
  exact (AddCommGroup.DirectLimit.of_f hj _).symm

theorem toBar_injective (m : ℕ) [NeZero m] : Function.Injective (toBar Ω hk m) := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  intro x y hxy
  rw [toBar_apply hk m x, toBar_apply hk m y] at hxy
  exact conNN_injective hk (ofBar_injective hk m hxy)

theorem degBar_toBar (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    degBar Ω hk (toBar Ω hk m x) = degPic (Lc Fq Ω m) (Fc Fq F Ω m) x := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  rw [toBar_apply hk m x, degBar_of, degPic_conNN hk x]

theorem toBar_mem_PicBar0 (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    toBar Ω hk m x ∈ PicBar0 Ω hk ↔ x ∈ Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) := by
  rw [mem_PicBar0, degBar_toBar]
  exact AddMonoidHom.mem_ker.symm

section Descent

variable [IsAlgClosed Ω]

theorem toBar_mem (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    toBar Ω hk m x ∈ fixedBar Ω hk m := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  rw [mem_fixedBar, toBar_apply hk m x, piBar_iterate_of, frobN_iterate_conNN hk x]

/-- **Descent**: a class of `Pic(X̄)` fixed by `π ^ m` comes from `Pic(F_m)`. -/
theorem exists_toBar_eq (m : ℕ) [NeZero m] (z : PicBar Ω hk) (hz : z ∈ fixedBar Ω hk m) :
    ∃ x : Pic (Lc Fq Ω m) (Fc Fq F Ω m), toBar Ω hk m x = z := by
  revert hz
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  intro hz
  change ofBar Ω hk j y ∈ fixedBar Ω hk m at hz
  change ∃ x : Pic (Lc Fq Ω m) (Fc Fq F Ω m), toBar Ω hk m x = ofBar Ω hk j y
  have hjj : j ≤ max j m := le_max_left j m
  have hmj : m ≤ max j m := le_max_right j m
  have e : ofBar Ω hk j y = ofBar Ω hk (max j m) (tr Ω hk j (max j m) hjj y) :=
    (AddCommGroup.DirectLimit.of_f hjj y).symm
  rw [e] at hz ⊢
  generalize tr Ω hk j (max j m) hjj y = y' at hz ⊢
  rw [mem_fixedBar, piBar_iterate_of] at hz
  have hz' := ofBar_injective hk _ hz
  have : Fact (m ∣ lev (max j m)) := ⟨dvd_lev (NeZero.pos m) hmj⟩
  obtain ⟨x, hx⟩ := exists_conNN_eq hk y' hz'
  exact ⟨x, by rw [toBar_eq hk m hmj x, hx]⟩

variable (Ω) in
/-- **Galois descent for `Pic` over `X̄`**: `Pic(F_m) ≃+ Pic(X̄)^(π^m)` (`π` = arithmetic Frobenius). -/
noncomputable def picBarEquiv (m : ℕ) [NeZero m] : Pic (Lc Fq Ω m) (Fc Fq F Ω m) ≃+ fixedBar Ω hk m :=
  AddEquiv.ofBijective ((toBar Ω hk m).codRestrict (fixedBar Ω hk m) (toBar_mem hk m))
    ⟨fun x y hxy => toBar_injective hk m (congrArg Subtype.val hxy), fun z => by
      obtain ⟨x, hx⟩ := exists_toBar_eq hk m z.1 z.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem picBarEquiv_apply (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    (picBarEquiv Ω hk m x : PicBar Ω hk) = toBar Ω hk m x := rfl

variable (Ω) in
/-- **Galois descent for `Pic⁰` over `X̄`**: `Pic⁰(F_m) ≃+ Pic⁰(X̄)^(π^m)`. -/
noncomputable def pic0BarEquiv (m : ℕ) [NeZero m] :
    Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) ≃+ (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨toBar Ω hk m x.1,
          AddSubgroup.mem_inf.2 ⟨toBar_mem hk m x.1, (toBar_mem_PicBar0 hk m x.1).2 x.2⟩⟩
       map_zero' := Subtype.ext (map_zero (toBar Ω hk m))
       map_add' := fun x y => Subtype.ext (map_add (toBar Ω hk m) x.1 y.1) } :
      Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) →+ (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)))
    ⟨fun x y hxy => Subtype.ext (toBar_injective hk m (congrArg Subtype.val hxy)), fun z => by
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 z.2
      obtain ⟨x, hx⟩ := exists_toBar_eq hk m z.1 h1
      have hx0 : x ∈ Pic0 (Lc Fq Ω m) (Fc Fq F Ω m) := by
        rw [← toBar_mem_PicBar0 hk m x, hx]
        exact h2
      exact ⟨⟨x, hx0⟩, Subtype.ext hx⟩⟩

theorem pic0BarEquiv_apply (m : ℕ) [NeZero m] (x : Pic0 (Lc Fq Ω m) (Fc Fq F Ω m)) :
    (pic0BarEquiv Ω hk m x : PicBar Ω hk) = toBar Ω hk m x := rfl

/-! ### The base level `m = 1` and class numbers -/

theorem frobL_Lc_one : frobL Fq (Lc Fq Ω 1) = 1 := by
  have e := frobL_pow_finrank Fq (Lc Fq Ω 1)
  rwa [finrank_Lc Fq Ω one_ne_zero, pow_one] at e

theorem actPic_Fc_one (x : Pic (Lc Fq Ω 1) (Fc Fq F Ω 1)) :
    actPic (isConstExt_Fc Fq F Ω hk 1) (frobL Fq (Lc Fq Ω 1)) x = x := by
  rw [frobL_Lc_one, actPic_one]

variable (Ω) in
/-- `Pic(F) ≃+ Pic(F_1)` (`F_1 = F` with `L_1 = Fq`; D5 descent with trivial Frobenius). -/
noncomputable def picOneEquiv : Pic Fq F ≃+ Pic (Lc Fq Ω 1) (Fc Fq F Ω 1) :=
  AddEquiv.ofBijective (conormPic (isConstExt_Fc Fq F Ω hk 1))
    ⟨conormPic_injective _ hk, fun x' => exists_conormPic_eq _ hk x' (actPic_Fc_one hk x')⟩

variable (Ω) in
/-- `Pic⁰(F) ≃+ Pic⁰(F_1)`. -/
noncomputable def pic0OneEquiv : Pic0 Fq F ≃+ Pic0 (Lc Fq Ω 1) (Fc Fq F Ω 1) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨conormPic (isConstExt_Fc Fq F Ω hk 1) x.1,
          (conormPic_mem_Pic0_iff (isConstExt_Fc Fq F Ω hk 1) x.1).2 x.2⟩
       map_zero' := Subtype.ext (map_zero (conormPic (isConstExt_Fc Fq F Ω hk 1)))
       map_add' := fun x y => Subtype.ext (map_add (conormPic (isConstExt_Fc Fq F Ω hk 1)) x.1 y.1) } :
      Pic0 Fq F →+ Pic0 (Lc Fq Ω 1) (Fc Fq F Ω 1))
    ⟨fun x y hxy => Subtype.ext (conormPic_injective _ hk (congrArg Subtype.val hxy)), fun x' => by
      obtain ⟨x, hx⟩ := exists_conormPic_eq _ hk x'.1 (actPic_Fc_one hk x'.1)
      have hx0 : x ∈ Pic0 Fq F := by
        rw [← conormPic_mem_Pic0_iff (isConstExt_Fc Fq F Ω hk 1), hx]
        exact x'.2
      exact ⟨⟨x, hx0⟩, Subtype.ext hx⟩⟩

variable (Ω) in
/-- **`Pic(X) ≃+ Pic(X̄)^π`** for the curve `X` of `F` itself. -/
noncomputable def picBaseEquiv : Pic Fq F ≃+ fixedBar Ω hk 1 :=
  (picOneEquiv Ω hk).trans (picBarEquiv Ω hk 1)

variable (Ω) in
/-- **`Pic⁰(X) ≃+ Pic⁰(X̄)^π`**. -/
noncomputable def pic0BaseEquiv : Pic0 Fq F ≃+ (fixedBar Ω hk 1 ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) :=
  (pic0OneEquiv Ω hk).trans (pic0BarEquiv Ω hk 1)

theorem card_fixedBar0 (m : ℕ) [NeZero m] :
    Nat.card (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) =
      Nat.card (Pic0 (Lc Fq Ω m) (Fc Fq F Ω m)) :=
  (Nat.card_congr (pic0BarEquiv Ω hk m).toEquiv).symm

/-- **`h_m = #Pic⁰(X̄)^(π^m) = #Pic⁰(X_m) = L_m(1) = Π (1 - ω_i ^ m)`**, with the zeta multiset `ω` of `F`
(`|ω_i| ≤ √q`, at most `2g` of them, `N_k(F) = 1 + q^k - Σ ω_i^k`). -/
theorem classNumber_bar :
    ∃ c : Multiset ℂ, Multiset.card c ≤ 2 * RR.genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ ≤ Real.sqrt (Fintype.card Fq)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Places.numPoints Fq F k : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ k - (c.map (· ^ k)).sum) ∧
      ∀ (m : ℕ) [NeZero m], Finite (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) ∧
        (Nat.card (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) : ℂ) = (Lpoly c m).eval 1 ∧
        (Lpoly c m).eval 1 = (c.map fun z => 1 - z ^ m).prod := by
  obtain ⟨c, h1, h2, h3, h4⟩ := classNumber_Fc_zeta Ω hk
  refine ⟨c, h1, h2, h3, fun m _ => ?_⟩
  obtain ⟨hf, -, hcard, hL⟩ := h4 m
  have := hf
  exact ⟨Finite.of_equiv _ (pic0BarEquiv Ω hk m).toEquiv, by rw [card_fixedBar0, hcard], hL⟩

end Descent

end Bar

end RamanujanPetersson.PicDescent

end


