-- Prove2me | Definitions.Def_RPLib_S4_CDPack12
-- name    : RPLib_S4_CDPack12
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:15:07.883928+00:00
-- url     : https://prove2.me/theorems/c75cf98d-0848-47f3-a603-985c0f2212ab
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 12 of 71
-- statement:
--   Part 12 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacAlg_Kernel`: Core B algebra, part 6: the kernel count (unit S4-JacAlg, lemma L3 = route A2)
--   * `Def_RP_CoreA_Grow`: S4-CoreA part S4: growth of `det (1 - X ^ (l ^ j))` for `X ≡ 1 mod l ^ 2`
--   * `Def_RP_PicDescent_D4c`: S4-PicDescent, part D4c: conorm of divisors and the Galois action
--   * `Def_RP_PicDescent_H90`: S4-PicDescent, part D (H90): cyclic Hilbert 90 and norms of finite fields
--   * `Def_RP_PicDescent_D5`: S4-PicDescent, part D5: Galois descent for `Pic` and `Pic⁰` along a constant field extension
--   * `Def_RP_Kummer_InfMain`: S4-Kummer K5c: parabolic Kummer classes (main theorem)
--   * `Def_RP_CP4a_TrExact`: S4-CP4a, part d1: traces are additive along short exact sequences of free modules
--   * `Def_RP_CP4a_Les`: S4-CP4a, part d2: traces along `0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0` (constant coefficients)
--   * `Def_RP_Cone_ResCos`: S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_PicDescentD4b
import Definitions.Def_RPLib_S4_KummerInf
import Definitions.Def_RPLib_S4_CurveCohConst

/-!
# Curve-duality library package, part 12 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacAlg_Kernel`: Core B algebra, part 6: the kernel count (unit S4-JacAlg, lemma L3 = route A2)
* `Def_RP_CoreA_Grow`: S4-CoreA part S4: growth of `det (1 - X ^ (l ^ j))` for `X ≡ 1 mod l ^ 2`
* `Def_RP_PicDescent_D4c`: S4-PicDescent, part D4c: conorm of divisors and the Galois action
* `Def_RP_PicDescent_H90`: S4-PicDescent, part D (H90): cyclic Hilbert 90 and norms of finite fields
* `Def_RP_PicDescent_D5`: S4-PicDescent, part D5: Galois descent for `Pic` and `Pic⁰` along a constant field extension
* `Def_RP_Kummer_InfMain`: S4-Kummer K5c: parabolic Kummer classes (main theorem)
* `Def_RP_CP4a_TrExact`: S4-CP4a, part d1: traces are additive along short exact sequences of free modules
* `Def_RP_CP4a_Les`: S4-CP4a, part d2: traces along `0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0` (constant coefficients)
* `Def_RP_Cone_ResCos`: S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacAlg_Kernel =====
section

/-!
# Core B algebra, part 6: the kernel count (unit S4-JacAlg, lemma L3 = route A2)

* `card_quotient_range` (K1): for `f` an endomorphism of a free finite `ℤ_l`-module with `det f ≠ 0`,
  `#(M ⧸ f M) = l ^ v_l(det f)` (Smith normal form over the PID `ℤ_l`).
* `card_ker_mod` (K2): for a matrix `B` over `ℤ_l` with `det B ≠ 0` and `N ≥ v_l(det B)`, the kernel of
  `B mod l^N` on `(ℤ/l^N)^n` has `l ^ v_l(det B)` elements. With `A[l^N] ≅ (ℤ/l^N)^n` this is
  `#Ker(b on A[l^∞]) = |det T_l b|_l⁻¹` (Milne p.52).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Matrix Module

variable {l : ℕ} [hl : Fact l.Prime]

theorem card_quot_span_pow (n : ℕ) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ n}) = l ^ n := by
  rw [← PadicInt.ker_toZModPow, Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow n))).toEquiv,
    Nat.card_zmod]

theorem card_quot_span (x : ℤ_[l]) (hx : x ≠ 0) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation := by
  have e := PadicInt.unitCoeff_spec hx
  have : Ideal.span {x} = Ideal.span {(l : ℤ_[l]) ^ x.valuation} :=
    (congrArg (fun y => Ideal.span {y}) e).trans
      (Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _)
  rw [this, card_quot_span_pow]

theorem valuation_prod {ι : Type*} (s : Finset ι) (a : ι → ℤ_[l]) (ha : ∀ i ∈ s, a i ≠ 0) :
    (∏ i ∈ s, a i).valuation = ∑ i ∈ s, (a i).valuation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, PadicInt.valuation_mul (ha j (by simp))
      (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (by simp [hi])),
      ih fun i hi => ha i (by simp [hi])]

variable {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] [Module.Free ℤ_[l] M] [Module.Finite ℤ_[l] M]

theorem injective_of_det_ne_zero (f : M →ₗ[ℤ_[l]] M) (hf : LinearMap.det f ≠ 0) :
    Function.Injective f := by
  classical
  let b := Module.Free.chooseBasis ℤ_[l] M
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  have hv : (⇑(b.repr x) : _ → ℤ_[l]) ≠ 0 := fun h =>
    hne (b.repr.map_eq_zero_iff.mp (Finsupp.coe_eq_zero.mp h))
  have h1 : (LinearMap.toMatrix b b f) *ᵥ (b.repr x) = 0 := by
    rw [LinearMap.toMatrix_mulVec_repr, hx, map_zero, Finsupp.coe_zero]
  have h2 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hv, h1⟩
  rw [LinearMap.det_toMatrix] at h2
  exact hf h2

/-- K1: `#(M ⧸ f M) = l ^ v_l(det f)`. -/
theorem card_quotient_range (f : M →ₗ[ℤ_[l]] M) (hf : LinearMap.det f ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = l ^ (LinearMap.det f).valuation := by
  classical
  set N := LinearMap.range f
  let b := Module.Free.chooseBasis ℤ_[l] M
  have hinj := injective_of_det_ne_zero f hf
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] M := LinearMap.finrank_range_of_inj hinj
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[ℤ_[l]] N := b'.equiv ab (Equiv.refl _)
  have ha : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[ℤ_[l]] N)) (b' i) = a i • b' i := by
    intro i
    change (N.subtype (b'.equiv ab (Equiv.refl _) (b' i))) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet' : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[ℤ_[l]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hassoc : Associated (LinearMap.det f) (∏ i, a i) := by
    rw [← hdet']
    have hf' : f = N.subtype ∘ₗ ((LinearEquiv.ofInjective f hinj : M ≃ₗ[ℤ_[l]] N) : M →ₗ[ℤ_[l]] N) := by
      ext x; rfl
    rw [hf']
    exact LinearMap.associated_det_comp_equiv N.subtype _ _
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h
  have hp0 : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha0 i
  calc Nat.card (M ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {a i}) := by
        rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
    _ = ∏ i, l ^ (a i).valuation := Finset.prod_congr rfl fun i _ => card_quot_span _ (ha0 i)
    _ = l ^ (∑ i, (a i).valuation) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = l ^ (∏ i, a i).valuation := by rw [valuation_prod _ _ fun i _ => ha0 i]
    _ = l ^ (LinearMap.det f).valuation := by
        rw [← card_quot_span _ hp0, ← card_quot_span _ hf,
          Ideal.span_singleton_eq_span_singleton.mpr hassoc]

/-- K2: `#Ker(B mod l^N on (ℤ/l^N)^n) = l ^ v_l(det B)` for `N ≥ v_l(det B)`. -/
theorem card_ker_mod {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℤ_[l]) (hB : B.det ≠ 0)
    (N : ℕ) (hN : B.det.valuation ≤ N) :
    Nat.card {x : n → ZMod (l ^ N) // (B.map (PadicInt.toZModPow N)) *ᵥ x = 0} =
      l ^ B.det.valuation := by
  classical
  set Bb := B.map (PadicInt.toZModPow N)
  let φ : (n → ZMod (l ^ N)) →+ (n → ZMod (l ^ N)) := (Matrix.toLin' Bb).toAddMonoidHom
  let π : (n → ℤ_[l]) →+ (n → ZMod (l ^ N)) :=
    { toFun := fun v i => PadicInt.toZModPow N (v i)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hπ : Function.Surjective π := fun y =>
    ⟨fun i => (ZMod.ringHom_surjective (PadicInt.toZModPow N) (y i)).choose,
      funext fun i => (ZMod.ringHom_surjective (PadicInt.toZModPow N) (y i)).choose_spec⟩
  have hπB : ∀ v, π (B *ᵥ v) = Bb *ᵥ π v := fun v => by
    ext i; simp [π, Bb, Matrix.mulVec, dotProduct, map_sum]
  -- `l^N` is a multiple of `det B`
  obtain ⟨t, ht⟩ : B.det ∣ (l : ℤ_[l]) ^ N := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hB]
    rw [← Nat.add_sub_cancel' hN, pow_add]
    rw [mul_comm]
    exact mul_dvd_mul_left _ (Units.isUnit _).dvd
  let R : AddSubgroup (n → ℤ_[l]) := (LinearMap.range (Matrix.toLin' B)).toAddSubgroup
  have hker : ((QuotientAddGroup.mk' φ.range).comp π).ker = R := by
    ext w
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range, R, Submodule.mem_toAddSubgroup,
      LinearMap.mem_range, Matrix.toLin'_apply, φ, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨v, rfl⟩ := hπ y
      have hz : ∀ i, (w - B *ᵥ v) i ∈ Ideal.span {(l : ℤ_[l]) ^ N} := fun i => by
        rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
        have := congrFun (show π (w - B *ᵥ v) = 0 by rw [map_sub, hπB, hy, sub_self]) i
        simpa [π] using this
      choose c hc using fun i => Ideal.mem_span_singleton'.mp (hz i)
      refine ⟨v + Matrix.adjugate B *ᵥ (t • c), ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, ← ht]
      ext i; simp [hc, mul_comm]
    · rintro ⟨v, rfl⟩
      exact ⟨π v, (hπB v).symm⟩
  have hcoker : Nat.card ((n → ZMod (l ^ N)) ⧸ φ.range) = l ^ B.det.valuation := by
    have hs : Function.Surjective ((QuotientAddGroup.mk' φ.range).comp π) :=
      (QuotientAddGroup.mk'_surjective _).comp hπ
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hs).toEquiv, hker]
    have := card_quotient_range (Matrix.toLin' B) (by rwa [LinearMap.det_toLin'])
    rw [LinearMap.det_toLin'] at this
    exact this
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have e2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.range
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv] at e1
  have hr : 0 < Nat.card φ.range := Nat.card_pos
  have hk : Nat.card φ.ker = Nat.card ((n → ZMod (l ^ N)) ⧸ φ.range) :=
    Nat.eq_of_mul_eq_mul_left hr (by rw [← e1, e2, mul_comm])
  rw [← hcoker, ← hk]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp [φ, AddMonoidHom.mem_ker, Matrix.toLin'_apply])

end RamanujanPetersson.JacAlg

end

-- ===== S4.Def_RP_CoreA_Grow =====
section

/-!
# S4-CoreA part S4: growth of `det (1 - X ^ (l ^ j))` for `X ≡ 1 mod l ^ 2`

In any ring, `X = 1 + l^2 • F` gives `X ^ (l^j) - 1 = (l^j • (1 + l • U)) * (X - 1)` (geometric sums only, no
binomial theorem). For matrices over `ℤ_[l]` this yields
`v det (1 - X ^ (l^j)) = v det (1 - X) + s * j`.
-/

set_option autoImplicit false

open scoped Matrix

open Finset

namespace RamanujanPetersson.CoreA

section Ring

variable {R : Type*} [Ring R] (l : ℕ)

theorem pow_eq_one_add_nsmul {a : ℕ} {Y F : R} (hY : Y = 1 + (l ^ a) • F) (k : ℕ) :
    ∃ Fk : R, Y ^ k = 1 + (l ^ a) • Fk := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨Fk, hk⟩ := ih
    refine ⟨F + Fk + Fk * ((l ^ a) • F), ?_⟩
    rw [pow_succ, hk, hY]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, smul_add]
    abel

theorem geom_sum_eq_nsmul {a : ℕ} {Y F : R} (hY : Y = 1 + (l ^ (a + 2)) • F) :
    ∃ U : R, ∑ k ∈ range l, Y ^ k = l • (1 + l • U) := by
  choose Fk hFk using pow_eq_one_add_nsmul l hY
  refine ⟨l ^ a • ∑ k ∈ range l, Fk k, ?_⟩
  rw [sum_congr rfl (fun k _ => hFk k), sum_add_distrib, sum_const, card_range, ← smul_sum,
    smul_add, smul_smul, smul_smul]
  congr 2
  ring

theorem pow_prime_pow_sub_one {X F : R} (hX : X = 1 + (l ^ 2) • F) (j : ℕ) :
    ∃ U : R, X ^ (l ^ j) - 1 = (l ^ j • (1 + l • U)) * (X - 1) ∧
      ∃ Fj : R, X ^ (l ^ j) = 1 + l ^ (j + 2) • Fj := by
  induction j with
  | zero => exact ⟨0, by simp, F, by simpa using hX⟩
  | succ j ih =>
    obtain ⟨U, hU, Fj, hFj⟩ := ih
    obtain ⟨U', hU'⟩ := geom_sum_eq_nsmul l hFj
    have hpow : X ^ (l ^ (j + 1)) = (X ^ (l ^ j)) ^ l := by rw [pow_succ, pow_mul]
    have key : (1 + l • U') * (1 + l • U) = 1 + l • (U + U' + U' * (l • U)) := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, smul_add]
      abel
    have key2 : (l • (1 + l • U')) * (l ^ j • (1 + l • U)) =
        l ^ (j + 1) • (1 + l • (U + U' + U' * (l • U))) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, key, pow_succ, mul_comm (l ^ j) l]
    refine ⟨U + U' + U' * (l • U), ?_, (1 + l • U') * Fj, ?_⟩
    · rw [hpow, ← geom_sum_mul, hU', hU, ← mul_assoc, key2]
    · have h1 : (X ^ l ^ j) ^ l - 1 = l ^ (j + 1 + 2) • ((1 + l • U') * Fj) := by
        rw [← geom_sum_mul, hU', hFj, add_sub_cancel_left, smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1
        ring
      rw [hpow, ← h1]
      abel

end Ring

section Matrix

variable (l : ℕ) [hl : Fact l.Prime] {s : ℕ}

theorem det_one_add_nsmul (U : Matrix (Fin s) (Fin s) ℤ_[l]) :
    (1 + l • U).det ≠ 0 ∧ (1 + l • U).det.valuation = 0 := by
  have hl0 : (l : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [pow_one])
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.out.one_lt⟩
  have h0 : ∀ V : Matrix (Fin s) (Fin s) (ZMod (l ^ 1)), l • V = 0 := by
    intro V
    ext i j
    simp [nsmul_eq_mul, hl0]
  have hmap : PadicInt.toZModPow 1 (1 + l • U).det = 1 := by
    rw [RingHom.map_det, map_add, map_one, map_nsmul, h0, add_zero, Matrix.det_one]
  have hne : (1 + l • U).det ≠ 0 := by
    intro h
    rw [h, map_zero] at hmap
    exact zero_ne_one hmap
  refine ⟨hne, ?_⟩
  by_contra hv
  have hmem := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).mpr (by omega)
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker] at hmem
  rw [hmem] at hmap
  exact zero_ne_one hmap

/-- Growth along `l`-power multiples: `v det (1 - X^(l^j)) = v det (1 - X) + s j`. -/
theorem det_one_sub_pow_prime_pow {X F : Matrix (Fin s) (Fin s) ℤ_[l]} (hX : X = 1 + (l ^ 2) • F)
    (hdet : (1 - X).det ≠ 0) (j : ℕ) :
    (1 - X ^ (l ^ j)).det ≠ 0 ∧ (1 - X ^ (l ^ j)).det.valuation = (1 - X).det.valuation + s * j := by
  obtain ⟨U, hU, -⟩ := pow_prime_pow_sub_one l hX j
  have e : 1 - X ^ (l ^ j) = (((l ^ j : ℕ) : ℤ_[l]) • (1 + l • U)) * (1 - X) := by
    rw [Nat.cast_smul_eq_nsmul, ← neg_sub X 1, ← neg_sub (X ^ l ^ j) 1, hU, mul_neg]
  have hdet_e : (1 - X ^ (l ^ j)).det = ((l : ℤ_[l]) ^ j) ^ s * ((1 + l • U).det * (1 - X).det) := by
    rw [e, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Nat.cast_pow, mul_assoc]
  obtain ⟨hne, hv0⟩ := det_one_add_nsmul l U
  have hlj : ((l : ℤ_[l]) ^ j) ^ s ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero))
  refine ⟨?_, ?_⟩
  · rw [hdet_e]
    exact mul_ne_zero hlj (mul_ne_zero hne hdet)
  · rw [hdet_e, PadicInt.valuation_mul hlj (mul_ne_zero hne hdet), PadicInt.valuation_mul hne hdet, hv0,
      ← pow_mul, PadicInt.valuation_pow, PadicInt.valuation_p]
    ring

/-- A matrix that is `1` modulo `l ^ k` has the form `1 + l^k • F`. -/
theorem exists_eq_one_add_nsmul (A : Matrix (Fin s) (Fin s) ℤ_[l]) (k : ℕ)
    (hA : A.map (PadicInt.toZModPow k) = 1) : ∃ F : Matrix (Fin s) (Fin s) ℤ_[l], A = 1 + (l ^ k) • F := by
  have h : ∀ i j, ∃ f : ℤ_[l], (A - 1) i j = (l : ℤ_[l]) ^ k * f := by
    intro i j
    have hmem : (A - 1) i j ∈ RingHom.ker (PadicInt.toZModPow (p := l) k) := by
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
      have h1 := congrFun (congrFun hA i) j
      rw [Matrix.map_apply] at h1
      rw [h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    exact hmem
  choose F hF using h
  refine ⟨Matrix.of F, ?_⟩
  ext i j
  have := hF i j
  rw [Matrix.sub_apply] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_pow, ← this]
  abel

end Matrix

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_PicDescent_D4c =====
section

/-!
# S4-PicDescent, part D4c: conorm of divisors and the Galois action

For `h : RR.IsConstExt Fq F L F' c`:
* `conorm h : Divisor Fq F →+ Divisor L F'`, `conorm h D P' = D (P' ∩ F)`; `conorm_div` (`ι (div f) = div f'`),
  `deg_conorm` (`deg ι D = deg D`), `conorm_injective`.
* `actD h τ : Divisor L F' ≃+ Divisor L F'`, `(actD τ D) P' = D (τ⁻¹ P')`; `div_gal` (`div (gal τ f) = actD τ (div f)`),
  `actD_conorm` (conorms are invariant), `exists_conorm_eq` (invariant divisors are conorms).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Conorm

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

/-- **Conorm** `ι D (P') = D (P' ∩ F)`. -/
noncomputable def conorm : Divisor Fq F →+ Divisor L F' where
  toFun D := by
    classical
    exact Finsupp.onFinset (D.support.biUnion (fibre h)) (fun P' => D (contract h P')) (fun P' hP' =>
      Finset.mem_biUnion.2 ⟨contract h P', Finsupp.mem_support_iff.2 hP', (mem_fibre h _ _).2 rfl⟩)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp

theorem conorm_apply (D : Divisor Fq F) (P' : Place L F') : conorm h D P' = D (contract h P') := by
  simp [conorm]

/-- **`ι (div f) = div f'`**. -/
theorem conorm_div (f : F) : conorm h (div f) = div (algebraMap F F' f) := by
  ext P'
  rw [conorm_apply, div_apply, div_apply, ord_contract]

theorem conorm_single (P : Place Fq F) (n : ℤ) :
    conorm h (Finsupp.single P n) = ∑ P' ∈ fibre h P, Finsupp.single P' n := by
  classical
  ext P'
  rw [conorm_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hc : contract h P' = P
  · rw [if_pos ((mem_fibre h P P').2 hc), if_pos hc.symm]
  · rw [if_neg (fun hm => hc ((mem_fibre h P P').1 hm)), if_neg (Ne.symm hc)]

/-- **`deg ι D = deg D`**. -/
theorem deg_conorm (D : Divisor Fq F) : Divisor.deg (conorm h D) = Divisor.deg D := by
  induction D using Finsupp.induction with
  | zero => simp [Divisor.deg]
  | single_add P n D _ _ ih =>
    rw [map_add, Divisor.deg_add, Divisor.deg_add, ih, conorm_single, Divisor.deg_single,
      ← sum_deg_fibre h P]
    have e := map_sum (degHom L F') (fun P' => Finsupp.single P' n) (fibre h P)
    simp only [degHom, AddMonoidHom.mk'_apply, Divisor.deg_single] at e
    rw [e, Nat.cast_sum, Finset.mul_sum]

/-- `Gal(L/Fq)` acting on divisors of `F'`. -/
noncomputable def actD (τ : L ≃ₐ[Fq] L) : Divisor L F' ≃+ Divisor L F' := Finsupp.domCongr (plE h τ).symm

theorem actD_apply (τ : L ≃ₐ[Fq] L) (D : Divisor L F') (P' : Place L F') : actD h τ D P' = D (plE h τ P') := by
  simp [actD]

/-- **`div (gal τ f) = actD τ (div f)`**. -/
theorem div_gal (τ : L ≃ₐ[Fq] L) (f : F') : div (gal h.linearIndependent h.span τ f) = actD h τ (div f) := by
  ext P'
  rw [actD_apply, div_apply, div_apply, ord_plE]

theorem actD_conorm (τ : L ≃ₐ[Fq] L) (D : Divisor Fq F) : actD h τ (conorm h D) = conorm h D := by
  ext P'
  rw [actD_apply, conorm_apply, conorm_apply, contract_plE]

/-- **Invariant divisors are conorms.** -/
theorem exists_conorm_eq (D' : Divisor L F') (hD : ∀ τ, actD h τ D' = D') : ∃ D, conorm h D = D' := by
  classical
  choose lift hlift using exists_contract_eq h
  refine ⟨Finsupp.onFinset (D'.support.image (contract h)) (fun P => D' (lift P)) (fun P hP =>
    Finset.mem_image.2 ⟨lift P, Finsupp.mem_support_iff.2 hP, hlift P⟩), ?_⟩
  ext P'
  rw [conorm_apply, Finsupp.onFinset_apply]
  obtain ⟨τ, hτ⟩ := exists_plE_of_contract_eq h (lift (contract h P')) P' (hlift _)
  calc D' (lift (contract h P')) = actD h τ D' (lift (contract h P')) := by rw [hD]
    _ = D' P' := by rw [actD_apply, ← hτ]

theorem conorm_injective : Function.Injective (conorm h) := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  ext P
  obtain ⟨P', hP'⟩ := exists_contract_eq h P
  have := DFunLike.congr_fun hD P'
  rw [conorm_apply, hP'] at this
  exact this

end Conorm

end RamanujanPetersson.PicDescent

end

-- ===== S4.Def_RP_PicDescent_H90 =====
section

/-!
# S4-PicDescent, part D (H90): cyclic Hilbert 90 and norms of finite fields

* `pnorm τ u i = Π_{j<i} τ^j u` (partial norms); `pnorm τ u k` is the norm when `τ` has order `k`.
* `hilbert90_cyclic`: for an automorphism `τ` of order `k > 0` of a field `E`, `pnorm τ u k = 1` implies
  `u = τ g / g` for some `g ≠ 0` (Dedekind independence of the characters `τ^i`, `i < k`).
* `pnorm_frob_eq_norm`, `exists_pnorm_frob_eq`: for finite fields `L / K` with the arithmetic Frobenius
  `x ↦ x^q`, `pnorm` is the field norm, and it is surjective onto `K` (this is `Br(F_q) = 0` in the form
  the descent needs).
-/

set_option autoImplicit false

namespace RamanujanPetersson.PicDescent

section Hilbert90

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Partial norms `Π_{j<i} τ^j u`. -/
noncomputable def pnorm (τ : E ≃ₐ[K] E) (u : E) (i : ℕ) : E := ∏ j ∈ Finset.range i, (τ ^ j) u

theorem pnorm_zero (τ : E ≃ₐ[K] E) (u : E) : pnorm τ u 0 = 1 := by
  simp [pnorm]

theorem pnorm_succ (τ : E ≃ₐ[K] E) (u : E) (i : ℕ) : pnorm τ u (i + 1) = u * τ (pnorm τ u i) := by
  unfold pnorm
  rw [Finset.prod_range_succ', pow_zero, AlgEquiv.one_apply, map_prod, mul_comm _ u]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [pow_succ', AlgEquiv.mul_apply]

theorem pnorm_mul (τ : E ≃ₐ[K] E) (u v : E) (i : ℕ) :
    pnorm τ (u * v) i = pnorm τ u i * pnorm τ v i := by
  unfold pnorm
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => map_mul _ _ _

theorem pnorm_inv (τ : E ≃ₐ[K] E) (u : E) (i : ℕ) : pnorm τ u⁻¹ i = (pnorm τ u i)⁻¹ := by
  unfold pnorm
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun j _ => map_inv₀ _ _

theorem pnorm_ne_zero (τ : E ≃ₐ[K] E) {u : E} (hu : u ≠ 0) (i : ℕ) : pnorm τ u i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => (map_ne_zero _).2 hu

/-- The norm is fixed by `τ` when `τ ^ k = 1`. -/
theorem pnorm_fixed (τ : E ≃ₐ[K] E) {k : ℕ} (hk : τ ^ k = 1) {u : E} (hu : u ≠ 0) :
    τ (pnorm τ u k) = pnorm τ u k := by
  have h1 := pnorm_succ τ u k
  have h2 : pnorm τ u (k + 1) = u * pnorm τ u k := by
    unfold pnorm
    rw [Finset.prod_range_succ, hk, AlgEquiv.one_apply, mul_comm]
  exact mul_left_cancel₀ hu (h1.symm.trans h2)

theorem hilbert90_aux (τ : E ≃ₐ[K] E) {k : ℕ} (hk : orderOf τ = k) (hk0 : 0 < k) {u : E}
    (hu : pnorm τ u k = 1) : ∃ b : E, b ≠ 0 ∧ u * τ b = b := by
  have hinj : Function.Injective fun i : Fin k => ((τ ^ (i : ℕ) : E ≃ₐ[K] E) : E →* E) := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hk]; exact i.isLt)
      (by rw [Set.mem_Iio, hk]; exact j.isLt) h1)
  have hli := (linearIndependent_monoidHom E E).comp _ hinj
  have hex : ∃ θ : E, (∑ i : Fin k, pnorm τ u i * (τ ^ (i : ℕ)) θ) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 := Fintype.linearIndependent_iff.1 hli (fun i => pnorm τ u i) (funext fun θ => by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcon θ)
    have := h0 ⟨0, hk0⟩
    simp [pnorm] at this
  obtain ⟨θ, hθ⟩ := hex
  rw [Fin.sum_univ_eq_sum_range (fun i => pnorm τ u i * (τ ^ i) θ)] at hθ
  have hτk : τ ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one τ
  set f : ℕ → E := fun i => pnorm τ u i * (τ ^ i) θ with hf
  refine ⟨∑ i ∈ Finset.range k, f i, hθ, ?_⟩
  have hshift : ∀ i, u * τ (f i) = f (i + 1) := by
    intro i
    simp only [hf, map_mul, pnorm_succ, pow_succ', AlgEquiv.mul_apply]
    ring
  have hfk : f k = f 0 := by
    simp only [hf, hu, hτk, pnorm_zero, pow_zero, AlgEquiv.one_apply]
  rw [map_sum, Finset.mul_sum]
  simp only [hshift]
  have h1 := Finset.sum_range_succ' f k
  have h2 := Finset.sum_range_succ f k
  rw [hfk] at h2
  exact add_right_cancel (h1.symm.trans h2)

/-- **Hilbert 90 (cyclic form).** -/
theorem hilbert90_cyclic (τ : E ≃ₐ[K] E) {k : ℕ} (hk : orderOf τ = k) (hk0 : 0 < k) {u : E}
    (hu : pnorm τ u k = 1) : ∃ g : E, g ≠ 0 ∧ u = τ g / g := by
  obtain ⟨b, hb, hub⟩ := hilbert90_aux τ hk hk0 hu
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  refine ⟨b⁻¹, inv_ne_zero hb, ?_⟩
  rw [map_inv₀, inv_div_inv, eq_div_iff hτb]
  exact hub

end Hilbert90

section FiniteNorm

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Finite L] [Algebra K L]

theorem pnorm_frob_eq_norm (x : L) :
    pnorm (FiniteField.frobeniusAlgEquivOfAlgebraic K L) x (Module.finrank K L) =
      algebraMap K L (Algebra.norm K x) := by
  have := Fintype.ofFinite L
  rw [Algebra.norm_eq_prod_automorphisms,
    ← (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).prod_comp, pnorm,
    Fin.prod_univ_eq_prod_range (fun j => (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ j) x)]

theorem orderOf_frob : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L :=
  FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K L

/-- **Norms of finite fields are surjective.** -/
theorem exists_pnorm_frob_eq (a : K) :
    ∃ b : L, pnorm (FiniteField.frobeniusAlgEquivOfAlgebraic K L) b (Module.finrank K L) = algebraMap K L a := by
  obtain ⟨b, hb⟩ := FiniteField.norm_surjective K L a
  exact ⟨b, by rw [pnorm_frob_eq_norm, hb]⟩

end FiniteNorm

end RamanujanPetersson.PicDescent

end

-- ===== S4.Def_RP_PicDescent_D5 =====
section

/-!
# S4-PicDescent, part D5: Galois descent for `Pic` and `Pic⁰` along a constant field extension

For `h : RR.IsConstExt Fq F L F' c` with `constField Fq F = ⊥`, `π = frobL Fq L` the ARITHMETIC Frobenius `x ↦ x ^ q`
of `L / Fq` (review R4), acting on `F' = L ⊗ F` by `frobF h = π ⊗ id`, on divisors by `actD h π` and on classes by
`actPic h π`:
* `conormPic h : Pic Fq F →+ Pic L F'`, `degPic_conormPic` (degree preserved), `actPic_conormPic` (image is fixed);
* `conormPic_injective` (Hilbert 90 for `L / Fq`, `hilbert90_cyclic`);
* `exists_conormPic_eq`: every `π`-fixed class comes from `F` (Hilbert 90 for `F' / F` plus surjectivity of the norm
  `L^× → Fq^×`, i.e. `Br(Fq) = 0`, `exists_pnorm_frob_eq`);
* **`picEquiv h hk : Pic Fq F ≃+ fixedPic h`** (`Pic(F) = Pic(F')^π`) and
  **`pic0Equiv h hk : Pic0 Fq F ≃+ (fixedPic h ⊓ Pic0 L F')`** (`Pic⁰(F) = Pic⁰(F')^π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Toolkit

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem pow_apply_of_fixed (σ : E ≃ₐ[K] E) {x : E} (hx : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rw [pow_zero, AlgEquiv.one_apply]
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hx]

/-- Telescoping: `N_n(σ g / g) = σ^n g / g`. -/
theorem pnorm_div_self (σ : E ≃ₐ[K] E) {g : E} (hg : g ≠ 0) (n : ℕ) :
    pnorm σ (σ g / g) n = (σ ^ n) g / g := by
  induction n with
  | zero => rw [pnorm_zero, pow_zero, AlgEquiv.one_apply, div_self hg]
  | succ n ih =>
    have h1 : σ g ≠ 0 := (_root_.map_ne_zero σ).2 hg
    rw [pnorm_succ, ih, map_div₀, pow_succ', AlgEquiv.mul_apply, div_mul_div_comm,
      mul_comm (σ g) (σ ((σ ^ n) g)), mul_div_mul_right _ _ h1]

end Toolkit

section Frob

variable (Fq L : Type*) [Field Fq] [Fintype Fq] [Field L] [Fintype L] [Algebra Fq L]

/-- The arithmetic Frobenius `x ↦ x ^ q` of `L / Fq`. -/
noncomputable abbrev frobL : L ≃ₐ[Fq] L := FiniteField.frobeniusAlgEquivOfAlgebraic Fq L

theorem frobL_pow_finrank : frobL Fq L ^ Module.finrank Fq L = 1 := by
  rw [← orderOf_frob Fq L]
  exact pow_orderOf_eq_one _

theorem finrank_pos' : 0 < Module.finrank Fq L := Module.finrank_pos

variable {Fq L} in
/-- `Gal(L/Fq)` is generated by the Frobenius. -/
theorem exists_frobL_pow (τ : L ≃ₐ[Fq] L) : ∃ n : ℕ, frobL Fq L ^ n = τ := by
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow Fq L).2 τ
  exact ⟨n.1, hn⟩

end Frob

section Descent

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

/-! ### Places and divisors -/

theorem plE_plE (τ1 τ2 : L ≃ₐ[Fq] L) (P' : Place L F') : plE h τ1 (plE h τ2 P') = plE h (τ2 * τ1) P' := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact congrArg Sum.inl (pullH_pullH h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ1 τ2 w)
  · letI := algInf h; haveI := towerInf h
    exact congrArg Sum.inr (pullH_pullH h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ1 τ2 w)

theorem plE_one (P' : Place L F') : plE h 1 P' = P' := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact congrArg Sum.inl (pullH_one h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin w)
  · letI := algInf h; haveI := towerInf h
    exact congrArg Sum.inr (pullH_one h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf w)

theorem actD_mul (τ1 τ2 : L ≃ₐ[Fq] L) (D : Divisor L F') :
    actD h (τ1 * τ2) D = actD h τ1 (actD h τ2 D) := by
  ext P'
  simp only [actD_apply, plE_plE]

theorem actD_one (D : Divisor L F') : actD h 1 D = D := by
  ext P'
  simp only [actD_apply, plE_one]

theorem actD_pow_of_fixed (τ : L ≃ₐ[Fq] L) {D : Divisor L F'} (hD : actD h τ D = D) (n : ℕ) :
    actD h (τ ^ n) D = D := by
  induction n with
  | zero => rw [pow_zero, actD_one]
  | succ n ih => rw [pow_succ', actD_mul, ih, hD]

/-- A Frobenius-fixed divisor is fixed by all of `Gal(L/Fq)`. -/
theorem actD_forall_of_frob {D : Divisor L F'} (hD : actD h (frobL Fq L) D = D) (τ : L ≃ₐ[Fq] L) :
    actD h τ D = D := by
  obtain ⟨n, rfl⟩ := exists_frobL_pow τ
  exact actD_pow_of_fixed h _ hD n

/-! ### The Frobenius on `F'` -/

/-- The arithmetic Frobenius `π ⊗ id` on `F' = L ⊗ F`. -/
noncomputable def frobF : F' ≃ₐ[F] F' := gal h.linearIndependent h.span (frobL Fq L)

theorem frobF_apply (x : F') : frobF h x = gal h.linearIndependent h.span (frobL Fq L) x := rfl

theorem gal_pow (τ : L ≃ₐ[Fq] L) (n : ℕ) :
    gal h.linearIndependent h.span (τ ^ n) = gal h.linearIndependent h.span τ ^ n :=
  map_pow (galHom h.linearIndependent h.span) τ n

theorem frobF_pow : frobF h ^ Module.finrank Fq L = 1 := by
  unfold frobF
  rw [← gal_pow h, frobL_pow_finrank]
  exact map_one (galHom h.linearIndependent h.span)

theorem orderOf_frobF : orderOf (frobF h) = Module.finrank Fq L := by
  rw [← orderOf_frob Fq L]
  exact orderOf_injective (galHom h.linearIndependent h.span) (galHom_injective _ _) (frobL Fq L)

/-- A Frobenius-fixed element of `F'` is fixed by all of `Gal(L/Fq)`. -/
theorem gal_fixed_of_frob {x : F'} (hx : frobF h x = x) (τ : L ≃ₐ[Fq] L) :
    gal h.linearIndependent h.span τ x = x := by
  obtain ⟨n, rfl⟩ := exists_frobL_pow τ
  rw [gal_pow h]
  exact pow_apply_of_fixed _ hx n

theorem frobF_algebraMap_L (l : L) : frobF h (algebraMap L F' l) = algebraMap L F' (frobL Fq L l) :=
  gal_algebraMap_L h.linearIndependent h.span (frobL Fq L) l

theorem pnorm_frobF_algebraMap (l : L) (n : ℕ) :
    pnorm (frobF h) (algebraMap L F' l) n = algebraMap L F' (pnorm (frobL Fq L) l n) := by
  induction n with
  | zero => rw [pnorm_zero, pnorm_zero, map_one]
  | succ n ih => rw [pnorm_succ, pnorm_succ, ih, map_mul, frobF_algebraMap_L]

theorem div_frobF (f : F') : (div (frobF h f) : Divisor L F') = actD h (frobL Fq L) (div f) :=
  div_gal h (frobL Fq L) f

theorem div_algebraMap_L {l : L} (hl : l ≠ 0) : (div (algebraMap L F' l) : Divisor L F') = 0 :=
  ZetaSB.div_algebraMap L hl

include h in
/-- `div f = 0` in `F'` forces `f ∈ L`. -/
theorem exists_const_of_div_eq_zero (hk : constField Fq F = ⊥) {f : F'} (hf : f ≠ 0)
    (h0 : (div f : Divisor L F') = 0) : ∃ l : L, algebraMap L F' l = f := by
  have hm := (Places.div_eq_zero_iff L F' hf).1 h0
  rw [h.constField_eq_bot hk, IntermediateField.mem_bot] at hm
  exact hm

/-! ### `Pic` -/

/-- **Conorm on classes** `Pic(F) → Pic(F')`. -/
noncomputable def conormPic : Pic Fq F →+ Pic L F' :=
  QuotientAddGroup.map (princ Fq F) (princ L F') (conorm h) (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddSubgroup.mem_comap]
    exact (mem_princ L F').2 ⟨algebraMap F F' f, (_root_.map_ne_zero _).2 hf, (conorm_div h f).symm⟩)

theorem conormPic_mk (D : Divisor Fq F) :
    conormPic h (QuotientAddGroup.mk D) = (QuotientAddGroup.mk (conorm h D) : Pic L F') := rfl

/-- `Gal(L/Fq)` acting on `Pic(F')`. -/
noncomputable def actPic (τ : L ≃ₐ[Fq] L) : Pic L F' →+ Pic L F' :=
  QuotientAddGroup.map (princ L F') (princ L F') (actD h τ).toAddMonoidHom (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddSubgroup.mem_comap]
    exact (mem_princ L F').2 ⟨gal h.linearIndependent h.span τ f, (_root_.map_ne_zero _).2 hf, div_gal h τ f⟩)

theorem actPic_mk (τ : L ≃ₐ[Fq] L) (D : Divisor L F') :
    actPic h τ (QuotientAddGroup.mk D) = (QuotientAddGroup.mk (actD h τ D) : Pic L F') := rfl

/-- The classes fixed by the arithmetic Frobenius: `Pic(F')^π`. -/
noncomputable def fixedPic : AddSubgroup (Pic L F') where
  carrier := {x | actPic h (frobL Fq L) x = x}
  add_mem' := fun {a b} (ha : actPic h (frobL Fq L) a = a) (hb : actPic h (frobL Fq L) b = b) => by
    show actPic h (frobL Fq L) (a + b) = a + b
    rw [map_add, ha, hb]
  zero_mem' := by
    show actPic h (frobL Fq L) 0 = 0
    exact map_zero _
  neg_mem' := fun {a} (ha : actPic h (frobL Fq L) a = a) => by
    show actPic h (frobL Fq L) (-a) = -a
    rw [map_neg, ha]

theorem mem_fixedPic (x : Pic L F') : x ∈ fixedPic h ↔ actPic h (frobL Fq L) x = x := Iff.rfl

theorem actPic_conormPic (τ : L ≃ₐ[Fq] L) (x : Pic Fq F) : actPic h τ (conormPic h x) = conormPic h x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conormPic_mk, actPic_mk, actD_conorm]

theorem degPic_conormPic (x : Pic Fq F) : degPic L F' (conormPic h x) = degPic Fq F x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conormPic_mk, degPic_mk, degPic_mk, deg_conorm]

theorem conormPic_mem_Pic0_iff (x : Pic Fq F) : conormPic h x ∈ Pic0 L F' ↔ x ∈ Pic0 Fq F := by
  rw [mem_Pic0 L F', mem_Pic0 Fq F, degPic_conormPic]

/-- **Injectivity** (Hilbert 90 for `L / Fq`). -/
theorem conormPic_injective (hk : constField Fq F = ⊥) : Function.Injective (conormPic h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [conormPic_mk, QuotientAddGroup.eq_zero_iff] at hx
  obtain ⟨g, hg, hgD⟩ := (mem_princ L F').1 hx
  have hσg : frobF h g ≠ 0 := (_root_.map_ne_zero _).2 hg
  have hu0 : frobF h g / g ≠ 0 := div_ne_zero hσg hg
  have hdiv : (div (frobF h g / g) : Divisor L F') = 0 := by
    rw [Places.div_div hσg hg, div_frobF, hgD, actD_conorm, sub_self]
  obtain ⟨u, hu⟩ := exists_const_of_div_eq_zero h hk hu0 hdiv
  have hk0 := finrank_pos' Fq L
  have hnu : pnorm (frobL Fq L) u (Module.finrank Fq L) = 1 := by
    apply (algebraMap L F').injective
    rw [← pnorm_frobF_algebraMap h, hu, pnorm_div_self (frobF h) hg, frobF_pow, AlgEquiv.one_apply,
      div_self hg, map_one]
  obtain ⟨b, hb, hub⟩ := hilbert90_cyclic (frobL Fq L) (orderOf_frob Fq L) hk0 hnu
  have hb' : algebraMap L F' b ≠ 0 := (_root_.map_ne_zero _).2 hb
  have hfb : algebraMap L F' (frobL Fq L b) ≠ 0 := (_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hb)
  have e2 : frobF h g = algebraMap L F' u * g := by
    rw [hu]
    field_simp
  have hfix : frobF h (g / algebraMap L F' b) = g / algebraMap L F' b := by
    rw [map_div₀, frobF_algebraMap_L, e2, hub, map_div₀]
    field_simp
  obtain ⟨f, hf⟩ := RingHom.mem_range.1
    (mem_range_of_forall_gal h.linearIndependent h.span _ (gal_fixed_of_frob h hfix))
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact div_ne_zero hg hb' hf.symm
  rw [QuotientAddGroup.eq_zero_iff]
  refine (mem_princ Fq F).2 ⟨f, hf0, conorm_injective h ?_⟩
  rw [conorm_div, hf, Places.div_div hg hb', div_algebraMap_L (F' := F') hb, sub_zero, hgD]

/-- **Fixed classes descend** (Hilbert 90 for `F' / F` and `Br(Fq) = 0`). -/
theorem exists_conormPic_eq (hk : constField Fq F = ⊥) (x' : Pic L F') (hx : actPic h (frobL Fq L) x' = x') :
    ∃ x, conormPic h x = x' := by
  obtain ⟨D', rfl⟩ := QuotientAddGroup.mk_surjective x'
  rw [actPic_mk, QuotientAddGroup.eq] at hx
  obtain ⟨g, hg, hgD⟩ := (mem_princ L F').1 hx
  have hstep : actD h (frobL Fq L) D' = D' - div g := by
    rw [hgD]
    abel
  have hiter : ∀ n : ℕ, actD h (frobL Fq L ^ n) D' = D' - div (pnorm (frobF h) g n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, actD_one, pnorm_zero, div_one' L F', sub_zero]
    | succ n ih =>
      rw [pow_succ', actD_mul, ih, map_sub, hstep, ← div_frobF, pnorm_succ,
        Places.div_mul hg ((_root_.map_ne_zero (frobF h)).2 (pnorm_ne_zero (frobF h) hg n))]
      abel
  have hN0 : pnorm (frobF h) g (Module.finrank Fq L) ≠ 0 := pnorm_ne_zero _ hg _
  have hN : (div (pnorm (frobF h) g (Module.finrank Fq L)) : Divisor L F') = 0 := by
    have e := hiter (Module.finrank Fq L)
    rw [frobL_pow_finrank, actD_one] at e
    exact sub_eq_self.1 e.symm
  -- the norm `N = N_{F'/F}(g)` lies in `F`, has divisor `0`, hence is a constant of `Fq`
  have hNfix : frobF h (pnorm (frobF h) g (Module.finrank Fq L)) = pnorm (frobF h) g (Module.finrank Fq L) :=
    pnorm_fixed (frobF h) (frobF_pow h) hg
  obtain ⟨f0, hf0⟩ := RingHom.mem_range.1
    (mem_range_of_forall_gal h.linearIndependent h.span _ (gal_fixed_of_frob h hNfix))
  have hf00 : f0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf0
    exact hN0 hf0.symm
  have hdf0 : (div f0 : Divisor Fq F) = 0 := by
    apply conorm_injective h
    rw [conorm_div, hf0, hN, map_zero]
  have hm := (Places.div_eq_zero_iff Fq F hf00).1 hdf0
  rw [hk, IntermediateField.mem_bot] at hm
  obtain ⟨a0, ha0⟩ := hm
  have hNa : pnorm (frobF h) g (Module.finrank Fq L) = algebraMap L F' (algebraMap Fq L a0) := by
    rw [← hf0, ← ha0, ← IsScalarTower.algebraMap_apply Fq F F', IsScalarTower.algebraMap_apply Fq L F']
  have hk0 := finrank_pos' Fq L
  have hz : pnorm (frobL Fq L) (0 : L) (Module.finrank Fq L) = 0 := by
    rw [pnorm]
    exact Finset.prod_eq_zero (Finset.mem_range.2 hk0) (by simp)
  obtain ⟨b, hb⟩ := exists_pnorm_frob_eq Fq L a0
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hN0
    rw [hNa, ← hb]
    erw [hz]
    rw [map_zero]
  have hb' : algebraMap L F' b ≠ 0 := (_root_.map_ne_zero _).2 hb0
  have hw : pnorm (frobF h) (g / algebraMap L F' b) (Module.finrank Fq L) = 1 := by
    rw [div_eq_mul_inv, pnorm_mul, pnorm_inv, pnorm_frobF_algebraMap h]
    erw [hb]
    rw [← hNa, mul_inv_cancel₀ hN0]
  obtain ⟨e, he, hwe⟩ := hilbert90_cyclic (frobF h) (orderOf_frobF h) hk0 hw
  have hσe : frobF h e ≠ 0 := (_root_.map_ne_zero _).2 he
  have hg' : g = frobF h e / e * algebraMap L F' b := by
    rw [← hwe]
    field_simp
  have hdivg : (div g : Divisor L F') = actD h (frobL Fq L) (div e) - div e := by
    rw [hg', Places.div_mul (div_ne_zero hσe he) hb', Places.div_div hσe he, div_frobF,
      div_algebraMap_L (F' := F') hb0, add_zero]
  have hfixD : actD h (frobL Fq L) (D' + div e) = D' + div e := by
    rw [map_add, hstep, hdivg]
    abel
  obtain ⟨D, hD⟩ := exists_conorm_eq h _ (actD_forall_of_frob h hfixD)
  refine ⟨QuotientAddGroup.mk D, ?_⟩
  rw [conormPic_mk, hD, QuotientAddGroup.eq]
  refine (mem_princ L F').2 ⟨e⁻¹, inv_ne_zero he, ?_⟩
  rw [div_inv' L he]
  abel

/-- **Galois descent for `Pic`**: `Pic(F) ≃ Pic(F')^π` (`π` = arithmetic Frobenius), via the conorm. -/
noncomputable def picEquiv (hk : constField Fq F = ⊥) : Pic Fq F ≃+ fixedPic h :=
  AddEquiv.ofBijective ((conormPic h).codRestrict (fixedPic h) fun x =>
      (mem_fixedPic h _).2 (actPic_conormPic h _ x)) (by
    constructor
    · intro x y hxy
      exact conormPic_injective h hk (congrArg Subtype.val hxy)
    · rintro ⟨x', hx'⟩
      obtain ⟨x, hx⟩ := exists_conormPic_eq h hk x' hx'
      exact ⟨x, Subtype.ext hx⟩)

theorem picEquiv_apply (hk : constField Fq F = ⊥) (x : Pic Fq F) :
    (picEquiv h hk x : Pic L F') = conormPic h x := rfl

/-- **Galois descent for `Pic⁰`**: `Pic⁰(F) ≃ Pic⁰(F')^π`. -/
noncomputable def pic0Equiv (hk : constField Fq F = ⊥) :
    Pic0 Fq F ≃+ (fixedPic h ⊓ Pic0 L F' : AddSubgroup (Pic L F')) :=
  AddEquiv.ofBijective (((conormPic h).comp (Pic0 Fq F).subtype).codRestrict (fixedPic h ⊓ Pic0 L F') fun x =>
      AddSubgroup.mem_inf.2 ⟨(mem_fixedPic h _).2 (actPic_conormPic h _ x),
        (conormPic_mem_Pic0_iff h x).2 x.2⟩) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (conormPic_injective h hk (congrArg Subtype.val hxy))
    · rintro ⟨x', hx'⟩
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx'
      obtain ⟨x, hx⟩ := exists_conormPic_eq h hk x' hx1
      have hx0 : x ∈ Pic0 Fq F := by
        rw [← conormPic_mem_Pic0_iff h, hx]
        exact hx2
      exact ⟨⟨x, hx0⟩, Subtype.ext hx⟩)

theorem pic0Equiv_apply (hk : constField Fq F = ⊥) (x : Pic0 Fq F) :
    (pic0Equiv h hk x : Pic L F') = conormPic h x := rfl

end Descent

end RamanujanPetersson.PicDescent

end

-- ===== S4.Def_RP_Kummer_InfMain =====
section

/-!
# S4-Kummer K5c: parabolic Kummer classes (main theorem)

Generic chart `R0` (Dedekind, fraction field `K`), boundary data `D` whose `B` is "nonzero prime of the pro-chart".
* `forall_dvd_congr_range`: the divisibility condition `N ∣ v(a)` does not depend on the Dedekind model of the integral
  closure of `R0` in `M`.
* `fixed_of_dvd`: `N ∣ v(a)` at all primes over `R0` ⇒ boundary inertia fixing `M` fixes every `N`-th root of `a`.
* `dvd_of_mem_maxUnram`: an `N`-th root of `a` unramified over `R0` ⇒ `N ∣ v(a)` at all primes over `R0`.
* `fixed_of_mem_curveH1par`: a parabolic Kummer class is fixed by the inertia of EVERY boundary prime.
* **`kclass_mem_curveH1par_iff`**: `kclass α ∈ H¹_par ↔ α ∈ maxUnram R0 K ↔ ∀ v over R0, N ∣ v(α ^ N)`.
* Curve instance (`R0 = Rinf`): `isIntegral_iff_mem_Rinf`, `perfect_Rinf`, `Fc_mem_unramSet_inf`, `fixed_of_mem_Fc`,
  **`kclass_mem_curveH1par_iff_ord`** (orders at the infinite places of the constant level `F_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

section GenericInf

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0] [IsDedekindDomain R0]
  [Algebra R0 K] [IsFractionRing R0 K]

/-- The divisibility condition is independent of the Dedekind model `B` of the integral closure of `R0` in `M`. -/
theorem forall_dvd_congr_range {M : IntermediateField K (AlgebraicClosure K)}
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range) (n : ℤ) (a : M) :
    (∀ v : HeightOneSpectrum B, n ∣ WithZero.log (v.valuation M a)) ↔
      ∀ v : HeightOneSpectrum (integralClosure R0 M), n ∣ WithZero.log (v.valuation M a) := by
  have hBinj : Function.Injective (algebraMap B M) := IsFractionRing.injective B M
  have hrange : (integralClosure R0 M).toSubring = (algebraMap B M).range :=
    Subring.ext fun x => hB x
  let e1 : integralClosure R0 M ≃+* (algebraMap B M).range := RingEquiv.subringCongr hrange
  let e2 : B ≃+* (algebraMap B M).range := RingEquiv.ofBijective (algebraMap B M).rangeRestrict
    ⟨fun x y hxy => hBinj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective _⟩
  let eR : integralClosure R0 M ≃+* B := e1.trans e2.symm
  have heR : ∀ x, algebraMap B M (eR x) = algebraMap (integralClosure R0 M) M x := fun x =>
    congrArg Subtype.val (e2.apply_symm_apply (e1 x))
  have heR' : ∀ b, algebraMap (integralClosure R0 M) M (eR.symm b) = algebraMap B M b := fun b => by
    rw [← heR, RingEquiv.apply_symm_apply]
  constructor
  · intro hv v
    have h1 := hv (HeightOneSpectrum.comap (eR.symm : B →+* integralClosure R0 M) eR.symm.surjective v)
    rwa [valuation_comap eR.symm heR' v] at h1
  · intro hv v
    have h1 := hv (HeightOneSpectrum.comap (eR : integralClosure R0 M →+* B) eR.surjective v)
    rwa [valuation_comap eR heR v] at h1

/-- **(b)** `N ∣ v(a)` at every prime over `R0` (in any Dedekind model `B`) ⇒ a pro-chart inertia element fixing the
finite level `M ∈ unramSet A K` fixes every `N`-th root of `a`. -/
theorem fixed_of_dvd {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K) {N : ℕ} [NeZero N]
    (hN : IsUnit (N : R0)) {a : M} (ha : a ≠ 0) {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M]
    [IsFractionRing B M] (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range)
    (hv : ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a))
    {P : Ideal (proChart A K R0)} [P.IsPrime] {g : Pi1 A K} (hg : g ∈ P.inertia (Pi1 A K))
    (hgM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x)
    (α : maxUnram A K) (hα : (α : AlgebraicClosure K) ^ N = a) : g α = α := by
  haveI : FiniteDimensional K M := hM.1
  haveI : IsGalois K M := hM.2.1
  haveI : IsFractionRing (integralClosure R0 M) M :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K M
  haveI : IsDedekindDomain (integralClosure R0 M) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := M)
  obtain ⟨I, hI⟩ := exists_pow_mul_spanSingleton_eq_one ha ((forall_dvd_congr_range R0 hB (N : ℤ) a).1 hv)
  exact fixed_of_bdry_inertia hM hN hg hgM I hI α hα

/-- **(c)** An `N`-th root of `a ∈ M` unramified over `R0` ⇒ `N ∣ v(a)` at every prime over `R0`. -/
theorem dvd_of_mem_maxUnram {M : IntermediateField K (AlgebraicClosure K)} (hMR : M ∈ unramSet R0 K)
    (hperf : ∀ (p : Ideal R0) [p.IsMaximal], PerfectField p.ResidueField)
    {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range)
    {N : ℕ} {α : AlgebraicClosure K} (hαU : α ∈ maxUnram R0 K) {a : M} (hα : α ^ N = (a : AlgebraicClosure K))
    (v : HeightOneSpectrum B) : (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  haveI : FiniteDimensional K M := hMR.1
  haveI : IsGalois K M := hMR.2.1
  haveI : IsFractionRing (integralClosure R0 M) M :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K M
  haveI : IsDedekindDomain (integralClosure R0 M) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := M)
  exact (forall_dvd_congr_range R0 hB (N : ℤ) a).2 (dvd_log_valuation_of_mem_maxUnram R0 hMR hperf hαU hα) v

variable {q N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo A K q, σ ζ = ζ) {S : Type} (D : BdryData A K q R0 S)

include hζ hζΓ in
/-- A parabolic Kummer class is fixed by the inertia of EVERY boundary prime (not only the representatives `D.P s`):
conjugate into `D.P s` by `h ∈ π₁^geo` and use that `kchar α` is a homomorphism to an abelian group. -/
theorem fixed_of_mem_curveH1par {p e : ℕ} [Fact p.Prime] [CharP K p] (he : 0 < e) (hq : q = p ^ e)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) {α : (maxUnram A K)ˣ} (hα : α ∈ rad (pi1geo A K q) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D) :
    ∀ P : Ideal (proChart A K R0), IsBdryPrime A K R0 P → ∀ g ∈ P.inertia (Pi1 A K),
      g (α : maxUnram A K) = α := by
  intro P hP g hg
  haveI := hP.1
  have hgΓ : g ∈ pi1geo A K q := inertia_le_pi1geo he hq hg
  obtain ⟨s, h, hh, hPs⟩ := D.cover P ((hDB P).2 hP)
  have hg' : h⁻¹ * g * h ∈ D.inertia s := inv_conj_mem_inertia A K R0 hPs hg
  have hΓ' : h⁻¹ * g * h ∈ pi1geo A K q := mul_mem (mul_mem (inv_mem hh) hgΓ) hh
  have h0 := ((mem_curveH1par_iff hζ hζΓ D hα).1 hpar) s _ hΓ' hg'
  have hk : kchar hζ α (⟨h⁻¹ * g * h, hΓ'⟩ : pi1geo A K q) = 0 :=
    (kchar_eq_iff hζ hα _ 0).2 (by rw [epow_zero, one_mul]; exact h0)
  have e1 := kchar_mul hζ hζΓ hα ((⟨h, hh⟩ : pi1geo A K q)⁻¹ * ⟨g, hgΓ⟩) ⟨h, hh⟩
  have e2 := kchar_mul hζ hζΓ hα (⟨h, hh⟩ : pi1geo A K q)⁻¹ ⟨g, hgΓ⟩
  have e3 := kchar_mul hζ hζΓ hα (⟨h, hh⟩ : pi1geo A K q)⁻¹ ⟨h, hh⟩
  rw [inv_mul_cancel, kchar_one hζ hζΓ hα] at e3
  have e0 : (⟨h, hh⟩ : pi1geo A K q)⁻¹ * ⟨g, hgΓ⟩ * ⟨h, hh⟩ = ⟨h⁻¹ * g * h, hΓ'⟩ := Subtype.ext rfl
  rw [e0, hk, e2] at e1
  have hg0 : kchar hζ α (⟨g, hgΓ⟩ : pi1geo A K q) = 0 := by linear_combination -e1 + e3
  have h1 := (kchar_eq_iff hζ hα (⟨g, hgΓ⟩ : pi1geo A K q) 0).1 hg0
  rw [epow_zero, one_mul] at h1
  exact h1

include hζ hζΓ in
/-- **K5c MAIN (generic chart)**: for `α` with `α ^ N = a ∈ M` (`M` a finite level of constants, unramified over `A`
and over `R0`), the Kummer class of `α` is parabolic iff `α` is unramified over `R0` iff `N` divides the valuation of
`a` at every prime of `M` over `R0`. -/
theorem kclass_mem_curveH1par_iff {p e : ℕ} [Fact p.Prime] [CharP K p] (he : 0 < e) (hq : q = p ^ e)
    (hlift : BdryLift A K R0) (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q)
    {M : IntermediateField K (AlgebraicClosure K)} (hMA : M ∈ unramSet A K) (hMR : M ∈ unramSet R0 K)
    (hperf : ∀ (p : Ideal R0) [p.IsMaximal], PerfectField p.ResidueField) (hN : IsUnit (N : R0))
    (hMfix : ∀ g ∈ pi1geo A K q, ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x)
    {a : M} (ha : a ≠ 0) {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral R0 x ↔ x ∈ (algebraMap B M).range)
    {α : (maxUnram A K)ˣ} (hα : α ∈ rad (pi1geo A K q) N)
    (haα : ((α : maxUnram A K) : AlgebraicClosure K) ^ N = a) :
    (kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D ↔
        ((α : maxUnram A K) : AlgebraicClosure K) ∈ maxUnram R0 K) ∧
      (kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D ↔
        ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) := by
  have h1 : kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D →
      ((α : maxUnram A K) : AlgebraicClosure K) ∈ maxUnram R0 K := fun hpar =>
    mem_maxUnram_of_fixed hlift _ (fixed_of_mem_curveH1par R0 hζ hζΓ D he hq hDB hα hpar)
  have h2 : ((α : maxUnram A K) : AlgebraicClosure K) ∈ maxUnram R0 K →
      ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a) := fun hU =>
    dvd_of_mem_maxUnram R0 hMR hperf hB hU haα
  have h3 : (∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) →
      kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D := fun hv => by
    rw [mem_curveH1par_iff hζ hζΓ D hα]
    intro s g hgΓ hgs
    haveI : (D.P s).IsPrime := ((hDB _).1 (D.mem s)).1
    exact fixed_of_dvd R0 hMA hN ha hB hv (P := D.P s) hgs (hMfix g hgΓ) _ haα
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

end GenericInf

/-! ## The curve instance: `R0 = Rinf` -/

section GenericC

open PicDescent Places

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

/-- In a constant field extension `F'/F`, the integral closure of `Rinf(F)` in `F'` is `Rinf(F')`. -/
theorem isIntegral_iff_mem_Rinf (h : RR.IsConstExt Fq F L F' c) (x : F') :
    IsIntegral (Rinf Fq F) x ↔ IsIntegral (Oinf L) x := by
  constructor
  · intro hx
    letI := algInf h
    haveI := towerInf h
    refine isIntegral_of_forall_algebraMap (A := Rinf Fq F) (fun a => ?_) hx
    rw [IsScalarTower.algebraMap_apply (Rinf Fq F) (Rinf L F') F']
    exact (algebraMap (Rinf Fq F) (Rinf L F') a).2
  · intro hx
    letI := algInf h
    haveI := towerInf h
    haveI := isIntegral_AA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf
    exact (Algebra.IsIntegral.isIntegral (R := Rinf Fq F) (⟨x, hx⟩ : Rinf L F')).algebraMap

end GenericC

section InfC

open PicDescent Places

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- Residue fields of `Rinf(F)` at maximal ideals are finite, hence perfect. -/
theorem perfect_Rinf : ∀ (P : Ideal (Rinf Fq F)) [P.IsMaximal], PerfectField P.ResidueField := by
  intro P hP
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (not_isField_Rinf Fq F)
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  haveI := Places.FiniteQuot.finite (S := Rinf Fq F) a ha0
  haveI : Finite (Rinf Fq F ⧸ P) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haP))
  haveI : Finite P.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField P).2
  infer_instance

variable {Fq F} {p e : ℕ} [Fact p.Prime] [CharP F p]

/-- Constant levels are unramified over `Rinf` too. -/
theorem Fc_mem_unramSet_inf (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m] :
    Fc Fq F (AlgebraicClosure F) m ∈ unramSet (Rinf Fq F) F := by
  rw [Fc_eq_constLevel hq (Nat.mul_pos he (NeZero.pos m))]
  exact constLevel_mem_unramSet (Rinf Fq F) (Nat.mul_pos he (NeZero.pos m))

/-- `π₁^geo` fixes the constant level `F_m`. -/
theorem fixed_of_mem_Fc (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m] :
    ∀ g ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), ∀ x : maxUnram (Rfin Fq F) F,
      (x : AlgebraicClosure F) ∈ Fc Fq F (AlgebraicClosure F) m → g x = x := by
  intro g hg x hx
  rw [Fc_eq_constLevel hq (Nat.mul_pos he (NeZero.pos m))] at hx
  rw [hq] at hg
  exact fixed_of_mem_constLevel he (Nat.mul_pos he (NeZero.pos m)) hx g hg

/-- **K5c MAIN (curves, boundary at infinity)**: for `α ∈ K_U^×` with `α ^ N = a ∈ F_m^×` (`α` in `rad π₁^geo`), the
Kummer class of `α` is parabolic iff `α` is unramified over `Rinf` iff `N ∣ ord_v a` at every infinite place `v` of
`F_m`. -/
theorem kclass_mem_curveH1par_iff_ord (hk : constField Fq F = ⊥) (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (m : ℕ) [NeZero m] {N : ℕ} [NeZero N] (hN : IsUnit (N : Rinf Fq F))
    {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
    (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
    (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
    {a : Fc Fq F (AlgebraicClosure F) m} (ha : a ≠ 0)
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (haα : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N = a) :
    (kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ↔
        ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ∈ maxUnram (Rinf Fq F) F) ∧
      (kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ↔
        ∀ v : HeightOneSpectrum (Rinf (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m)),
          (N : ℤ) ∣ Places.ord v a) := by
  have hB : ∀ x : Fc Fq F (AlgebraicClosure F) m, IsIntegral (Rinf Fq F) x ↔
      x ∈ (algebraMap (Rinf (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m))
        (Fc Fq F (AlgebraicClosure F) m)).range := by
    intro x
    refine (isIntegral_iff_mem_Rinf (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) x).trans
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact y.2
  have hmain := kclass_mem_curveH1par_iff (Rinf Fq F) hζ hζΓ D he hq hlift hDB
    (Fc_mem_unramSet hq he m) (Fc_mem_unramSet_inf hq he m) (perfect_Rinf Fq F) hN
    (fixed_of_mem_Fc hq he m) ha hB hα haα
  refine ⟨hmain.1, hmain.2.trans (forall_congr' fun v => ?_)⟩
  rw [Places.ord]
  exact dvd_neg.symm

end InfC

end

end Kummer
end RamanujanPetersson

end

-- ===== S4.Def_RP_CP4a_TrExact =====
section

/-!
# S4-CP4a, part d1: traces are additive along short exact sequences of free modules

`trace_eq_add_of_exact`: for `0 → P → M → Q → 0` exact (`P`, `Q` finite free over a commutative ring) and
compatible endomorphisms `fP, f, fQ`, `Tr f = Tr fP + Tr fQ` (the sequence splits since `Q` is projective; in the
split coordinates `f` is block upper triangular, and the off-diagonal block has trace `0`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.CP4a

variable {R : Type*} [CommRing R] {P M Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- A short exact sequence `0 → P → M → Q → 0` with `Q` projective splits: `P × Q ≃ M`. -/
theorem exists_split_of_exact [Module.Projective R Q] (i : P →ₗ[R] M) (π : M →ₗ[R] Q)
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : LinearMap.range i = LinearMap.ker π) :
    ∃ e : (P × Q) ≃ₗ[R] M, (∀ p, e (p, 0) = i p) ∧ ∀ x, π x = (e.symm x).2 := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ q, π (s q) = q := fun q => LinearMap.congr_fun hs q
  have hπi : ∀ p, π (i p) = 0 := fun p => LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self i p)
  have he0 : Function.Bijective (i.coprod s) := by
    constructor
    · refine (injective_iff_map_eq_zero _).mpr ?_
      rintro ⟨p, q⟩ h
      rw [LinearMap.coprod_apply] at h
      have hq : q = 0 := by
        have h1 := congrArg π h
        rwa [map_add, hπi, hs', zero_add, map_zero] at h1
      subst hq
      rw [map_zero, add_zero] at h
      rw [(injective_iff_map_eq_zero i).mp hi p h]
      rfl
    · intro x
      have hx : x - s (π x) ∈ LinearMap.range i := by
        rw [hex, LinearMap.mem_ker, map_sub, hs', sub_self]
      obtain ⟨p, hp⟩ := hx
      exact ⟨(p, π x), by rw [LinearMap.coprod_apply, hp, sub_add_cancel]⟩
  refine ⟨LinearEquiv.ofBijective _ he0, fun p => ?_, fun x => ?_⟩
  · rw [LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_zero, add_zero]
  · obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ he0).surjective x
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_add, hπi, hs',
      zero_add]

/-- **Trace additivity** along `0 → P → M → Q → 0` (finite free `P`, `Q`). -/
theorem trace_eq_add_of_exact [Module.Free R P] [Module.Finite R P] [Module.Free R Q] [Module.Finite R Q]
    (i : P →ₗ[R] M) (π : M →ₗ[R] Q) (hi : Function.Injective i) (hπ : Function.Surjective π)
    (hex : LinearMap.range i = LinearMap.ker π) (f : Module.End R M) (fP : Module.End R P) (fQ : Module.End R Q)
    (hP : ∀ p, f (i p) = i (fP p)) (hQ : ∀ x, π (f x) = fQ (π x)) :
    LinearMap.trace R M f = LinearMap.trace R P fP + LinearMap.trace R Q fQ := by
  obtain ⟨e, he1, he2⟩ := exists_split_of_exact i π hi hπ hex
  have : Module.Free R M := Module.Free.of_equiv e
  have : Module.Finite R M := Module.Finite.equiv e
  rw [← LinearMap.trace_conj' f e.symm]
  set g := e.symm.conj f with hgdef
  have hg1 : ∀ p, g (p, 0) = (fP p, 0) := fun p => by
    rw [hgdef, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, he1, hP, ← he1, LinearEquiv.symm_apply_apply]
  have hg2 : ∀ q, (g (0, q)).2 = fQ q := fun q => by
    rw [hgdef, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, ← he2, hQ, he2, LinearEquiv.symm_apply_apply]
  set h := LinearMap.fst R P Q ∘ₗ g ∘ₗ LinearMap.inr R P Q with hh
  have hsplit : g = LinearMap.prodMap fP fQ + LinearMap.inl R P Q ∘ₗ (h ∘ₗ LinearMap.snd R P Q) := by
    refine LinearMap.prod_ext (LinearMap.ext fun p => ?_) (LinearMap.ext fun q => ?_)
    · simp [hg1]
    · refine Prod.ext ?_ ?_
      · simp [hh]
      · simp [hg2]
  rw [hsplit, map_add, LinearMap.trace_prodMap', LinearMap.trace_comp_comm', LinearMap.comp_assoc,
    LinearMap.snd_comp_inl, LinearMap.comp_zero, map_zero, add_zero]

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_CP4a_Les =====
section

/-!
# S4-CP4a, part d2: traces along `0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0` (constant coefficients)

* `trace_les` / `trace_les_pow`: for an exact `0 → H₀ → B → C → P → 0` with compatible endomorphisms
  (`H₀`, `B / H₀`, `P` finite free), `Tr(f_C^m) = Tr(f_B^m) - Tr(f_{H₀}^m) + Tr(f_P^m)`.
* `trace_funLeft`: the trace of `b ↦ b ∘ σ` on `S → R` is `#{s | σ s = s}`.
* Constant coefficients (`Representation.trivial k G k`, generic profinite-style `G`, `Γ`, boundary `I`):
  `trace_frobH0_triv` (`= 1`), `trace_frobBdry_triv` (`= #Fix(τ^m)`), `trace_frobH2c_triv` (`= χ^m`),
  `trace_frobH1c_triv`: `Tr(F^m | H¹_c) = #Fix(τ^m) - 1 + Tr(F^m | H¹_par)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CP4a

open CurveCoh

section Abstract

variable {R : Type*} [CommRing R]

theorem pow_apply_comm {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (g : M₁ →ₗ[R] M₂) (f₁ : Module.End R M₁) (f₂ : Module.End R M₂) (h : ∀ x, f₂ (g x) = g (f₁ x))
    (m : ℕ) (x : M₁) : (f₂ ^ m) (g x) = g ((f₁ ^ m) x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [pow_succ, Module.End.mul_apply, h, ih, pow_succ, Module.End.mul_apply]

theorem conj_pow_les {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) (m : ℕ) : e.conj (f ^ m) = e.conj f ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]; rfl
  | succ m ih => rw [pow_succ, Module.End.mul_eq_comp, LinearEquiv.conj_comp, ih, pow_succ, Module.End.mul_eq_comp]

theorem exact_codRestrict {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : Submodule R M₃)
    (hp : ∀ x, g x ∈ p) (h : Function.Exact f g) : Function.Exact f (LinearMap.codRestrict p g hp) := fun y => by
  rw [← h y, Subtype.ext_iff]
  exact Iff.rfl

theorem surjective_codRestrict {M₂ M₃ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (g : M₂ →ₗ[R] M₃) (p : Submodule R M₃) (hp : ∀ x, g x ∈ p) (h : LinearMap.range g = p) :
    Function.Surjective (LinearMap.codRestrict p g hp) := by
  rintro ⟨y, hy⟩
  rw [← h] at hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  exact ⟨x, rfl⟩

/-- **Trace along a four-term exact sequence** `0 → H₀ → B → C → P → 0`. -/
theorem trace_les {H0 B C P : Type*} [AddCommGroup H0] [Module R H0] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup P] [Module R P]
    (i : H0 →ₗ[R] B) (d : B →ₗ[R] C) (π : C →ₗ[R] P) (hi : Function.Injective i)
    (hid : Function.Exact i d) (hdπ : Function.Exact d π) (hπ : Function.Surjective π)
    (hH0 : Module.Free R H0 ∧ Module.Finite R H0) (hBf : Module.Finite R B)
    (hQ : Module.Free R (B ⧸ LinearMap.range i)) (hP : Module.Free R P ∧ Module.Finite R P)
    (f0 : Module.End R H0) (fB : Module.End R B) (fC : Module.End R C) (fP : Module.End R P)
    (h0 : ∀ x, fB (i x) = i (f0 x)) (h1 : ∀ b, fC (d b) = d (fB b)) (h2 : ∀ c, π (fC c) = fP (π c)) :
    LinearMap.trace R C fC = LinearMap.trace R B fB - LinearMap.trace R H0 f0 + LinearMap.trace R P fP := by
  obtain ⟨_, _⟩ := hH0
  obtain ⟨_, _⟩ := hP
  have hle : LinearMap.range i ≤ (LinearMap.range i).comap fB := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f0 x, (h0 x).symm⟩
  have hker : LinearMap.ker d = LinearMap.range i := LinearMap.exact_iff.mp hid
  have hker' : LinearMap.ker π = LinearMap.range d := LinearMap.exact_iff.mp hdπ
  let fQ : Module.End R (B ⧸ LinearMap.range i) := (LinearMap.range i).mapQ (LinearMap.range i) fB hle
  let dq : (B ⧸ LinearMap.range i) →ₗ[R] C := (LinearMap.range i).liftQ d hker.ge
  have hB := trace_eq_add_of_exact i (LinearMap.range i).mkQ hi (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm fB f0 fQ h0 (fun _ => rfl)
  have hdq : Function.Injective dq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hker.symm
  have hC := trace_eq_add_of_exact dq π hdq hπ (by rw [Submodule.range_liftQ, hker']) fC fQ fP
    (fun x => by
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
      exact h1 b) h2
  rw [hC, hB]
  ring

/-- `trace_les` for powers, with the three known traces as hypotheses (for term-mode use on heavy types). -/
theorem trace_les_pow {H0 B C P : Type*} [AddCommGroup H0] [Module R H0] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup P] [Module R P]
    (i : H0 →ₗ[R] B) (d : B →ₗ[R] C) (π : C →ₗ[R] P) (hi : Function.Injective i)
    (hid : Function.Exact i d) (hdπ : Function.Exact d π) (hπ : Function.Surjective π)
    (hH0 : Module.Free R H0 ∧ Module.Finite R H0) (hBf : Module.Finite R B)
    (hQ : Module.Free R (B ⧸ LinearMap.range i)) (hP : Module.Free R P ∧ Module.Finite R P)
    (f0 : Module.End R H0) (fB : Module.End R B) (fC : Module.End R C) (fP : Module.End R P)
    (h0 : ∀ x, fB (i x) = i (f0 x)) (h1 : ∀ b, fC (d b) = d (fB b)) (h2 : ∀ c, π (fC c) = fP (π c))
    (m : ℕ) {t0 tB tP : R} (ht0 : LinearMap.trace R H0 (f0 ^ m) = t0)
    (htB : LinearMap.trace R B (fB ^ m) = tB) (htP : LinearMap.trace R P (fP ^ m) = tP) :
    LinearMap.trace R C (fC ^ m) = tB - t0 + tP := by
  rw [← ht0, ← htB, ← htP]
  exact trace_les i d π hi hid hdπ hπ hH0 hBf hQ hP _ _ _ _ (pow_apply_comm i f0 fB h0 m)
    (pow_apply_comm d fB fC h1 m) (fun c => (pow_apply_comm π fC fP (fun c => (h2 c).symm) m c).symm)

theorem funLeft_pow {S : Type*} (σ : S → S) (m : ℕ) :
    LinearMap.funLeft R R σ ^ m = LinearMap.funLeft R R σ^[m] := by
  induction m with
  | zero => exact LinearMap.ext fun _ => rfl
  | succ m ih =>
    rw [pow_succ', ih, Function.iterate_succ, LinearMap.funLeft_comp]
    rfl

/-- **Permutation trace**: `Tr(b ↦ b ∘ σ | S → R) = #{s | σ s = s}`. -/
theorem trace_funLeft {S : Type*} [Fintype S] [DecidableEq S] (σ : S → S) :
    LinearMap.trace R (S → R) (LinearMap.funLeft R R σ) =
      ((Finset.univ.filter fun s => σ s = s).card : R) := by
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R S), LinearMap.toMatrix_eq_toMatrix', Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix'_apply, LinearMap.funLeft_apply, Pi.single_apply]
  rw [Finset.sum_boole]

theorem trace_one_of_equiv {M₁ : Type*} [AddCommGroup M₁] [Module R M₁] (e : M₁ ≃ₗ[R] R) :
    LinearMap.trace R M₁ 1 = 1 := by
  have := Module.Free.of_equiv e.symm
  have := Module.Finite.equiv e.symm
  rw [LinearMap.trace_one, e.finrank_eq]
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · rw [Module.finrank_self, Nat.cast_one]

/-- Arithmetic of the Lefschetz combination `Tr(H²_c) - Tr(H¹_c)`. -/
theorem lefschetz_combine (q Nm fix m : ℕ) {t2 t1 : R} (h2 : t2 = (q : R) ^ m)
    (h1 : t1 = (fix : R) - 1 + (((1 + (q : ℤ) ^ m - (Nm : ℤ)) : ℤ) : R)) : t2 - t1 = (Nm : R) - (fix : R) := by
  rw [h2, h1]
  push_cast
  ring

end Abstract

section Pair

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

theorem frobH0_triv (ψ : G) : frobH0 (Representation.trivial k G k) Γ ψ = 1 :=
  LinearMap.ext fun _ => rfl

theorem trace_frobH0_triv (ψ : G) (m : ℕ) :
    LinearMap.trace k (H0 (Representation.trivial k G k) Γ) (frobH0 (Representation.trivial k G k) Γ ψ ^ m) = 1 := by
  rw [frobH0_triv, one_pow]
  exact trace_one_of_equiv (h0ConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl))

/-- Constant coefficients: `⊕_s M^{I_s} = (S → k)`. -/
noncomputable def bdryTrivEquiv : bdryInv (Representation.trivial k G k) Γ I ≃ₗ[k] (S → k) :=
  (LinearEquiv.ofEq _ _ (bdryInv_eq_top_of_trivial _ Γ I (fun _ => rfl))).trans (LinearEquiv.ofTop ⊤ rfl)

theorem trace_frobBdry_triv [Fintype S] [DecidableEq S] (ψ : G) (τ : S → S) (h : S → Γ)
    (hI : BdryCompat Γ I ψ τ h) (m : ℕ) :
    LinearMap.trace k (bdryInv (Representation.trivial k G k) Γ I)
        (frobBdry (Representation.trivial k G k) Γ I ψ τ h hI ^ m) =
      ((Finset.univ.filter fun s => τ^[m] s = s).card : k) := by
  have he : (bdryTrivEquiv Γ I).conj (frobBdry (Representation.trivial k G k) Γ I ψ τ h hI) =
      LinearMap.funLeft k k τ := LinearMap.ext fun _ => rfl
  rw [← LinearMap.trace_conj' _ (bdryTrivEquiv Γ I), conj_pow_les, he, funLeft_pow, trace_funLeft]

theorem trace_frobH2c_triv (ψ : G) (χ : k) (m : ℕ) :
    LinearMap.trace k (H2c (Representation.trivial k G k) Γ)
      (frobH2c (Representation.trivial k G k) Γ ψ χ ^ m) = χ ^ m := by
  have hf : frobH2c (Representation.trivial k G k) Γ ψ χ = χ • 1 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    exact frobH2c_mk _ _ _ _ _
  rw [hf, smul_pow, one_pow, map_smul,
    trace_one_of_equiv (h2cConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl)), smul_eq_mul, mul_one]

/-- `H¹_c → H¹_par` (the corestriction of `h1cToH1` to its range). -/
noncomputable def h1cToH1par : H1c (Representation.trivial k G k) Γ I →ₗ[k] H1par (Representation.trivial k G k) Γ I :=
  LinearMap.codRestrict _ (h1cToH1 (Representation.trivial k G k) Γ I) fun c => by
    rw [← range_h1cToH1]
    exact LinearMap.mem_range_self _ c

/-- **Constant coefficients**: `Tr(F^m | H¹_c) = #Fix(τ^m) - 1 + Tr(F^m | H¹_par)` (`F = T_ψ`, any `fP` on
`H¹_par` compatible with `h1cToH1`, `H¹_par` finite free). -/
theorem trace_frobH1c_triv [Fintype S] [DecidableEq S] [Nonempty S] (ψ : G) (τ : S → S) (h : S → Γ)
    (hI : BdryCompat Γ I ψ τ h) (fP : Module.End k (H1par (Representation.trivial k G k) Γ I))
    (hfP : ∀ c, h1cToH1 (Representation.trivial k G k) Γ I (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI c) =
      (fP (h1cToH1par (k := k) Γ I c) : H1 (Representation.trivial k G k) Γ))
    (hP : Module.Free k (H1par (Representation.trivial k G k) Γ I) ∧
      Module.Finite k (H1par (Representation.trivial k G k) Γ I))
    (m : ℕ) {tP : k} (htP : LinearMap.trace k _ (fP ^ m) = tP) :
    LinearMap.trace k (H1c (Representation.trivial k G k) Γ I)
        (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI ^ m) =
      ((Finset.univ.filter fun s => τ^[m] s = s).card : k) - 1 + tP :=
  by
  refine trace_les_pow (h0ToBdry _ Γ I) (bdryToH1c _ Γ I) (h1cToH1par (k := k) Γ I) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hP
    (frobH0 _ Γ ψ) (frobBdry _ Γ I ψ τ h hI) _ fP ?_ ?_ ?_ m ?_ ?_ htP
  · exact h0ToBdry_injective _ Γ I
  · exact exact_h0ToBdry_bdryToH1c _ Γ I
  · exact exact_codRestrict _ _ _ _ (exact_bdryToH1c_h1cToH1 _ Γ I)
  · exact surjective_codRestrict _ _ _ (range_h1cToH1 _ Γ I)
  · exact ⟨Module.Free.of_equiv (h0ConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl)).symm,
      Module.Finite.equiv (h0ConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl)).symm⟩
  · exact Module.Finite.equiv (bdryTrivEquiv Γ I).symm
  · exact Module.Free.of_equiv (constQuotEquiv (Representation.trivial k G k) Γ I (Classical.arbitrary S)
      (fun _ => rfl)).symm
  · exact frobBdry_h0ToBdry _ Γ I ψ τ h hI
  · exact frobH1c_bdryToH1c _ Γ I ψ τ h hI
  · exact fun c => Subtype.ext (hfP c)
  · exact trace_frobH0_triv Γ ψ m
  · exact trace_frobBdry_triv Γ I ψ τ h hI m

end Pair

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_Cone_ResCos =====
section

/-!
# S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)

`π : G →* Gf`, `Γ ≤ G`, subgroups `I s`. The cover points are `CosT = Σ s, π(Γ) ⧸ π(Γ ∩ I s)` (left cosets), with lifts
`cosX t ∈ Γ` of the coset representatives (`cosX = 1` on the trivial coset).

* `cos_rep`: every `p ∈ π(Γ)` lies in exactly one coset `π(x_t) π(Γ ∩ I s)` over `s` (the `hrep` field of `ResDat`).
* `cos_cover`, `cos_disj`: for an action of `G` with `I s ≤ Stab(P s)`, every `γ • P s` (`γ ∈ Γ`) is `g • (x_t • P s)` with
  `g ∈ Γ ∩ ker π`, and such a `t` is unique when `Γ`-conjugate base points coincide and `Γ`-stabilisers lie in `I s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

section Cos

variable {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- The subgroup `π(Γ ∩ I s)` of `π(Γ)`. -/
abbrev cosD (s : S) : Subgroup (Γ.map π) := ((Γ ⊓ I s).map π).subgroupOf (Γ.map π)

/-- Cover points: `Σ s, π(Γ) ⧸ π(Γ ∩ I s)`. -/
abbrev CosT : Type := Σ s : S, (Γ.map π) ⧸ cosD π Γ I s

open Classical in
/-- A lift to `Γ` of the coset representative (`1` on the trivial coset). -/
def cosX (t : CosT π Γ I) : G :=
  if t.2 = ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I t.1) then 1
  else Classical.choose (Subgroup.mem_map.1 (Quotient.out t.2).2)

variable {π Γ I}

theorem cosX_mem (t : CosT π Γ I) : cosX π Γ I t ∈ Γ := by
  unfold cosX
  split_ifs with h
  · exact Γ.one_mem
  · exact (Classical.choose_spec (Subgroup.mem_map.1 (Quotient.out t.2).2)).1

theorem cosX_base (s : S) :
    cosX π Γ I ⟨s, ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩ = 1 := by
  unfold cosX
  rw [if_pos rfl]

theorem cosX_map_mem (t : CosT π Γ I) : π (cosX π Γ I t) ∈ Γ.map π :=
  Subgroup.mem_map_of_mem π (cosX_mem t)

/-- The lift represents its coset. -/
theorem cosX_mk (t : CosT π Γ I) :
    ((⟨π (cosX π Γ I t), cosX_map_mem t⟩ : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I t.1) = t.2 := by
  by_cases h : t.2 = ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I t.1)
  · have hx : cosX π Γ I t = 1 := by unfold cosX; rw [if_pos h]
    have he : (⟨π (cosX π Γ I t), cosX_map_mem t⟩ : Γ.map π) = 1 :=
      Subtype.ext (by show π (cosX π Γ I t) = 1; rw [hx, map_one])
    rw [he]
    exact h.symm
  · have hx : cosX π Γ I t = Classical.choose (Subgroup.mem_map.1 (Quotient.out t.2).2) := by
      unfold cosX; rw [if_neg h]
    have hx' : π (cosX π Γ I t) = ((Quotient.out t.2 : Γ.map π) : Gf) := by
      rw [hx]; exact (Classical.choose_spec (Subgroup.mem_map.1 (Quotient.out t.2).2)).2
    have he : (⟨π (cosX π Γ I t), cosX_map_mem t⟩ : Γ.map π) = Quotient.out t.2 := Subtype.ext hx'
    rw [he]
    exact QuotientGroup.out_eq' t.2

theorem mem_cosD_iff {s : S} (a b : Γ.map π) :
    ((a : (Γ.map π) ⧸ cosD π Γ I s) = (b : (Γ.map π) ⧸ cosD π Γ I s)) ↔
      ((a : Gf))⁻¹ * b ∈ (Γ ⊓ I s).map π := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

/-- **Coset partition** (`hrep`). -/
theorem cos_rep (s : S) (p : Gf) (hp : p ∈ Γ.map π) :
    ∃! t : CosT π Γ I, t.1 = s ∧ (π (cosX π Γ I t))⁻¹ * p ∈ (Γ ⊓ I s).map π := by
  refine ⟨⟨s, ((⟨p, hp⟩ : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩, ⟨rfl, ?_⟩, ?_⟩
  · have h := cosX_mk (π := π) (Γ := Γ) (I := I) ⟨s, ((⟨p, hp⟩ : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩
    exact (mem_cosD_iff (s := s) _ ⟨p, hp⟩).1 h
  · rintro ⟨s', q'⟩ ⟨h1, h2⟩
    dsimp only at h1
    subst h1
    have h := cosX_mk (π := π) (Γ := Γ) (I := I) ⟨_, q'⟩
    have h3 := (mem_cosD_iff ⟨π (cosX π Γ I ⟨_, q'⟩), cosX_map_mem _⟩ ⟨p, hp⟩).2 h2
    dsimp only at h
    rw [h] at h3
    rw [h3]

variable [Finite S] [Finite Gf]

instance finite_cosT : Finite (CosT π Γ I) := by
  have : ∀ s : S, Finite ((Γ.map π) ⧸ cosD π Γ I s) := fun s => Quotient.finite _
  exact Finite.instSigma

end Cos

section Act

variable {G Gf : Type} [Group G] [Group Gf] {π : G →* Gf} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}
  {X : Type} [MulAction G X] {P : S → X}

/-- **Cover**: `γ • P s` (`γ ∈ Γ`) is `g • (x_t • P s)` with `g ∈ Γ ∩ ker π`. -/
theorem cos_cover (hI : ∀ s, ∀ δ ∈ I s, δ • P s = P s) (s : S) {γ : G} (hγ : γ ∈ Γ) :
    ∃ t : CosT π Γ I, t.1 = s ∧ ∃ g ∈ Γ, π g = 1 ∧ γ • P s = g • (cosX π Γ I t • P s) := by
  obtain ⟨t, ⟨ht, hmem⟩, -⟩ := cos_rep (π := π) (Γ := Γ) (I := I) s (π γ) (Subgroup.mem_map_of_mem π hγ)
  obtain ⟨δ, hδ, hδπ⟩ := Subgroup.mem_map.1 hmem
  have hδΓ := (Subgroup.mem_inf.1 hδ).1
  have hδI := (Subgroup.mem_inf.1 hδ).2
  refine ⟨t, ht, γ * δ⁻¹ * (cosX π Γ I t)⁻¹,
    Γ.mul_mem (Γ.mul_mem hγ (Γ.inv_mem hδΓ)) (Γ.inv_mem (cosX_mem t)), ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, map_inv, hδπ]
    group
  · rw [smul_smul, inv_mul_cancel_right, mul_smul, hI s δ⁻¹ ((I s).inv_mem hδI)]

/-- **Disjointness**: the cover point is unique. -/
theorem cos_disj (hdisj : ∀ s s', ∀ u ∈ Γ, P s' = u • P s → s = s')
    (hstab : ∀ s, ∀ u ∈ Γ, u • P s = P s → u ∈ I s) (t t' : CosT π Γ I) {g : G} (hg : g ∈ Γ) (hgπ : π g = 1)
    (h : cosX π Γ I t' • P t'.1 = g • (cosX π Γ I t • P t.1)) : t = t' := by
  obtain ⟨s, q⟩ := t
  obtain ⟨s', q'⟩ := t'
  dsimp only at h
  set u := (cosX π Γ I ⟨s', q'⟩)⁻¹ * g * cosX π Γ I ⟨s, q⟩ with hu
  have huΓ : u ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (cosX_mem _)) hg) (cosX_mem _)
  have hP : P s' = u • P s := by
    rw [hu, mul_smul, mul_smul, ← h, inv_smul_smul]
  have hss : s = s' := hdisj s s' u huΓ hP
  subst hss
  have huI : u ∈ I s := hstab s u huΓ hP.symm
  have hrep := cos_rep (π := π) (Γ := Γ) (I := I) s (π (cosX π Γ I ⟨s, q⟩)) (cosX_map_mem _)
  refine hrep.unique ⟨rfl, ?_⟩ ⟨rfl, ?_⟩
  · rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · refine Subgroup.mem_map.2 ⟨u, Subgroup.mem_inf.2 ⟨huΓ, huI⟩, ?_⟩
    rw [hu, map_mul, map_mul, map_inv, hgπ, mul_one]

end Act

end

end Residue
end RamanujanPetersson

end


