-- Prove2me | Definitions.Def_RPLib_S3_RRC
-- name    : RPLib_S3_RRC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:23:26.758642+00:00
-- url     : https://prove2.me/theorems/366e87fa-719b-4267-a0b6-e13cba129668
-- title:
--   Weight-two Ramanujan-Petersson library: the concrete instance for function fields
-- statement:
--   The concrete instance for function fields.
--
--   The abstract axioms of `RR_A` (`Data.Axioms`) hold for the places of a function field
--   `F / Fq`: the local index `[ball (n+1) : ball n] = q ^ deg P` (generic
--   Dedekind lemma `relIndex_ballG`), the product formula, `L(0)` = constants, and the Riemann
--   input with `B` the pole divisor of `x` and `C` the pole divisor of an integral basis.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_RRB
import Definitions.Def_RPLib_S3_PlacesC

/-!
# Riemann-Roch, part C: the concrete instance for function fields

The abstract axioms of `RR_A` (`Data.Axioms`) hold for the places of a function field
`F / Fq` (unit S3-Places): the local index `[ball (n+1) : ball n] = q ^ deg P` (generic
Dedekind lemma `relIndex_ballG`), the product formula, `L(0)` = constants, and the Riemann
input with `B` the pole divisor of `x` and `C` the pole divisor of an integral basis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.RR

/-! ### The local index at a place of a Dedekind domain -/

section LocalIndex

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {K : Type*} [Field K] [Algebra S K]
  [IsFractionRing S K]

/-- The additive subgroup `{f | v_P f ≤ exp n}`. -/
def ballG (P : HeightOneSpectrum S) (n : ℤ) : AddSubgroup K where
  carrier := {f | P.valuation K f ≤ exp n}
  add_mem' {a b} ha hb := ((P.valuation K).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    show P.valuation K (-a) ≤ exp n
    rw [Valuation.map_neg]; exact ha

theorem mem_ballG {P : HeightOneSpectrum S} {n : ℤ} {f : K} :
    f ∈ ballG P n ↔ P.valuation K f ≤ exp n := Iff.rfl

theorem le_exp_neg_one_iff {x : ℤᵐ⁰} : x ≤ exp (-1) ↔ x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = exp k := ⟨log x, (exp_log hx).symm⟩
    rw [exp_le_exp, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]; omega

theorem exists_valuation_eq_exp (P : HeightOneSpectrum S) (k : ℤ) :
    ∃ c : K, P.valuation K c = exp k := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
  have h1 : ∀ m : ℕ, P.valuation K (π ^ m) = exp (-(m : ℤ)) := fun m => by
    rw [map_pow, hπ, ← exp_nsmul]; congr 1; simp
  have h2 : ∀ m : ℕ, P.valuation K (π⁻¹ ^ m) = exp (m : ℤ) := fun m => by
    rw [map_pow, map_inv₀, hπ, ← exp_neg, ← exp_nsmul]; congr 1; simp
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  exacts [⟨_, h2 m⟩, ⟨_, h1 m⟩]

theorem relIndex_ballG_neg_one (P : HeightOneSpectrum S) :
    (ballG (K := K) P (-1)).relIndex (ballG P 0) = Nat.card (S ⧸ P.asIdeal) := by
  let f : S →+ K := (algebraMap S K).toAddMonoidHom
  have hinj : Function.Injective f := IsFractionRing.injective S K
  have hle : ballG (K := K) P (-1) ≤ ballG P 0 := fun x hx =>
    (mem_ballG.1 hx).trans (exp_le_exp.2 (by norm_num))
  have hR : f.range ≤ ballG (K := K) P 0 := by
    rintro _ ⟨a, rfl⟩; exact P.valuation_le_one a
  rw [relIndex_split f.range hle]
  have h1 : ballG (K := K) P 0 ⊓ f.range = (⊤ : AddSubgroup S).map f := by
    rw [inf_eq_right.2 hR, ← AddMonoidHom.range_eq_map]
  have h2 : ballG (K := K) P (-1) ⊓ f.range = P.asIdeal.toAddSubgroup.map f := by
    ext y; constructor
    · rintro ⟨hy, ⟨a, rfl⟩⟩
      exact ⟨a, (P.valuation_lt_one_iff_mem a).1 (le_exp_neg_one_iff.1 hy), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨le_exp_neg_one_iff.2 ((P.valuation_lt_one_iff_mem a).2 ha), a, rfl⟩
  have h3 : ballG (K := K) P 0 ≤ ballG P (-1) ⊔ f.range := by
    intro x hx
    obtain ⟨a, ha⟩ := P.exists_valuation_sub_lt_of_integer (mem_ballG.1 hx) 1
    have hmem : x - algebraMap S K a ∈ ballG (K := K) P (-1) := by
      rw [mem_ballG, le_exp_neg_one_iff, Valuation.map_sub_swap]; simpa using ha
    exact AddSubgroup.mem_sup.2 ⟨_, hmem, algebraMap S K a, ⟨a, rfl⟩, sub_add_cancel _ _⟩
  rw [h1, h2, sup_eq_left.2 hR, AddSubgroup.relIndex_eq_one.2 h3, mul_one,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_top_right]
  rfl

/-- The local index `[ball P (n+1) : ball P n] = #(S / P)`. -/
theorem relIndex_ballG (P : HeightOneSpectrum S) (n : ℤ) :
    (ballG (K := K) P n).relIndex (ballG P (n + 1)) = Nat.card (S ⧸ P.asIdeal) := by
  obtain ⟨c, hc⟩ := exists_valuation_eq_exp (K := K) P (-(n + 1))
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (exp_ne_zero hc.symm).elim
  let g : K →+ K := AddMonoidHom.mulLeft c
  have e1 : ballG (K := K) P n = (ballG (K := K) P (-1)).comap g := by
    ext x
    simp only [AddSubgroup.mem_comap, mem_ballG, g, AddMonoidHom.coe_mulLeft, map_mul, hc,
      exp_mul_le_exp_iff]
    rw [show (-1 : ℤ) - -(n + 1) = n by ring]
  have e2 : (ballG (K := K) P (n + 1)).map g = ballG P 0 := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      show P.valuation K (c * x) ≤ exp 0
      rw [map_mul, hc, exp_mul_le_exp_iff, show (0 : ℤ) - -(n + 1) = n + 1 by ring]; exact hx
    · intro hy
      refine ⟨c⁻¹ * y, ?_, ?_⟩
      · show P.valuation K (c⁻¹ * y) ≤ exp (n + 1)
        rw [map_mul, map_inv₀, hc, ← exp_neg, exp_mul_le_exp_iff,
          show n + 1 - -(-(n + 1)) = (0 : ℤ) by ring]; exact hy
      · show c * (c⁻¹ * y) = y
        rw [mul_inv_cancel_left₀ hc0]
  rw [e1, AddSubgroup.relIndex_comap, e2, relIndex_ballG_neg_one]

end LocalIndex

/-! ### The data of a function field -/

section FunctionField

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The valuation at a place. -/
noncomputable def ffv : Places.Place Fq F → Valuation F ℤᵐ⁰ :=
  Sum.elim (fun P => P.valuation F) (fun P => P.valuation F)

variable {Fq F}

theorem ord_eq_neg_log (P : Places.Place Fq F) (f : F) : P.ord f = -log (ffv Fq F P f) := by
  rcases P with P | P <;> rfl

theorem ffv_eq_one {P : Places.Place Fq F} {f : F} (hf : f ≠ 0) (h : P.ord f = 0) :
    ffv Fq F P f = 1 := by
  have hv : ffv Fq F P f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  rw [ord_eq_neg_log] at h
  rw [← exp_log hv, show log (ffv Fq F P f) = 0 by omega, exp_zero]

variable (Fq F)

/-- The abstract Riemann-Roch data of a function field. -/
noncomputable def ffData : Data Fq F (Places.Place Fq F) where
  v := ffv Fq F
  deg := Places.Place.deg
  v_algebraMap P c hc := by
    have h0 : algebraMap Fq F c ≠ 0 := (_root_.map_ne_zero _).2 hc
    exact ffv_eq_one h0 (Places.ord_eq_zero_of_mem_constField Fq F
      (IntermediateField.algebraMap_mem _ c) h0 P)
  finite_ne_one f hf := by
    refine (Places.div f : Places.Divisor Fq F).support.finite_toSet.subset fun P hP => ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Places.div_apply]
    exact fun h => hP (ffv_eq_one hf h)

variable {Fq F}

@[simp] theorem ffData_v (P : Places.Place Fq F) : (ffData Fq F).v P = ffv Fq F P := rfl

@[simp] theorem ffData_deg (P : Places.Place Fq F) : (ffData Fq F).deg P = P.deg := rfl

theorem ffData_div (f : F) : (ffData Fq F).div f = Places.div f := by
  ext P
  rw [Data.div_apply, Places.div_apply, ord_eq_neg_log]; rfl

theorem ffData_degD (D : Places.Divisor Fq F) : (ffData Fq F).degD D = D.deg := rfl

theorem ffData_localIndex (P : Places.Place Fq F) (n : ℤ) :
    rI ((ffData Fq F).ball P n) ((ffData Fq F).ball P (n + 1)) =
      Fintype.card Fq ^ (ffData Fq F).deg P := by
  unfold rI
  rcases P with P | P
  · have e : ∀ m : ℤ, ((ffData Fq F).ball (Sum.inl P) m).toAddSubgroup = ballG P m :=
      fun m => AddSubgroup.ext fun _ => Iff.rfl
    rw [e, e, relIndex_ballG, Places.card_residue_eq Fq]; rfl
  · have e : ∀ m : ℤ, ((ffData Fq F).ball (Sum.inr P) m).toAddSubgroup = ballG P m :=
      fun m => AddSubgroup.ext fun _ => Iff.rfl
    rw [e, e, relIndex_ballG, Places.card_residue_eq Fq]; rfl

theorem ffData_finite_L0 : Finite ((ffData Fq F).LD 0) := by
  have hmem : ∀ f : (ffData Fq F).LD 0, (f : F) ∈ Places.constField Fq F := fun f =>
    Places.mem_constField_of_ord_nonneg Fq F fun P => by
      have h := (ffData Fq F).mem_LD.1 f.2 P
      rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero] at h
      rcases P with P | P
      · exact Places.neg_log_nonneg_of_valuation_le_one P h
      · exact Places.neg_log_nonneg_of_valuation_le_one P h
  have : Finite (Places.constField Fq F) := Module.finite_of_finite Fq
  exact Finite.of_injective (fun f => (⟨f, hmem f⟩ : Places.constField Fq F))
    fun f g h => Subtype.ext (congrArg Subtype.val h :)

/-- The local axioms hold for function fields. -/
theorem ffData_axioms0 : (ffData Fq F).Axioms0 where
  nonempty := ⟨Sum.inr (Places.nonempty_infPlace Fq F).some⟩
  deg_pos := Places.Place.deg_pos
  localIndex := ffData_localIndex
  deg_div f hf := by rw [ffData_div, ffData_degD]; exact Places.deg_div hf
  finite_L0 := ffData_finite_L0

end FunctionField

/-! ### The Riemann input -/

section RiemannInput

/-- If `v x ≤ e` with `1 ≤ e` then `v (p(x)) ≤ e ^ m` for `deg p ≤ m`. -/
theorem Data.v_aeval_le {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] (d : Data Fq F ι)
    (i : ι) {x : F} {e : ℤᵐ⁰} (he : 1 ≤ e) (hx : d.v i x ≤ e) {m : ℕ} {p : Fq[X]}
    (hp : p ∈ degreeLT Fq (m + 1)) : d.v i (aeval x p) ≤ e ^ m := by
  have hdeg : p.natDegree < m + 1 := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · exact (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp)
  rw [aeval_eq_sum_range' hdeg]
  refine Valuation.map_sum_le _ fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  by_cases hc : p.coeff j = 0
  · rw [hc, zero_smul, map_zero]; exact zero_le
  · rw [d.v_smul i hc, map_pow]
    exact (pow_le_pow_left₀ zero_le hx j).trans (pow_le_pow_right₀ he hjm)

theorem log_nonpos_iff' {v : ℤᵐ⁰} (hv : v ≠ 0) : log v ≤ 0 ↔ v ≤ 1 := by
  conv_rhs => rw [← exp_log hv]
  rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]

theorem log_nonneg_iff' {v : ℤᵐ⁰} (hv : v ≠ 0) : 0 ≤ log v ↔ 1 ≤ v := by
  conv_rhs => rw [← exp_log hv]
  rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The separating element `x`. -/
noncomputable def xF : F := algebraMap Fq[X] F X

/-- An `Fq[X]`-basis of the ring of integers `Rfin` (an integral basis). -/
noncomputable def bas : Module.Basis (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) Fq[X]
    (Places.Rfin Fq F) :=
  Module.Free.chooseBasis Fq[X] (Places.Rfin Fq F)

/-- The pole divisor of `x`. -/
noncomputable def poleB : Places.Divisor Fq F := (-(ffData Fq F).div (xF Fq F)) ⊔ 0

/-- The sum of the pole divisors of the integral basis. -/
noncomputable def poleC : Places.Divisor Fq F :=
  ∑ k, ((-(ffData Fq F).div (algebraMap (Places.Rfin Fq F) F (bas Fq F k))) ⊔ 0)

variable {Fq F}

theorem xF_ne_zero : xF Fq F ≠ 0 := by
  rw [xF, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Fq[X] F)]; exact X_ne_zero

theorem aeval_xF (q : Fq[X]) : aeval (xF Fq F) q = algebraMap Fq[X] F q := by
  have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom Fq Fq[X] F) X q
  rw [aeval_X_left_apply, IsScalarTower.coe_toAlgHom'] at this
  exact this

theorem xF_inv_eq : (xF Fq F)⁻¹ = algebraMap (Places.Rinf Fq F) F
    (algebraMap (Places.Oinf Fq) (Places.Rinf Fq F) (Places.piInf Fq)) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Places.Oinf Fq) (RatFunc Fq) F]
  show _ = algebraMap (RatFunc Fq) F (1 / RatFunc.X)
  rw [xF, IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F, RatFunc.algebraMap_X, one_div,
    map_inv₀]

theorem ffv_xF_inl (P : HeightOneSpectrum (Places.Rfin Fq F)) :
    ffv Fq F (Sum.inl P) (xF Fq F) ≤ 1 := by
  show P.valuation F (algebraMap Fq[X] F X) ≤ 1
  rw [IsScalarTower.algebraMap_apply Fq[X] (Places.Rfin Fq F) F]
  exact P.valuation_le_one _

theorem one_le_ffv_xF_inr (P : HeightOneSpectrum (Places.Rinf Fq F)) :
    1 ≤ ffv Fq F (Sum.inr P) (xF Fq F) := by
  have h : P.valuation F (xF Fq F)⁻¹ ≤ 1 := by rw [xF_inv_eq]; exact P.valuation_le_one _
  have hv : P.valuation F (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [map_inv₀] at h
  show 1 ≤ P.valuation F (xF Fq F)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, P.valuation F (xF Fq F) = exp k := ⟨_, (exp_log hv).symm⟩
  rw [hk, ← exp_neg, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at h
  rw [hk, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]; omega

theorem poleB_nonneg : 0 ≤ poleB Fq F := le_sup_right

theorem poleC_nonneg : 0 ≤ poleC Fq F := Finset.sum_nonneg fun _ _ => le_sup_right

theorem poleB_eq : poleB Fq F = Finsupp.sumElim 0 (-(Places.divS (Places.Rinf Fq F) (xF Fq F))) := by
  ext P
  have hv : ffv Fq F P (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [poleB, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffData_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  rcases P with P | P
  · rw [Finsupp.sumElim_inl, Finsupp.coe_zero, Pi.zero_apply]
    exact sup_eq_right.2 ((log_nonpos_iff' hv).2 (ffv_xF_inl P))
  · rw [Finsupp.sumElim_inr, Finsupp.neg_apply, Places.divS_apply,
      sup_eq_left.2 ((log_nonneg_iff' hv).2 (one_le_ffv_xF_inr P)), Places.ord, neg_neg]
    rfl

theorem degS_zero' {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S] :
    Places.degS Fq (0 : HeightOneSpectrum S →₀ ℤ) = 0 := by
  simp [Places.degS]

theorem degD_poleB :
    (ffData Fq F).degD (poleB Fq F) =
      Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) := by
  rw [ffData_degD, poleB_eq, Places.Divisor.deg_sumElim, degS_zero', zero_add, ← zero_sub,
    Places.degS_sub, degS_zero', zero_sub]
  have hsum := Places.degS_fin_add_degS_inf Fq F (xF_ne_zero (Fq := Fq) (F := F))
  have hxR : algebraMap Fq[X] (Places.Rfin Fq F) X ≠ 0 := fun h => xF_ne_zero (Fq := Fq) (F := F) (by
    rw [xF, IsScalarTower.algebraMap_apply Fq[X] (Places.Rfin Fq F) F, h, map_zero])
  have e : xF Fq F = algebraMap (Places.Rfin Fq F) F (algebraMap Fq[X] (Places.Rfin Fq F) X) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hfin : Places.degS Fq (Places.divS (Places.Rfin Fq F) (xF Fq F)) =
      Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) := by
    rw [e, Places.degS_fin Fq F hxR, ← Places.norm_bridge_fin Fq F,
      Algebra.norm_algebraMap_of_basis (bas Fq F), RatFunc.intDegree_polynomial, natDegree_X_pow]
  omega

theorem ffv_bas_le (k : Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) (P : Places.Place Fq F) :
    (ffData Fq F).v P (algebraMap (Places.Rfin Fq F) F (bas Fq F k)) ≤ exp (poleC Fq F P) := by
  have hbk : algebraMap (Places.Rfin Fq F) F (bas Fq F k) ≠ 0 := fun h =>
    (bas Fq F).ne_zero k (Subtype.ext h)
  rw [(ffData Fq F).v_eq_exp hbk P, exp_le_exp, poleC, Finsupp.finsetSum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ((-(ffData Fq F).div
    (algebraMap (Places.Rfin Fq F) F (bas Fq F k))) ⊔ 0) P)
    (fun k _ => by rw [Finsupp.sup_apply]; exact le_sup_right) (Finset.mem_univ k))
  rw [Finsupp.sup_apply, Finsupp.neg_apply]
  exact le_sup_left

variable (Fq F) in
/-- `p ↦ Σ_k p_k(x) b_k`, polynomials of degree `≤ m` against the integral basis. -/
noncomputable def Phi (m : ℕ) :
    (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F) → degreeLT Fq (m + 1)) →ₗ[Fq] F where
  toFun p := ∑ k, aeval (xF Fq F) (p k : Fq[X]) * algebraMap (Places.Rfin Fq F) F (bas Fq F k)
  map_add' p q := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c p := by simp [Finset.smul_sum]

theorem Phi_apply (m : ℕ) (p) : Phi Fq F m p =
    ∑ k, aeval (xF Fq F) (p k : Fq[X]) * algebraMap (Places.Rfin Fq F) F (bas Fq F k) := rfl

theorem Phi_mem (m : ℕ) (p) :
    Phi Fq F m p ∈ (ffData Fq F).LD (m • poleB Fq F + poleC Fq F) := by
  rw [Data.mem_LD]
  intro P
  rw [Finsupp.add_apply, Finsupp.smul_apply, exp_add, exp_nsmul, Phi_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  have hB : 0 ≤ poleB Fq F P := poleB_nonneg (Fq := Fq) (F := F) P
  have he : 1 ≤ exp (poleB Fq F P) := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]; exact hB
  have hx : (ffData Fq F).v P (xF Fq F) ≤ exp (poleB Fq F P) := by
    rw [(ffData Fq F).v_eq_exp xF_ne_zero P, exp_le_exp, poleB, Finsupp.sup_apply,
      Finsupp.neg_apply]
    exact le_sup_left
  exact mul_le_mul' ((ffData Fq F).v_aeval_le P he hx (p k).2) (ffv_bas_le k P)

theorem Phi_injective (m : ℕ) : Function.Injective (Phi Fq F m) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hker : LinearMap.ker (IsScalarTower.toAlgHom Fq[X] (Places.Rfin Fq F) F).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 fun a b h => Subtype.ext h
  have hli := Fintype.linearIndependent_iff.1 ((bas Fq F).linearIndependent.map' _ hker)
    (fun k => (p k : Fq[X])) (by
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
        Algebra.smul_def, ← aeval_xF]
      exact hp)
  funext k
  exact Subtype.ext (hli k)

theorem finrank_dom (m : ℕ) :
    Module.finrank Fq (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F) → degreeLT Fq (m + 1)) =
      Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) * (m + 1) := by
  let e := (LinearEquiv.piCongrRight fun _ => degreeLTEquiv Fq (m + 1)).trans
    (LinearEquiv.curry Fq Fq (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) (Fin (m + 1))).symm
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]

theorem ell_ge (m : ℕ) :
    Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) * (m + 1) ≤
      (ffData Fq F).ell (m • poleB Fq F + poleC Fq F) := by
  have := Data.finite_LD (ffData_axioms0 (Fq := Fq) (F := F)) (m • poleB Fq F + poleC Fq F)
  have : Module.Finite Fq ((ffData Fq F).LD (m • poleB Fq F + poleC Fq F)) := Module.Finite.of_finite
  rw [← finrank_dom, Data.ell]
  exact LinearMap.finrank_le_finrank_of_injective (f := (Phi Fq F m).codRestrict _ (Phi_mem m))
    fun p q h => Phi_injective m (congrArg Subtype.val h)

theorem ffData_riemannInput : ∃ B : Places.Divisor Fq F, 0 ≤ B ∧ 0 < (ffData Fq F).degD B ∧
    ∃ C : Places.Divisor Fq F, 0 ≤ C ∧
      ∃ c : ℤ, ∀ n : ℕ, (n : ℤ) * (ffData Fq F).degD B - c ≤ (ffData Fq F).ell (n • B + C) := by
  have := (bas Fq F).index_nonempty
  have hpos : 0 < Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) :=
    Fintype.card_pos
  refine ⟨poleB Fq F, poleB_nonneg, ?_, poleC Fq F, poleC_nonneg, 0, fun n => ?_⟩
  · rw [degD_poleB]; exact_mod_cast hpos
  · rw [degD_poleB]
    have h := ell_ge (Fq := Fq) (F := F) n
    have h' : ((Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) * (n + 1) : ℕ) : ℤ)
        ≤ (ffData Fq F).ell (n • poleB Fq F + poleC Fq F) := by exact_mod_cast h
    push_cast at h'
    nlinarith

/-- **The axioms of the abstract theory hold for function fields.** -/
theorem ffData_axioms : (ffData Fq F).Axioms := ⟨ffData_axioms0, ffData_riemannInput⟩

end RiemannInput

/-! ### Riemann-Roch for function fields -/

section Concrete

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq F) in
/-- The Riemann-Roch space `L(D)` of a function field (over `Fq`). -/
noncomputable abbrev LF (D : Places.Divisor Fq F) : Submodule Fq F := (ffData Fq F).LD D

variable (Fq F) in
/-- `ℓ(D) = dim_Fq L(D)`. -/
noncomputable abbrev ellF (D : Places.Divisor Fq F) : ℕ := (ffData Fq F).ell D

variable (Fq F) in
/-- The genus of `F` (over `Fq`): `g = dim_Fq A / (A(0) + F)`. -/
noncomputable abbrev genusF : ℕ := (ffData Fq F).genus

variable (Fq F) in
/-- `W` is a canonical divisor of `F` (the divisor of a nonzero Weil differential). -/
abbrev IsCanonicalF (W : Places.Divisor Fq F) : Prop := (ffData Fq F).IsCanonical W

theorem mem_LF {D : Places.Divisor Fq F} {f : F} (hf : f ≠ 0) :
    f ∈ LF Fq F D ↔ 0 ≤ Places.div f + D := by
  rw [(ffData Fq F).mem_LD_iff_div hf, ffData_div]

theorem finiteDimensional_LF (D : Places.Divisor Fq F) : FiniteDimensional Fq (LF Fq F D) := by
  have := Data.finite_LD (ffData_axioms0 (Fq := Fq) (F := F)) D
  exact Module.Finite.of_finite

theorem card_LF (D : Places.Divisor Fq F) :
    Nat.card (LF Fq F D) = Fintype.card Fq ^ ellF Fq F D :=
  Data.card_LD ffData_axioms0 D

/-- `L(0)` is the full constant field. -/
theorem LF_zero_eq :
    LF Fq F 0 = Subalgebra.toSubmodule (Places.constField Fq F).toSubalgebra := by
  ext f
  rw [Data.mem_LD, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
  constructor
  · intro h
    exact Places.mem_constField_of_ord_nonneg Fq F fun P => by
      have h1 := h P
      rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero] at h1
      rcases P with P | P
      · exact Places.neg_log_nonneg_of_valuation_le_one P h1
      · exact Places.neg_log_nonneg_of_valuation_le_one P h1
  · intro hf P
    rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero]
    rcases P with P | P
    · exact Places.valuation_le_one_of_neg_log_nonneg P
        (Places.ord_nonneg_of_mem_constField Fq F hf (Sum.inl P))
    · exact Places.valuation_le_one_of_neg_log_nonneg P
        (Places.ord_nonneg_of_mem_constField Fq F hf (Sum.inr P))

/-- `ℓ(0) = [k : Fq]` for the full constant field `k`. -/
theorem ellF_zero : ellF Fq F 0 = Module.finrank Fq (Places.constField Fq F) := by
  rw [ellF, Data.ell, show (ffData Fq F).LD 0 = _ from LF_zero_eq]
  rfl

theorem ellF_zero_of_bot (h : Places.constField Fq F = ⊥) : ellF Fq F 0 = 1 := by
  rw [ellF_zero, h, IntermediateField.finrank_bot]

/-- A place of degree one forces `ℓ(0) = 1`. -/
theorem ellF_zero_of_deg_one {P : Places.Place Fq F} (hP : P.deg = 1) : ellF Fq F 0 = 1 :=
  ellF_zero_of_bot (Places.constField_eq_bot_of_deg_one Fq F hP)

theorem ellF_eq_zero_of_deg_neg {D : Places.Divisor Fq F} (hD : D.deg < 0) : ellF Fq F D = 0 :=
  Data.ell_eq_zero_of_degD_neg ffData_axioms hD

/-- The index formula `[A : A(D) + F] = q ^ (ℓ D - deg D + γ)`. -/
theorem rI_adelesF (D : Places.Divisor Fq F) :
    rI ((ffData Fq F).AD D ⊔ (ffData Fq F).Fs) (ffData Fq F).adeles =
      Fintype.card Fq ^ (ffData Fq F).iota D :=
  Data.rI_adeles ffData_axioms D

theorem genusF_eq_iota : genusF Fq F = (ffData Fq F).iota 0 := rfl

/-- The Weil differentials form a one-dimensional `F`-vector space. -/
theorem weilDiffF_one_dim :
    ∃ ω : Module.Dual Fq (ffData Fq F).adeles, (ffData Fq F).IsWeilDiff ω ∧ ω ≠ 0 ∧
      ∀ ω' : Module.Dual Fq (ffData Fq F).adeles, (ffData Fq F).IsWeilDiff ω' →
        ∃! x : F, ω' = (ffData Fq F).wsmul x ω :=
  Data.weilDiff_one_dim ffData_axioms

theorem exists_isCanonicalF : ∃ W : Places.Divisor Fq F, IsCanonicalF Fq F W :=
  Data.exists_isCanonical ffData_axioms

/-- Canonical divisors form one linear equivalence class. -/
theorem isCanonicalF_eq_add_div {W W' : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W)
    (hW' : IsCanonicalF Fq F W') : ∃ x : F, x ≠ 0 ∧ W' = W + Places.div x := by
  obtain ⟨x, hx, h⟩ := Data.isCanonical_eq_add_div ffData_axioms hW hW'
  exact ⟨x, hx, by rw [h, ffData_div]⟩

theorem isCanonicalF_add_div {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) {x : F}
    (hx : x ≠ 0) : IsCanonicalF Fq F (W + Places.div x) := by
  have := (ffData Fq F).isCanonical_add_div hW hx
  rwa [ffData_div] at this

/-- **Riemann-Roch** (general constant field): `ℓ(D) - ℓ(W - D) = deg D + ℓ(0) - g`. -/
theorem riemannRochF {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) (D : Places.Divisor Fq F) :
    (ellF Fq F D : ℤ) - ellF Fq F (W - D) = D.deg + ellF Fq F 0 - genusF Fq F :=
  Data.riemannRoch ffData_axioms hW D

theorem riemann_inequalityF (D : Places.Divisor Fq F) :
    D.deg + ellF Fq F 0 - genusF Fq F ≤ ellF Fq F D :=
  Data.riemann_inequality ffData_axioms D

/-! #### The classical statements (full constant field `Fq`, so `ℓ(0) = 1`) -/

section FullConstantField

variable (hk : Places.constField Fq F = ⊥)
include hk

/-- **Riemann-Roch**: `ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/
theorem riemannRochF' {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W)
    (D : Places.Divisor Fq F) :
    (ellF Fq F D : ℤ) - ellF Fq F (W - D) = D.deg + 1 - genusF Fq F := by
  have := riemannRochF hW D
  rw [ellF_zero_of_bot hk] at this
  exact_mod_cast this

/-- Riemann's inequality `ℓ(D) ≥ deg D + 1 - g`. -/
theorem riemann_inequalityF' (D : Places.Divisor Fq F) :
    D.deg + 1 - genusF Fq F ≤ ellF Fq F D := by
  have := riemann_inequalityF (Fq := Fq) (F := F) D
  rw [ellF_zero_of_bot hk] at this
  exact_mod_cast this

/-- `ℓ(W) = g`. -/
theorem ellF_canonical {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) :
    ellF Fq F W = genusF Fq F :=
  Data.ell_canonical ffData_axioms hW

/-- `deg W = 2g - 2`. -/
theorem degF_canonical {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) :
    W.deg = 2 * (genusF Fq F : ℤ) - 2 := by
  have := Data.degD_canonical ffData_axioms hW
  rw [ffData_degD] at this
  rw [this]
  have h1 := ellF_zero_of_bot hk
  simp only [ellF] at h1
  rw [h1]; push_cast; ring

/-- `ℓ(D) = deg D + 1 - g` for `deg D ≥ 2g - 1`. -/
theorem ellF_eq_of_deg {D : Places.Divisor Fq F} (hD : 2 * (genusF Fq F : ℤ) - 1 ≤ D.deg) :
    (ellF Fq F D : ℤ) = D.deg + 1 - genusF Fq F := by
  have h1 := ellF_zero_of_bot hk
  simp only [ellF] at h1
  have hD' : 2 * ((ffData Fq F).genus : ℤ) - 1 ≤ D.deg := hD
  have := Data.ell_eq_of_large_degD ffData_axioms (D := D) (by
    rw [ffData_degD, h1]; push_cast; omega)
  rw [this, h1, ffData_degD]; push_cast; ring

/-- `ℓ(D) ≤ deg D + 1` for `deg D ≥ 0`. -/
theorem ellF_le {D : Places.Divisor Fq F} (hD : 0 ≤ D.deg) : (ellF Fq F D : ℤ) ≤ D.deg + 1 := by
  have h1 := ellF_zero_of_bot hk
  simp only [ellF] at h1
  have := Data.ell_le_degD_add ffData_axioms (D := D) hD
  rw [h1] at this
  exact_mod_cast this

end FullConstantField

end Concrete

end RamanujanPetersson.RR


