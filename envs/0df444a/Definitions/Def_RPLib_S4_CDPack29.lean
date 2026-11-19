-- Prove2me | Definitions.Def_RPLib_S4_CDPack29
-- name    : RPLib_S4_CDPack29
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:11:21.374338+00:00
-- url     : https://prove2.me/theorems/6fa0f93f-655c-491f-acc5-3cb72087a90a
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 29 of 71
-- statement:
--   Part 29 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_SecB`: The Jacobian (unit S4-JacComplete), part `SecB` (sections with exact poles and a full reduced zero set)
--   * `Def_RP_JacLaw_Bridge`: S4-JacLaw, file O10a: open immersions from maps that are inverse at points
--   * `Def_RP_JacLaw_Sch`: S4-JacLaw, file O10b: from algebraic chunk data on `R` to a `StrictChunk` on `Spec R`
--   * `Def_RP_JacLaw_ShrinkA`: S4-JacLaw, file O10d-1: tools for shrinking a chunk
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack28c
import Definitions.Def_RPLib_S4_CDPack26

/-!
# Curve-duality library package, part 29 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_SecB`: The Jacobian (unit S4-JacComplete), part `SecB` (sections with exact poles and a full reduced zero set)
* `Def_RP_JacLaw_Bridge`: S4-JacLaw, file O10a: open immersions from maps that are inverse at points
* `Def_RP_JacLaw_Sch`: S4-JacLaw, file O10b: from algebraic chunk data on `R` to a `StrictChunk` on `Spec R`
* `Def_RP_JacLaw_ShrinkA`: S4-JacLaw, file O10d-1: tools for shrinking a chunk
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_SecB =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `SecB` (sections with exact poles and a full reduced zero set)

* `card_of_cnt_le_one`: converse of `div_of_card`: if all zeros of `s` are simple, `#Z = deg Hn`.
* `exactPoleH_of_nonpos`: no zeros at infinity gives `ExactPoleH s (poleDiv s)`.
* `ord_inr_prod`: `q(x) = ∏_{c ∈ Λ} (x - c)` has a pole of order `≥ #Λ` at every infinite place.
* `secOf g Λ := g · q_Λ(x)`; **`exists_secOf`**: for `g ≠ 0` with simple zeros, for all large generic `Λ`,
  `secOf g Λ` has exact poles, only simple zeros, and zero set `Z(g) ∪ {x ∈ Λ}`.
* **`exists_secP`**: through every closed point there is such a family of sections.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw

section SecB

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Converse of `div_of_card`.** -/
theorem card_of_cnt_le_one {s : Rfin K F} {Hn : Places.Divisor K F} (hs0 : s ≠ 0) (hHn : IsInf Hn)
    (hs : ExactPoleH s Hn) (h1 : ∀ φ, Places.cnt (ptP φ) s ≤ 1) {Z : Finset (Rfin K F →ₐ[K] K)}
    (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0) : (Z.card : ℤ) = Hn.deg := by
  have hT : (PlacesK.finite_cnt hs0).toFinset = Z.image ptP := by
    ext P
    obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · intro h
      exact ⟨φ, (hZ φ).2 (mem_ptP.1 ((cnt_ne_zero_iff _ hs0).1 h)), rfl⟩
    · rintro ⟨ψ, hψ, e⟩
      rw [← e]
      exact (cnt_ne_zero_iff _ hs0).2 (mem_ptP.2 ((hZ ψ).1 hψ))
  have hA := PlacesK.finrank_quot_span (K := K) hs0
  have h2 := finrank_quot_of_exactPoleH hs0 hHn hs
  rw [hT, Finset.sum_image (fun a _ b _ e => ptP_injective e)] at hA
  simp only [deg_eq_one, mul_one] at hA
  have hone : ∀ φ ∈ Z, Places.cnt (ptP φ) s = 1 := fun φ hφ => by
    have := (cnt_ne_zero_iff _ hs0).2 (mem_ptP.2 ((hZ φ).1 hφ))
    have := h1 φ
    omega
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one] at hA
  rw [← hA]
  exact h2

theorem exactPoleH_of_nonpos {s : Rfin K F} (hs : ∀ Q : HeightOneSpectrum (Rinf K F), Places.ord Q (incB K F s) ≤ 0) :
    ExactPoleH s (poleDiv (K := K) (incB K F s)) := by
  intro P
  have := hs P
  simp only [poleDiv, Finsupp.sup_apply, Finsupp.neg_apply, PlacesK.div_apply, Places.Place.ord_inr,
    Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem ord_inr_x_sub (Q : HeightOneSpectrum (Rinf K F)) (c : K) :
    Places.ord Q (algebraMap K[X] F X - algebraMap K F c) ≤ -1 := by
  have hx := one_lt_placeVal_inr_x (K := K) (F := F) Q
  have hc : placeVal (Sum.inr Q : Place K F) (algebraMap K F c) < placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X) := by
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, map_zero]; exact lt_trans zero_lt_one hx
    · rw [placeVal_algebraMap _ hc0]; exact hx
  have e := Valuation.map_sub_eq_of_lt_left (placeVal (Sum.inr Q : Place K F)) hc
  have hx0 : placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : (0 : ℤ) < WithZero.log (placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X)) := by
    have := (WithZero.log_lt_log one_ne_zero hx0).2 hx
    rwa [WithZero.log_one] at this
  have h := ord_eq_neg_log (Sum.inr Q : Place K F) (algebraMap K[X] F X - algebraMap K F c)
  change Places.ord Q _ = _ at h
  rw [e] at h
  omega

theorem ord_inr_prodF (Q : HeightOneSpectrum (Rinf K F)) (Λ : Finset K) :
    Places.ord Q (∏ c ∈ Λ, (algebraMap K[X] F X - algebraMap K F c)) ≤ -(Λ.card : ℤ) := by
  have hne : ∀ b : K, algebraMap K[X] F X - algebraMap K F b ≠ 0 := fun b h0 => by
    have := ord_inr_x_sub (F := F) Q b
    rw [h0] at this
    simp [Places.ord] at this
  induction Λ using Finset.induction_on with
  | empty => simp [Places.ord]
  | insert a Λ ha ih =>
    have h1 := ord_inr_x_sub (F := F) Q a
    have hP : ∏ c ∈ Λ, (algebraMap K[X] F X - algebraMap K F c) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b _ => hne b
    rw [Finset.prod_insert ha, PlacesK.ord_mul Q (hne a) hP, Finset.card_insert_of_notMem ha]
    push_cast
    omega

theorem incB_prod (Λ : Finset K) :
    incB K F (algebraMap K[X] (Rfin K F) (∏ c ∈ Λ, (X - C c))) =
      ∏ c ∈ Λ, (algebraMap K[X] F X - algebraMap K F c) := by
  rw [incB_apply, ← IsScalarTower.algebraMap_apply, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [map_sub, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem ord_inr_prod (Q : HeightOneSpectrum (Rinf K F)) (Λ : Finset K) :
    Places.ord Q (incB K F (algebraMap K[X] (Rfin K F) (∏ c ∈ Λ, (X - C c)))) ≤ -(Λ.card : ℤ) := by
  rw [incB_prod]
  exact ord_inr_prodF Q Λ

/-- `g · ∏_{c ∈ Λ} (x - c)`. -/
noncomputable def secOf (g : Rfin K F) (Λ : Finset K) : Rfin K F :=
  g * algebraMap K[X] (Rfin K F) (∏ c ∈ Λ, (X - C c))

theorem secOf_ne_zero {g : Rfin K F} (hg0 : g ≠ 0) (Λ : Finset K) : secOf g Λ ≠ 0 :=
  mul_ne_zero hg0 ((map_ne_zero_iff _ algebraMap_poly_injective).2
    (Finset.prod_ne_zero_iff.2 fun c _ => X_sub_C_ne_zero c))

theorem apply_secOf (φ : Rfin K F →ₐ[K] K) (g : Rfin K F) (Λ : Finset K) :
    φ (secOf g Λ) = 0 ↔ φ g = 0 ∨ φ (xB K F) ∈ Λ := by
  rw [secOf, map_mul, mul_eq_zero, apply_poly, eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- **Sections through the zeros of `g` with exact poles and simple zeros.** -/
theorem exists_secOf {g : Rfin K F} (hg0 : g ≠ 0) (hg1 : ∀ φ, Places.cnt (ptP φ) g ≤ 1) :
    ∃ a : K[X], a ≠ 0 ∧ ∃ N : ℕ, ∀ Λ : Finset K, (∀ c ∈ Λ, a.eval c ≠ 0) → N ≤ Λ.card →
      ExactPoleH (secOf g Λ) (poleDiv (K := K) (incB K F (secOf g Λ))) ∧
        ∀ φ, Places.cnt (ptP φ) (secOf g Λ) ≤ 1 := by
  obtain ⟨a0, ha0, hfib⟩ := exists_fib_data (K := K) (F := F)
  set Zg := (finite_zero hg0).toFinset with hZg
  refine ⟨a0 * ∏ φ ∈ Zg, (X - C (φ (xB K F))), mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun φ _ =>
    X_sub_C_ne_zero _), ∑ Q ∈ (Set.finite_univ (α := HeightOneSpectrum (Rinf K F))).toFinset,
    (Places.ord Q (incB K F g)).toNat, fun Λ hΛ hN => ?_⟩
  have hΛ0 : ∀ c ∈ Λ, a0.eval c ≠ 0 := fun c hc => by
    have h := hΛ c hc
    rw [eval_mul] at h
    exact left_ne_zero_of_mul h
  have hΛg : ∀ c ∈ Λ, ∀ φ : Rfin K F →ₐ[K] K, φ g = 0 → φ (xB K F) ≠ c := fun c hc φ hφ e => by
    have h := hΛ c hc
    rw [eval_mul, eval_prod] at h
    exact h (mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero ((finite_zero hg0).mem_toFinset.2 hφ)
      (by rw [eval_sub, eval_X, eval_C, e, sub_self]))))
  set q : K[X] := ∏ c ∈ Λ, (X - C c) with hq
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => X_sub_C_ne_zero c
  have hsq0 : algebraMap K[X] (Rfin K F) q ≠ 0 := (map_ne_zero_iff _ algebraMap_poly_injective).2 hq0
  obtain ⟨s', Zq, -, -, -, -, hZx, hZc⟩ := hfib Λ hΛ0
  have hZq : ∀ φ, φ ∈ Zq ↔ φ (algebraMap K[X] (Rfin K F) q) = 0 := fun φ => by
    rw [hZx, apply_poly φ q, hq, eval_prod, Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  have hqdeg : q.natDegree = Λ.card := by
    rw [hq, natDegree_prod _ _ fun c _ => X_sub_C_ne_zero c]
    simp
  have hdiv := div_of_card hsq0 (isInf_poleDiv _) (exactPoleH_poly hq0) hZq
    (by rw [deg_poleDiv_poly hq0, hqdeg, hZc])
  have hq1 : ∀ φ, Places.cnt (ptP φ) (algebraMap K[X] (Rfin K F) q) ≤ 1 := fun φ => by
    have e := congrArg (fun D : Places.Divisor K F => D (Sum.inl (ptP φ))) hdiv
    simp only [PlacesK.div_apply, Finsupp.coe_sub, Pi.sub_apply] at e
    have h1 := Zdiv_le_one Zq (Sum.inl (ptP φ) : Place K F)
    have h2 := isInf_poleDiv (K := K) (F := F) (algebraMap K[X] (Rfin K F) q) (ptP φ)
    have h3 := cnt_eq_ord φ hsq0
    rw [h2] at e
    omega
  have hmul : ∀ φ, (Places.cnt (ptP φ) (secOf g Λ) : ℤ) =
      Places.cnt (ptP φ) g + Places.cnt (ptP φ) (algebraMap K[X] (Rfin K F) q) := fun φ => by
    rw [cnt_eq_ord φ (secOf_ne_zero hg0 Λ), cnt_eq_ord φ hg0, cnt_eq_ord φ hsq0, secOf, map_mul]
    exact PlacesK.Place.ord_mul _ (incB_ne_zero hg0) (incB_ne_zero hsq0)
  refine ⟨exactPoleH_of_nonpos fun Q => ?_, fun φ => ?_⟩
  · have h1 := ord_inr_prod (F := F) Q Λ
    have h2 : (Places.ord Q (incB K F g)).toNat ≤ ∑ Q ∈ (Set.finite_univ (α := HeightOneSpectrum (Rinf K F))).toFinset,
        (Places.ord Q (incB K F g)).toNat :=
      Finset.single_le_sum (f := fun Q => (Places.ord Q (incB K F g)).toNat) (fun _ _ => Nat.zero_le _)
        ((Set.Finite.mem_toFinset _).2 (Set.mem_univ Q))
    have h3 := Int.self_le_toNat (Places.ord Q (incB K F g))
    have h4 := PlacesK.ord_mul Q (incB_ne_zero hg0) (incB_ne_zero hsq0)
    rw [secOf, map_mul, h4]
    rw [← hq] at h1
    have h5 : ((Places.ord Q (incB K F g)).toNat : ℤ) ≤ (Λ.card : ℤ) := by exact_mod_cast h2.trans hN
    omega
  · have h := hmul φ
    by_cases hφ : φ g = 0
    · have hq' : Places.cnt (ptP φ) (algebraMap K[X] (Rfin K F) q) = 0 := by
        by_contra hne
        have h0 := (hZq φ).2 (mem_ptP.1 ((cnt_ne_zero_iff _ hsq0).1 hne))
        exact hΛg _ ((hZx φ).1 h0) φ hφ rfl
      have := hg1 φ
      omega
    · have hg' : Places.cnt (ptP φ) g = 0 := by
        by_contra hne
        exact hφ (mem_ptP.1 ((cnt_ne_zero_iff _ hg0).1 hne))
      have := hq1 φ
      omega

/-- **Sections through a closed point** (input of `exists_role`). -/
theorem exists_secP (φ0 : Rfin K F →ₐ[K] K) : ∃ g : Rfin K F, g ≠ 0 ∧ φ0 g = 0 ∧ ∃ a : K[X], a ≠ 0 ∧ ∃ N : ℕ,
    ∀ Λ : Finset K, (∀ c ∈ Λ, a.eval c ≠ 0) → N ≤ Λ.card →
      ExactPoleH (secOf g Λ) (poleDiv (K := K) (incB K F (secOf g Λ))) ∧
        ∀ φ, Places.cnt (ptP φ) (secOf g Λ) ≤ 1 := by
  obtain ⟨g, hg0, hφ0, hg1⟩ := exists_simple φ0
  exact ⟨g, hg0, hφ0, exists_secOf hg0 hg1⟩

end SecB

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacLaw_Bridge =====
section

/-!
# S4-JacLaw, file O10a: open immersions from maps that are inverse at points

`T` reduced of finite type over an algebraically closed field `K`. If `f : T → T[1/ω]` and `g : T → T[1/ω']`
are mutually inverse at `K`-points (`h3`, `h4`) and `f` sends `D(ω)` into `D(ω')` (`h1`), then
`Spec f : Spec T[1/ω] ⟶ Spec T` is an open immersion (`isOpenImmersion_of_ptInv`): `f` factors as
`T → T[1/ω'] → T[1/ω'][1/g(ω)] ≅ T[1/ω]`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory AlgebraicGeometry

universe u

section Away

variable {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T]

/-- The structure map `T → T[1/ω]` as a `K`-algebra map. -/
noncomputable abbrev awayι (ω : T) : T →ₐ[K] Localization.Away ω := IsScalarTower.toAlgHom K T _

theorem awayι_apply (ω t : T) : awayι (K := K) ω t = algebraMap T _ t := rfl

/-- Maps out of `T[1/ω]` are determined on `T`. -/
theorem away_algHom_ext {ω : T} {C : Type*} [CommRing C] [Algebra K C]
    {f g : Localization.Away ω →ₐ[K] C} (h : f.comp (awayι ω) = g.comp (awayι ω)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (Submonoid.powers ω) (RingHom.ext fun t => ?_)
  exact DFunLike.congr_fun h t

end Away

section OI

variable {K : Type u} [Field K] [IsAlgClosed K] {T : Type u} [CommRing T] [Algebra K T] [IsReduced T]
  [Algebra.FiniteType K T]

/-- If `f : T → T[1/ω]` and `g : T → T[1/ω']` are inverse at points and `f` maps `D(ω)` into `D(ω')`, then
`Spec f` is an open immersion. -/
theorem isOpenImmersion_of_ptInv {ω ω' : T} (f : T →ₐ[K] Localization.Away ω)
    (g : T →ₐ[K] Localization.Away ω')
    (h1 : ∀ x : Localization.Away ω →ₐ[K] K, x (f ω') ≠ 0)
    (h3 : ∀ (x : Localization.Away ω →ₐ[K] K) (y : Localization.Away ω' →ₐ[K] K),
      y.comp (awayι ω') = x.comp f → y.comp g = x.comp (awayι ω))
    (h4 : ∀ (y : Localization.Away ω' →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
      x.comp (awayι ω) = y.comp g → x.comp f = y.comp (awayι ω')) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (f : T →+* Localization.Away ω))) := by
  have hu : IsUnit (f ω') := isUnit_of_forall_ne_zero (k := K) _ h1
  obtain ⟨ft, hft⟩ : ∃ ft : Localization.Away ω' →ₐ[K] Localization.Away ω, ft.comp (awayι ω') = f :=
    ⟨IsLocalization.Away.liftAlgHom ω' hu, by
      refine AlgHom.ext fun t => ?_; rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq]; rfl⟩
  have hfg : ft.comp g = awayι ω := by
    apply algHom_ext_pts (k := K)
    intro x
    have := h3 x (x.comp ft) (by rw [AlgHom.comp_assoc, hft])
    rw [← AlgHom.comp_assoc, this]
  have hu2 : IsUnit (ft (g ω)) := by
    rw [← AlgHom.comp_apply, hfg]; exact IsLocalization.Away.algebraMap_isUnit ω
  obtain ⟨F, hF⟩ : ∃ F : Localization.Away (g ω) →ₐ[K] Localization.Away ω, F.comp (awayι (g ω)) = ft :=
    ⟨IsLocalization.Away.liftAlgHom (g ω) hu2, by
      refine AlgHom.ext fun t => ?_; rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq]; rfl⟩
  have hι2 : IsUnit (((awayι (g ω)).comp g) ω) := IsLocalization.Away.algebraMap_isUnit (g ω)
  obtain ⟨G, hG⟩ : ∃ G : Localization.Away ω →ₐ[K] Localization.Away (g ω),
      G.comp (awayι ω) = (awayι (g ω)).comp g :=
    ⟨IsLocalization.Away.liftAlgHom ω hι2, by
      refine AlgHom.ext fun t => ?_; rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq]; rfl⟩
  have hFG : F.comp G = AlgHom.id K _ := by
    apply away_algHom_ext
    rw [AlgHom.comp_assoc, hG, AlgHom.id_comp, ← AlgHom.comp_assoc, hF, hfg]
  have hGf : G.comp f = (awayι (g ω)).comp (awayι ω') := by
    apply algHom_ext_pts (k := K)
    intro y2
    have hx : (y2.comp G).comp (awayι ω) = ((y2.comp (awayι (g ω)))).comp g := by
      rw [AlgHom.comp_assoc, hG]; rfl
    have := h4 (y2.comp (awayι (g ω))) (y2.comp G) hx
    rw [← AlgHom.comp_assoc, this]; rfl
  have hGF : G.comp F = AlgHom.id K _ := by
    apply away_algHom_ext
    apply away_algHom_ext
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, ← AlgHom.comp_assoc F, hF, hft, hGf, AlgHom.id_comp]
  have hiso : IsIso (CommRingCat.ofHom (F : Localization.Away (g ω) →+* Localization.Away ω)) := by
    refine ⟨⟨CommRingCat.ofHom (G : Localization.Away ω →+* Localization.Away (g ω)), ?_, ?_⟩⟩
    · ext a; simpa using DFunLike.congr_fun hGF a
    · ext a; simpa using DFunLike.congr_fun hFG a
  have hfac : CommRingCat.ofHom (f : T →+* Localization.Away ω) =
      CommRingCat.ofHom (algebraMap T (Localization.Away ω')) ≫
        CommRingCat.ofHom (algebraMap (Localization.Away ω') (Localization.Away (g ω))) ≫
          CommRingCat.ofHom (F : Localization.Away (g ω) →+* Localization.Away ω) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun t => ?_
    show f t = F (algebraMap _ _ (algebraMap T _ t))
    rw [← hft, ← hF]; rfl
  rw [hfac, Spec.map_comp, Spec.map_comp]
  infer_instance

end OI

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Sch =====
section

/-!
# S4-JacLaw, file O10b: from algebraic chunk data on `R` to a `StrictChunk` on `Spec R`

* `kpt x`: the point of `Spec A` of a `K`-point `x : A →ₐ[K] K`; `comap_kpt`, `kpt_injective`, `isClosed_kpt`,
  `exists_kpt` (closed points are `kpt`s for `K` algebraically closed and `A` of finite type), `SpecMap_kpt`.
* `AffChunk K R`: a law `μ : R → (R ⊗ R)[1/ω]` with point-level inverse data for `Φ = (pr₁, m)` and `Ψ = (m, pr₂)`
  (the hypotheses of `isOpenImmersion_of_ptInv`), fibres and associativity at `K`-points.
* `AffChunk.toStrict`: the `StrictChunk` on `Spec R` (structure map `sR K R`), `Ω = D(ω) ⊆ Spec (R ⊗ R) ≅ X ×_K X`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory Limits AlgebraicGeometry RamanujanPetersson.JacSym RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Kpt

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- The point of `Spec A` of a `K`-point (its kernel). -/
def kpt (x : A →ₐ[K] K) : Spec (.of A) := (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum A)

theorem kpt_asIdeal (x : A →ₐ[K] K) : PrimeSpectrum.asIdeal (R := A) (kpt x) = RingHom.ker x := rfl

theorem kpt_injective : Function.Injective (kpt (K := K) (A := A)) := fun _ _ h =>
  algHom_eq_of_ker_eq (congrArg (fun p : Spec (.of A) => PrimeSpectrum.asIdeal (R := A) p) h)

theorem isClosed_kpt (x : A →ₐ[K] K) : IsClosed ({kpt x} : Set (Spec (.of A))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) (kpt x)).2 (ker_isMaximal x)

theorem exists_kpt [IsAlgClosed K] [Algebra.FiniteType K A] (p : Spec (.of A))
    (hp : IsClosed ({p} : Set (Spec (.of A)))) : ∃ x : A →ₐ[K] K, kpt x = p := by
  have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) p).1 hp
  obtain ⟨x, hx⟩ := exists_algHom_ker_eq (k := K) (PrimeSpectrum.asIdeal (R := A) p)
  exact ⟨x, PrimeSpectrum.ext (R := A) hx⟩

theorem SpecMap_kpt {B : Type u} [CommRing B] [Algebra K B] (f : A →ₐ[K] B) (x : B →ₐ[K] K) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) (kpt x) = kpt (x.comp f) :=
  PrimeSpectrum.ext (R := A) (Ideal.ext fun _ => Iff.rfl)

end Kpt

section Sch

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]

theorem SpecMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B]
    [Algebra K C] (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    Spec.map (CommRingCat.ofHom (g : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) =
      Spec.map (CommRingCat.ofHom ((g.comp f : A →ₐ[K] C) : A →+* C)) := by
  rw [← Spec.map_comp]; rfl

instance isDomain_RR [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R] : IsDomain (R ⊗[K] R) :=
  isDomain_tensor (k := K) (B := R) (A := R)

instance finiteType_RR [Algebra.FiniteType K R] : Algebra.FiniteType K (R ⊗[K] R) :=
  Algebra.FiniteType.trans (S := R) inferInstance inferInstance

/-- The structure map of `Spec R` over `Spec K`. -/
noncomputable abbrev sR (K R : Type u) [Field K] [CommRing R] [Algebra K R] : Spec (.of R) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K R))

/-- `(x, y) ↦ (x, m(x,y))` on functions. -/
noncomputable def phiS {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : R ⊗[K] R →ₐ[K] Localization.Away ω :=
  Algebra.TensorProduct.lift ((awayι ω).comp includeLeft) μ fun _ _ => Commute.all _ _

/-- `(x, y) ↦ (m(x,y), y)` on functions. -/
noncomputable def psiS {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : R ⊗[K] R →ₐ[K] Localization.Away ω :=
  Algebra.TensorProduct.lift μ ((awayι ω).comp includeRight) fun _ _ => Commute.all _ _

theorem phiS_incL {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) :
    (phiS μ).comp includeLeft = (awayι ω).comp includeLeft :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem phiS_incR {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : (phiS μ).comp includeRight = μ :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

theorem psiS_incL {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) : (psiS μ).comp includeLeft = μ :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem psiS_incR {ω : R ⊗[K] R} (μ : R →ₐ[K] Localization.Away ω) :
    (psiS μ).comp includeRight = (awayι ω).comp includeRight :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

/-- First coordinate of a `K`-point of `D(ω) ⊆ Spec (R ⊗ R)`. -/
noncomputable abbrev pL {ω : R ⊗[K] R} (x : Localization.Away ω →ₐ[K] K) : R →ₐ[K] K :=
  x.comp ((awayι ω).comp includeLeft)

/-- Second coordinate of a `K`-point of `D(ω) ⊆ Spec (R ⊗ R)`. -/
noncomputable abbrev pR {ω : R ⊗[K] R} (x : Localization.Away ω →ₐ[K] K) : R →ₐ[K] K :=
  x.comp ((awayι ω).comp includeRight)

/-- Algebraic strict-chunk data on `R`: a law `μ` on `D(ω) ⊆ Spec (R ⊗ R)`; `Φ = (pr₁, m)` and `Ψ = (m, pr₂)`
satisfy the hypotheses of `isOpenImmersion_of_ptInv`; fibres and associativity at `K`-points. -/
structure AffChunk (K R : Type u) [Field K] [CommRing R] [Algebra K R] where
  ω : R ⊗[K] R
  μ : R →ₐ[K] Localization.Away ω
  ωΦ : R ⊗[K] R
  gΦ : R ⊗[K] R →ₐ[K] Localization.Away ωΦ
  Φ1 : ∀ x : Localization.Away ω →ₐ[K] K, x (phiS μ ωΦ) ≠ 0
  Φ3 : ∀ (x : Localization.Away ω →ₐ[K] K) (y : Localization.Away ωΦ →ₐ[K] K),
    y.comp (awayι ωΦ) = x.comp (phiS μ) → y.comp gΦ = x.comp (awayι ω)
  Φ4 : ∀ (y : Localization.Away ωΦ →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    x.comp (awayι ω) = y.comp gΦ → x.comp (phiS μ) = y.comp (awayι ωΦ)
  ωΨ : R ⊗[K] R
  gΨ : R ⊗[K] R →ₐ[K] Localization.Away ωΨ
  Ψ1 : ∀ x : Localization.Away ω →ₐ[K] K, x (psiS μ ωΨ) ≠ 0
  Ψ3 : ∀ (x : Localization.Away ω →ₐ[K] K) (y : Localization.Away ωΨ →ₐ[K] K),
    y.comp (awayι ωΨ) = x.comp (psiS μ) → y.comp gΨ = x.comp (awayι ω)
  Ψ4 : ∀ (y : Localization.Away ωΨ →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    x.comp (awayι ω) = y.comp gΨ → x.comp (psiS μ) = y.comp (awayι ωΨ)
  fibL : ∀ a : R →ₐ[K] K, ∃ x : Localization.Away ω →ₐ[K] K, pL x = a
  fibR : ∀ b : R →ₐ[K] K, ∃ x : Localization.Away ω →ₐ[K] K, pR x = b
  assoc : ∀ x₁ x₂ x₃ x₄ : Localization.Away ω →ₐ[K] K, pR x₁ = pL x₂ → pL x₃ = x₁.comp μ →
    pR x₃ = pR x₂ → pL x₄ = pL x₁ → pR x₄ = x₂.comp μ → x₃.comp μ = x₄.comp μ

/-- `D(ω) ⊆ Spec (R ⊗ R) ≅ X ×_K X`. -/
noncomputable def jAway (ω : R ⊗[K] R) : Spec (.of (Localization.Away ω)) ⟶ pullback (sR K R) (sR K R) :=
  Spec.map (CommRingCat.ofHom (awayι (K := K) ω : R ⊗[K] R →+* Localization.Away ω)) ≫
    (pullbackSpecIso K R R).inv

instance isOpenImmersion_jAway (ω : R ⊗[K] R) : IsOpenImmersion (jAway ω) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (awayι (K := K) ω : R ⊗[K] R →+* Localization.Away ω))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (R ⊗[K] R)) ω
  unfold jAway; infer_instance

@[reassoc] theorem eInv_fst : (pullbackSpecIso K R R).inv ≫ pullback.fst (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom ((includeLeft : R →ₐ[K] R ⊗[K] R) : R →+* R ⊗[K] R)) :=
  pullbackSpecIso_inv_fst K R R

@[reassoc] theorem eInv_snd : (pullbackSpecIso K R R).inv ≫ pullback.snd (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom ((includeRight : R →ₐ[K] R ⊗[K] R) : R →+* R ⊗[K] R)) :=
  pullbackSpecIso_inv_snd K R R

@[reassoc] theorem jAway_fst (ω : R ⊗[K] R) : jAway ω ≫ pullback.fst (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom (((awayι ω).comp includeLeft : R →ₐ[K] Localization.Away ω) : R →+* _)) := by
  rw [jAway, Category.assoc, eInv_fst, SpecMap_comp]

@[reassoc] theorem jAway_snd (ω : R ⊗[K] R) : jAway ω ≫ pullback.snd (sR K R) (sR K R) =
    Spec.map (CommRingCat.ofHom (((awayι ω).comp includeRight : R →ₐ[K] Localization.Away ω) : R →+* _)) := by
  rw [jAway, Category.assoc, eInv_snd, SpecMap_comp]

theorem fst_jAway (ω : R ⊗[K] R) (x : Localization.Away ω →ₐ[K] K) :
    pullback.fst (sR K R) (sR K R) (jAway ω (kpt x)) = kpt (pL x) := by
  rw [← Scheme.Hom.comp_apply, jAway_fst, SpecMap_kpt]

theorem snd_jAway (ω : R ⊗[K] R) (x : Localization.Away ω →ₐ[K] K) :
    pullback.snd (sR K R) (sR K R) (jAway ω (kpt x)) = kpt (pR x) := by
  rw [← Scheme.Hom.comp_apply, jAway_snd, SpecMap_kpt]

theorem isClosed_jAway (ω : R ⊗[K] R) (x : Localization.Away ω →ₐ[K] K) :
    IsClosed ({jAway ω (kpt x)} : Set (pullback (sR K R) (sR K R) : Scheme.{u})) := by
  have h := (Scheme.homeoOfIso (pullbackSpecIso K R R).symm).isClosedMap _ (isClosed_kpt (x.comp (awayι ω)))
  rw [Set.image_singleton] at h
  rw [jAway, Scheme.Hom.comp_apply, SpecMap_kpt]
  exact h

variable [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R]

omit [IsDomain R] in
theorem exists_pt_jAway (ω : R ⊗[K] R) (z : (jAway ω).opensRange)
    (hz : IsClosed ({z.1} : Set (pullback (sR K R) (sR K R) : Scheme.{u}))) :
    ∃ x : Localization.Away ω →ₐ[K] K, z.1 = jAway ω (kpt x) ∧ (jAway ω).isoOpensRange.inv z = kpt x := by
  obtain ⟨p, hp⟩ := Scheme.Hom.mem_opensRange.1 z.2
  have hinj := (jAway ω).isOpenEmbedding.injective
  have hpc : IsClosed ({p} : Set (Spec (.of (Localization.Away ω)) : Scheme.{u})) := by
    have e : (jAway ω) ⁻¹' {z.1} = {p} := by
      ext q; simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hp, hinj.eq_iff]
    rw [← e]; exact hz.preimage (jAway ω).continuous
  obtain ⟨x, rfl⟩ := exists_kpt (K := K) (A := Localization.Away ω) p hpc
  refine ⟨x, hp.symm, hinj ?_⟩
  exact (congrArg (fun f => f z) (Scheme.Hom.isoOpensRange_inv_comp (jAway ω))).trans hp.symm

omit [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R] in
theorem mS_apply (ω : R ⊗[K] R) (μ : R →ₐ[K] Localization.Away ω) (z : (jAway ω).opensRange)
    (x : Localization.Away ω →ₐ[K] K) (h : (jAway ω).isoOpensRange.inv z = kpt x) :
    ((jAway ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (μ : R →+* _))) z = kpt (x.comp μ) := by
  have e : ((jAway ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (μ : R →+* _))) z =
      Spec.map (CommRingCat.ofHom (μ : R →+* _)) ((jAway ω).isoOpensRange.inv z) := rfl
  rw [e, h, SpecMap_kpt]

namespace AffChunk

variable (C : AffChunk K R)

/-- The strict group chunk on `Spec R` defined by algebraic chunk data. -/
noncomputable def toStrict : StrictChunk (k := K) (sR K R) where
  Ω := (jAway C.ω).opensRange
  m := (jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (C.μ : R →+* _))
  Φ := (jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (phiS C.μ : R ⊗[K] R →+* _)) ≫
    (pullbackSpecIso K R R).inv
  Φ_fst := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp (jAway C.ω)]
    simp only [Category.assoc, eInv_fst, jAway_fst, SpecMap_comp, phiS_incL]
  Φ_snd := by simp only [Category.assoc, eInv_snd, SpecMap_comp, phiS_incR]
  isOpenImmersion_Φ := by
    have := isOpenImmersion_of_ptInv (phiS C.μ) C.gΦ C.Φ1 C.Φ3 C.Φ4
    infer_instance
  Ψ := (jAway C.ω).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (psiS C.μ : R ⊗[K] R →+* _)) ≫
    (pullbackSpecIso K R R).inv
  Ψ_fst := by simp only [Category.assoc, eInv_fst, SpecMap_comp, psiS_incL]
  Ψ_snd := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp (jAway C.ω)]
    simp only [Category.assoc, eInv_snd, jAway_snd, SpecMap_comp, psiS_incR]
  isOpenImmersion_Ψ := by
    have := isOpenImmersion_of_ptInv (psiS C.μ) C.gΨ C.Ψ1 C.Ψ3 C.Ψ4
    infer_instance
  fib_left a ha := by
    obtain ⟨y, rfl⟩ := exists_kpt (K := K) (A := R) a ha
    obtain ⟨x, hx⟩ := C.fibL y
    exact ⟨jAway C.ω (kpt x), Scheme.Hom.mem_opensRange.2 ⟨kpt x, rfl⟩, isClosed_jAway C.ω x,
      by rw [fst_jAway, hx]⟩
  fib_right b hb := by
    obtain ⟨y, rfl⟩ := exists_kpt (K := K) (A := R) b hb
    obtain ⟨x, hx⟩ := C.fibR y
    exact ⟨jAway C.ω (kpt x), Scheme.Hom.mem_opensRange.2 ⟨kpt x, rfl⟩, isClosed_jAway C.ω x,
      by rw [snd_jAway, hx]⟩
  assoc z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ e₁ e₂ e₃ e₄ e₅ := by
    obtain ⟨x₁, hz₁, hi₁⟩ := exists_pt_jAway C.ω z₁ h₁
    obtain ⟨x₂, hz₂, hi₂⟩ := exists_pt_jAway C.ω z₂ h₂
    obtain ⟨x₃, hz₃, hi₃⟩ := exists_pt_jAway C.ω z₃ h₃
    obtain ⟨x₄, hz₄, hi₄⟩ := exists_pt_jAway C.ω z₄ h₄
    rw [hz₁, hz₂, snd_jAway, fst_jAway] at e₁
    rw [hz₃, fst_jAway, mS_apply C.ω C.μ z₁ x₁ hi₁] at e₂
    rw [hz₃, hz₂, snd_jAway, snd_jAway] at e₃
    rw [hz₄, hz₁, fst_jAway, fst_jAway] at e₄
    rw [hz₄, snd_jAway, mS_apply C.ω C.μ z₂ x₂ hi₂] at e₅
    rw [mS_apply C.ω C.μ z₃ x₃ hi₃, mS_apply C.ω C.μ z₄ x₄ hi₄, C.assoc x₁ x₂ x₃ x₄ (kpt_injective e₁)
      (kpt_injective e₂) (kpt_injective e₃) (kpt_injective e₄) (kpt_injective e₅)]

end AffChunk

end Sch

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_ShrinkA =====
section

/-!
# S4-JacLaw, file O10d-1: tools for shrinking a chunk

* `pair a b`: the `K`-point `(a, b)` of `S ⊗ S`; slices `slL a` (`t ↦ t(a, ·)`), `slR b`.
* Nullstellensatz on a domain: three nonempty basic opens meet (`exists_pt_ne3`).
* `numA e`: a numerator of `e ∈ T[1/ω]` vanishing off `D(ω)`.
* `liftPt`: extend `A → B` to `A[1/ω]` when `ω` vanishes at no point of `B`.
* Base change to `R = S[1/u]`: `jj`, `extW`, `extK`, `extN` and their point lemmas.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Pair

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S]

theorem tensor_ext {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C]
    [Algebra K C] {f g : A ⊗[K] B →ₐ[K] C} (h1 : f.comp includeLeft = g.comp includeLeft)
    (h2 : f.comp includeRight = g.comp includeRight) : f = g :=
  Algebra.TensorProduct.ext h1 (AlgHom.ext fun s => DFunLike.congr_fun h2 s)

/-- The `K`-point `(a, b)` of `S ⊗ S`. -/
noncomputable def pair (a b : S →ₐ[K] K) : S ⊗[K] S →ₐ[K] K :=
  Algebra.TensorProduct.lift a b fun _ _ => Commute.all _ _

theorem pair_incL (a b : S →ₐ[K] K) : (pair a b).comp includeLeft = a :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem pair_incR (a b : S →ₐ[K] K) : (pair a b).comp includeRight = b :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

theorem eq_pair (z : S ⊗[K] S →ₐ[K] K) : z = pair (z.comp includeLeft) (z.comp includeRight) :=
  tensor_ext (pair_incL _ _).symm (pair_incR _ _).symm

theorem base_pair {ω : S ⊗[K] S} (x : Localization.Away ω →ₐ[K] K) : x.comp (awayι ω) = pair (pL x) (pR x) :=
  eq_pair _

theorem pts_of_base {ω : S ⊗[K] S} {x : Localization.Away ω →ₐ[K] K} {a b : S →ₐ[K] K}
    (h : x.comp (awayι ω) = pair a b) : pL x = a ∧ pR x = b :=
  ⟨(congrArg (fun z => z.comp includeLeft) h).trans (pair_incL a b),
    (congrArg (fun z => z.comp includeRight) h).trans (pair_incR a b)⟩

theorem exists_over_pair {ω : S ⊗[K] S} {a b : S →ₐ[K] K} (h : pair a b ω ≠ 0) :
    ∃ x : Localization.Away ω →ₐ[K] K, x.comp (awayι ω) = pair a b ∧ pL x = a ∧ pR x = b := by
  obtain ⟨x, hx⟩ := exists_baseAway ω (pair a b) h
  have hx' : x.comp (awayι ω) = pair a b := hx
  exact ⟨x, hx', pts_of_base hx'⟩

theorem phiS_pt {ω : S ⊗[K] S} (μ : S →ₐ[K] Localization.Away ω) (x : Localization.Away ω →ₐ[K] K) :
    x.comp (phiS μ) = pair (pL x) (x.comp μ) := by
  refine tensor_ext ?_ ?_
  · show x.comp ((phiS μ).comp includeLeft) = (pair (pL x) (x.comp μ)).comp includeLeft
    rw [phiS_incL, pair_incL]
  · show x.comp ((phiS μ).comp includeRight) = (pair (pL x) (x.comp μ)).comp includeRight
    rw [phiS_incR, pair_incR]

theorem psiS_pt {ω : S ⊗[K] S} (μ : S →ₐ[K] Localization.Away ω) (x : Localization.Away ω →ₐ[K] K) :
    x.comp (psiS μ) = pair (x.comp μ) (pR x) := by
  refine tensor_ext ?_ ?_
  · show x.comp ((psiS μ).comp includeLeft) = (pair (x.comp μ) (pR x)).comp includeLeft
    rw [psiS_incL, pair_incL]
  · show x.comp ((psiS μ).comp includeRight) = (pair (x.comp μ) (pR x)).comp includeRight
    rw [psiS_incR, pair_incR]

/-- `t ↦ t(a, ·)`. -/
noncomputable def slL (a : S →ₐ[K] K) : S ⊗[K] S →ₐ[K] S :=
  Algebra.TensorProduct.lift ((Algebra.ofId K S).comp a) (AlgHom.id K S) fun _ _ => Commute.all _ _

/-- `t ↦ t(·, b)`. -/
noncomputable def slR (b : S →ₐ[K] K) : S ⊗[K] S →ₐ[K] S :=
  Algebra.TensorProduct.lift (AlgHom.id K S) ((Algebra.ofId K S).comp b) fun _ _ => Commute.all _ _

theorem slL_pt (a b : S →ₐ[K] K) : b.comp (slL a) = pair a b :=
  Algebra.TensorProduct.ext' fun s t => by simp [slL, pair]

theorem slR_pt (a b : S →ₐ[K] K) : a.comp (slR b) = pair a b :=
  Algebra.TensorProduct.ext' fun s t => by simp [slR, pair]

theorem ne_zero_of_pt {f : S} (h : ∃ x : S →ₐ[K] K, x f ≠ 0) : f ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := h
  exact hx (map_zero x)

variable [IsAlgClosed K] [IsDomain S] [Algebra.FiniteType K S]

theorem exists_pt_ne {f : S} (hf : f ≠ 0) : ∃ x : S →ₐ[K] K, x f ≠ 0 := by
  by_contra h
  refine hf (evPts_injective (k := K) (funext fun x => ?_))
  rw [evPts_apply, map_zero]
  exact not_not.1 fun hx => h ⟨x, hx⟩

theorem exists_pt_ne2 {f g : S} (hf : ∃ x : S →ₐ[K] K, x f ≠ 0) (hg : ∃ x : S →ₐ[K] K, x g ≠ 0) :
    ∃ x : S →ₐ[K] K, x f ≠ 0 ∧ x g ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_pt_ne (K := K) (mul_ne_zero (ne_zero_of_pt hf) (ne_zero_of_pt hg))
  rw [map_mul] at hx
  exact ⟨x, left_ne_zero_of_mul hx, right_ne_zero_of_mul hx⟩

theorem exists_pt_ne3 {f g h : S} (hf : ∃ x : S →ₐ[K] K, x f ≠ 0) (hg : ∃ x : S →ₐ[K] K, x g ≠ 0)
    (hh : ∃ x : S →ₐ[K] K, x h ≠ 0) : ∃ x : S →ₐ[K] K, x f ≠ 0 ∧ x g ≠ 0 ∧ x h ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_pt_ne (K := K)
    (mul_ne_zero (mul_ne_zero (ne_zero_of_pt hf) (ne_zero_of_pt hg)) (ne_zero_of_pt hh))
  rw [map_mul, map_mul] at hx
  exact ⟨x, left_ne_zero_of_mul (left_ne_zero_of_mul hx), right_ne_zero_of_mul (left_ne_zero_of_mul hx),
    right_ne_zero_of_mul hx⟩

end Pair

section Num

variable {K : Type u} [Field K] {T : Type u} [CommRing T] [Algebra K T]

/-- A numerator of `e ∈ T[1/ω]`, times `ω` so that it also vanishes off `D(ω)`. -/
noncomputable def numA {ω : T} (e : Localization.Away ω) : T :=
  ω * (IsLocalization.surj (Submonoid.powers ω) e).choose.1

theorem numA_base {ω : T} (e : Localization.Away ω) (z : T →ₐ[K] K) (h : z (numA e) ≠ 0) : z ω ≠ 0 := by
  rw [numA, map_mul] at h
  exact left_ne_zero_of_mul h

theorem numA_pt {ω : T} (e : Localization.Away ω) (x : Localization.Away ω →ₐ[K] K) :
    (x.comp (awayι ω)) (numA e) ≠ 0 ↔ x e ≠ 0 := by
  have h := (IsLocalization.surj (Submonoid.powers ω) e).choose_spec
  have h1 : x (algebraMap T _ ω) ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away ω) ω).map x).ne_zero
  have h2 : x (algebraMap T _ (IsLocalization.surj (Submonoid.powers ω) e).choose.2) ≠ 0 :=
    ((IsLocalization.map_units (M := Submonoid.powers ω) (S := Localization.Away ω)
      (IsLocalization.surj (Submonoid.powers ω) e).choose.2).map x).ne_zero
  rw [AlgHom.comp_apply, awayι_apply, numA, map_mul (algebraMap T _), ← h, map_mul, map_mul]
  simp only [ne_eq, mul_eq_zero, h1, h2, false_or, or_false]

end Num

section Lift

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Extend `f : A → B` to `A[1/ω]` when `f ω` vanishes at no `K`-point of `B`. -/
noncomputable def liftPt {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] (f : A →ₐ[K] B) (ω : A) (h : ∀ y : B →ₐ[K] K, y (f ω) ≠ 0) :
    Localization.Away ω →ₐ[K] B :=
  IsLocalization.Away.liftAlgHom (f := f) ω (isUnit_of_forall_ne_zero (k := K) (f ω) h)

theorem liftPt_comp {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] (f : A →ₐ[K] B) (ω : A) (h : ∀ y : B →ₐ[K] K, y (f ω) ≠ 0) :
    (liftPt f ω h).comp (awayι ω) = f :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, awayι_apply]
    unfold liftPt
    rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
    rfl

end Lift

/-- `S ⊗ S → S[1/u] ⊗ S[1/u]`. -/
noncomputable def jj (K : Type u) [Field K] {S : Type u} [CommRing S] [Algebra K S] (u : S) :
    S ⊗[K] S →ₐ[K] Localization.Away u ⊗[K] Localization.Away u :=
  Algebra.TensorProduct.map (awayι u) (awayι u)

section Ext

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S] (u : S)

theorem jj_incL : (jj K u).comp includeLeft = includeLeft.comp (awayι (K := K) u) :=
  Algebra.TensorProduct.map_comp_includeLeft _ _

theorem jj_incR : (jj K u).comp includeRight = includeRight.comp (awayι (K := K) u) :=
  Algebra.TensorProduct.map_comp_includeRight _ _

theorem jj_ext {C : Type u} [CommRing C] [Algebra K C]
    {f g : Localization.Away u ⊗[K] Localization.Away u →ₐ[K] C}
    (h : f.comp (jj K u) = g.comp (jj K u)) : f = g := by
  refine tensor_ext (away_algHom_ext ?_) (away_algHom_ext ?_)
  · have := congrArg (fun F => F.comp includeLeft) h
    simp only [AlgHom.comp_assoc, jj_incL] at this
    exact this
  · have := congrArg (fun F => F.comp includeRight) h
    simp only [AlgHom.comp_assoc, jj_incR] at this
    exact this

theorem jj_pt {w : Localization.Away u ⊗[K] Localization.Away u} (y : Localization.Away w →ₐ[K] K) :
    (y.comp (awayι w)).comp (jj K u) = pair ((pL y).comp (awayι u)) ((pR y).comp (awayι u)) := by
  refine tensor_ext ?_ ?_
  · rw [pair_incL]
    show (y.comp (awayι w)).comp ((jj K u).comp includeLeft) =
      (y.comp (awayι w)).comp (includeLeft.comp (awayι u))
    rw [jj_incL]
  · rw [pair_incR]
    show (y.comp (awayι w)).comp ((jj K u).comp includeRight) =
      (y.comp (awayι w)).comp (includeRight.comp (awayι u))
    rw [jj_incR]

variable [IsAlgClosed K] [Algebra.FiniteType K S] {ω : S ⊗[K] S} (e : S ⊗[K] S)
  (ν : S →ₐ[K] Localization.Away ω)

/-- `w ∈ S[1/u] ⊗ S[1/u]`, the image of `e · num(ν u)`. -/
noncomputable def extW : Localization.Away u ⊗[K] Localization.Away u := jj K u (e * numA (ν u))

theorem extW_pt (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    pair ((pL y).comp (awayι u)) ((pR y).comp (awayι u)) (e * numA (ν u)) ≠ 0 := by
  rw [← jj_pt]
  exact baseAway_ne _ y

/-- `T[1/ω] → (S[1/u] ⊗ S[1/u])[1/w]`. -/
noncomputable def extK : Localization.Away ω →ₐ[K] Localization.Away (extW u e ν) :=
  liftPt ((awayι (extW u e ν)).comp (jj K u)) ω fun y => by
    have h := extW_pt u e ν y
    rw [map_mul] at h
    have h' := numA_base (ν u) _ (right_ne_zero_of_mul h)
    rw [← jj_pt] at h'
    exact h'

theorem extK_comp : (extK u e ν).comp (awayι ω) = (awayι (extW u e ν)).comp (jj K u) := liftPt_comp _ _ _

theorem extK_pt (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (awayι ω) = pair ((pL y).comp (awayι u)) ((pR y).comp (awayι u)) := by
  rw [AlgHom.comp_assoc, extK_comp, ← AlgHom.comp_assoc, jj_pt]

theorem extK_base (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (awayι ω) = (y.comp (awayι (extW u e ν))).comp (jj K u) := by
  rw [AlgHom.comp_assoc, extK_comp, ← AlgHom.comp_assoc]

theorem extK_pL (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    pL (y.comp (extK u e ν)) = (pL y).comp (awayι u) :=
  (congrArg (fun z => z.comp includeLeft) (extK_pt u e ν y)).trans (pair_incL _ _)

theorem extK_pR (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    pR (y.comp (extK u e ν)) = (pR y).comp (awayι u) :=
  (congrArg (fun z => z.comp includeRight) (extK_pt u e ν y)).trans (pair_incR _ _)

theorem extK_uL (y : Localization.Away (extW u e ν) →ₐ[K] K) : (pL (y.comp (extK u e ν))) u ≠ 0 := by
  rw [extK_pL]; exact baseAway_ne u (pL y)

theorem extK_uR (y : Localization.Away (extW u e ν) →ₐ[K] K) : (pR (y.comp (extK u e ν))) u ≠ 0 := by
  rw [extK_pR]; exact baseAway_ne u (pR y)

theorem extK_e (y : Localization.Away (extW u e ν) →ₐ[K] K) : ((y.comp (extK u e ν)).comp (awayι ω)) e ≠ 0 := by
  have h := extW_pt u e ν y
  rw [map_mul, ← extK_pt u e ν y] at h
  exact left_ne_zero_of_mul h

/-- `ν` extended to `S[1/u] → (S[1/u] ⊗ S[1/u])[1/w]`. -/
noncomputable def extN : Localization.Away u →ₐ[K] Localization.Away (extW u e ν) :=
  liftPt ((extK u e ν).comp ν) u fun y => by
    have h := extW_pt u e ν y
    rw [map_mul, ← extK_pt u e ν y] at h
    exact (numA_pt (ν u) (y.comp (extK u e ν))).1 (right_ne_zero_of_mul h)

theorem extN_comp : (extN u e ν).comp (awayι u) = (extK u e ν).comp ν := liftPt_comp _ _ _

theorem extK_nu (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp ν = (y.comp (extN u e ν)).comp (awayι u) := by
  rw [AlgHom.comp_assoc, ← extN_comp, ← AlgHom.comp_assoc]

theorem phiS_ext : (phiS (extN u e ν)).comp (jj K u) = (extK u e ν).comp (phiS ν) := by
  refine tensor_ext ?_ ?_
  · show (phiS (extN u e ν)).comp ((jj K u).comp includeLeft) = (extK u e ν).comp ((phiS ν).comp includeLeft)
    rw [jj_incL, phiS_incL]
    show ((phiS (extN u e ν)).comp includeLeft).comp (awayι u) = ((extK u e ν).comp (awayι ω)).comp includeLeft
    rw [phiS_incL, extK_comp]
    show (awayι (extW u e ν)).comp (includeLeft.comp (awayι u)) =
      (awayι (extW u e ν)).comp ((jj K u).comp includeLeft)
    rw [jj_incL]
  · show (phiS (extN u e ν)).comp ((jj K u).comp includeRight) = (extK u e ν).comp ((phiS ν).comp includeRight)
    rw [jj_incR, phiS_incR]
    show ((phiS (extN u e ν)).comp includeRight).comp (awayι u) = (extK u e ν).comp ν
    rw [phiS_incR, extN_comp]

theorem psiS_ext : (psiS (extN u e ν)).comp (jj K u) = (extK u e ν).comp (psiS ν) := by
  refine tensor_ext ?_ ?_
  · show (psiS (extN u e ν)).comp ((jj K u).comp includeLeft) = (extK u e ν).comp ((psiS ν).comp includeLeft)
    rw [jj_incL, psiS_incL]
    show ((psiS (extN u e ν)).comp includeLeft).comp (awayι u) = (extK u e ν).comp ν
    rw [psiS_incL, extN_comp]
  · show (psiS (extN u e ν)).comp ((jj K u).comp includeRight) = (extK u e ν).comp ((psiS ν).comp includeRight)
    rw [jj_incR, psiS_incR]
    show ((psiS (extN u e ν)).comp includeRight).comp (awayι u) = ((extK u e ν).comp (awayι ω)).comp includeRight
    rw [psiS_incR, extK_comp]
    show (awayι (extW u e ν)).comp (includeRight.comp (awayι u)) =
      (awayι (extW u e ν)).comp ((jj K u).comp includeRight)
    rw [jj_incR]

theorem extK_phi (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (phiS ν) = (y.comp (phiS (extN u e ν))).comp (jj K u) := by
  rw [AlgHom.comp_assoc, ← phiS_ext, ← AlgHom.comp_assoc]

theorem extK_psi (y : Localization.Away (extW u e ν) →ₐ[K] K) :
    (y.comp (extK u e ν)).comp (psiS ν) = (y.comp (psiS (extN u e ν))).comp (jj K u) := by
  rw [AlgHom.comp_assoc, ← psiS_ext, ← AlgHom.comp_assoc]

theorem exists_ext_pt (a b : S →ₐ[K] K) (ha : a u ≠ 0) (hb : b u ≠ 0) (h : pair a b (e * numA (ν u)) ≠ 0) :
    ∃ y : Localization.Away (extW u e ν) →ₐ[K] K, (pL y).comp (awayι u) = a ∧ (pR y).comp (awayι u) = b := by
  obtain ⟨a', ha'⟩ := exists_baseAway u a ha
  obtain ⟨b', hb'⟩ := exists_baseAway u b hb
  have hp : (pair a' b').comp (jj K u) = pair a b := by
    refine tensor_ext ?_ ?_
    · show (pair a' b').comp ((jj K u).comp includeLeft) = (pair a b).comp includeLeft
      rw [jj_incL, pair_incL]
      show ((pair a' b').comp includeLeft).comp (awayι u) = a
      rw [pair_incL]; exact ha'
    · show (pair a' b').comp ((jj K u).comp includeRight) = (pair a b).comp includeRight
      rw [jj_incR, pair_incR]
      show ((pair a' b').comp includeRight).comp (awayι u) = b
      rw [pair_incR]; exact hb'
  obtain ⟨y, hy⟩ := exists_baseAway (extW u e ν) (pair a' b') (by
    show ((pair a' b').comp (jj K u)) (e * numA (ν u)) ≠ 0
    rw [hp]; exact h)
  have hy' : y.comp (awayι (extW u e ν)) = pair a' b' := hy
  refine ⟨y, ?_, ?_⟩
  · show ((y.comp (awayι (extW u e ν))).comp includeLeft).comp (awayι u) = a
    rw [hy', pair_incL]; exact ha'
  · show ((y.comp (awayι (extW u e ν))).comp includeRight).comp (awayι u) = b
    rw [hy', pair_incR]; exact hb'

end Ext

end RamanujanPetersson.JacLaw

end


