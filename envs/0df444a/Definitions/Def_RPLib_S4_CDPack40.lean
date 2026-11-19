-- Prove2me | Definitions.Def_RPLib_S4_CDPack40
-- name    : RPLib_S4_CDPack40
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:56:15.908787+00:00
-- url     : https://prove2.me/theorems/7e593fbb-1307-4e15-bc4c-f87eb2ae2a9e
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 40 of 71
-- statement:
--   Part 40 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_Dict`: The Jacobian (unit S4-JacComplete), part `Dict` (dictionary D3 along `σ : F ≃ₐ[K] F'`)
--   * `Def_RP_JacComplete_AJConv`: The Jacobian (unit S4-JacComplete), part `AJConv`: moving points from the chart synonym back to `F`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack38
import Definitions.Def_RPLib_S4_CDPack31
import Definitions.Def_RPLib_S4_CDPack39
import Definitions.Def_RPLib_S4_CDPack28c

/-!
# Curve-duality library package, part 40 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_Dict`: The Jacobian (unit S4-JacComplete), part `Dict` (dictionary D3 along `σ : F ≃ₐ[K] F'`)
* `Def_RP_JacComplete_AJConv`: The Jacobian (unit S4-JacComplete), part `AJConv`: moving points from the chart synonym back to `F`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_Dict =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Dict` (dictionary D3 along `σ : F ≃ₐ[K] F'`)

For two function-field structures related by `σ : F ≃ₐ[K] F'` (e.g. `synEquiv K F c`):
* `divMap σ : Divisor K F ≃+ Divisor K F'` (along `placeEquiv σ`), `divMap_div`, `divMap_nonneg`,
  `deg_divMap` (`K` algebraically closed);
* `mem_LFK_divMap`, `LFK_divMap`, **`ellFK_divMap`**, **`genusFK_eq`**;
* `picMap σ : PicK K F ≃+ PicK K F'` with `picMap_clsK`, `degPicK_picMap`, `mem_Pic0K_picMap`, `pic0Map`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Divisor)
open RamanujanPetersson.RR

section Dict

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]
variable {F' : Type*} [Field F'] [Algebra K F'] [Algebra K[X] F'] [Algebra (RatFunc K) F']
  [IsScalarTower K[X] (RatFunc K) F'] [IsScalarTower K K[X] F'] [FunctionField K F']
  [Algebra.IsSeparable (RatFunc K) F']
variable (σ : F ≃ₐ[K] F')

/-- Transport of divisors along `σ`. -/
noncomputable def divMap : Divisor K F ≃+ Divisor K F' := Finsupp.domCongr (placeEquiv σ)

theorem divMap_apply (D : Divisor K F) (P' : Place K F') :
    divMap σ D P' = D ((placeEquiv σ).symm P') := rfl

theorem divMap_single (P : Place K F) (n : ℤ) :
    divMap σ (Finsupp.single P n) = Finsupp.single (placeEquiv σ P) n :=
  Finsupp.equivMapDomain_single _ _ _

theorem divMap_div (f : F) : divMap σ (PlacesK.div f) = PlacesK.div (σ f) := by
  ext P'
  rw [divMap_apply, PlacesK.div_apply, PlacesK.div_apply, ord_placeEquiv_symm]

theorem divMap_nonneg (E : Divisor K F) : 0 ≤ divMap σ E ↔ 0 ≤ E := by
  rw [Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h P
    simpa only [divMap_apply, Equiv.symm_apply_apply, Finsupp.coe_zero, Pi.zero_apply] using h (placeEquiv σ P)
  · intro h P'
    simpa only [divMap_apply, Finsupp.coe_zero, Pi.zero_apply] using h ((placeEquiv σ).symm P')

theorem mem_LFK_divMap (D : Divisor K F) (f : F) :
    σ f ∈ LFK K F' (divMap σ D) ↔ f ∈ LFK K F D := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [map_zero, Submodule.zero_mem]
  · rw [mem_LFK hf, mem_LFK ((map_ne_zero σ).2 hf), ← divMap_div, ← map_add, divMap_nonneg]

theorem LFK_divMap (D : Divisor K F) :
    LFK K F' (divMap σ D) = (LFK K F D).map (σ.toLinearEquiv : F →ₗ[K] F') := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · intro hy
    refine ⟨σ.symm y, ?_, by simp⟩
    rw [← mem_LFK_divMap σ, AlgEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨f, hf, rfl⟩
    exact (mem_LFK_divMap σ D f).2 hf

/-- `ℓ` is invariant under the transport. -/
theorem ellFK_divMap (D : Divisor K F) : ellFK K F' (divMap σ D) = ellFK K F D := by
  show Module.finrank K (LFK K F' (divMap σ D)) = Module.finrank K (LFK K F D)
  rw [LFK_divMap]
  exact LinearEquiv.finrank_map_eq σ.toLinearEquiv _

theorem deg_divMap [IsAlgClosed K] (D : Divisor K F) :
    Places.Divisor.deg (divMap σ D) = Places.Divisor.deg D := by
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; simp [Places.Divisor.deg]
  | add D E hD hE => rw [map_add, PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_add, hD, hE]
  | single P n => rw [divMap_single, deg_single', deg_single']

include σ in
/-- **The genus is invariant under the transport.** -/
theorem genusFK_eq [IsAlgClosed K] : genusFK K F' = genusFK K F := by
  have hne : poleBK K F ≠ 0 := by
    intro h
    have h1 := degD_poleBK_pos (K := K) (F := F)
    rw [h] at h1
    simp [Places.Divisor.deg] at h1
  obtain ⟨P, -⟩ := Finsupp.ne_iff.1 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 * ((genusFK K F : ℤ) + genusFK K F') + 1 := ⟨_, rfl⟩
  have hdeg : Places.Divisor.deg (Finsupp.single P n : Divisor K F) = n := deg_single' P n
  have hdeg' : Places.Divisor.deg (divMap σ (Finsupp.single P n)) = n := by rw [deg_divMap, hdeg]
  have h0 : ellFK K F' 0 = ellFK K F 0 := by simpa using ellFK_divMap σ 0
  have e1 := ellFK_eq_of_large_deg (K := K) (F := F) (D := Finsupp.single P n) (by rw [hdeg]; omega)
  have e2 := ellFK_eq_of_large_deg (K := K) (F := F') (D := divMap σ (Finsupp.single P n))
    (by rw [hdeg']; omega)
  rw [ellFK_divMap, hdeg', h0] at e2
  rw [hdeg] at e1
  omega

theorem map_PrincK :
    (PrincK K F).map (divMap σ : Divisor K F →+ Divisor K F') = PrincK K F' := by
  ext D'
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨D, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨σ f, (map_ne_zero σ).2 hf, (divMap_div σ f).symm⟩
  · rintro ⟨f', hf', rfl⟩
    refine ⟨PlacesK.div (σ.symm f'), div_mem_PrincK K F ((map_ne_zero σ.symm).2 hf'), ?_⟩
    show divMap σ (PlacesK.div (σ.symm f')) = _
    rw [divMap_div, AlgEquiv.apply_symm_apply]

/-- Transport of divisor classes. -/
noncomputable def picMap : PicK K F ≃+ PicK K F' :=
  QuotientAddGroup.congr (PrincK K F) (PrincK K F') (divMap σ) (map_PrincK σ)

theorem picMap_clsK (D : Divisor K F) : picMap σ (clsK K F D) = clsK K F' (divMap σ D) := rfl

theorem degPicK_picMap [IsAlgClosed K] (x : PicK K F) :
    degPicK K F' (picMap σ x) = degPicK K F x := by
  induction x using QuotientAddGroup.induction_on with
  | H D =>
    show degPicK K F' (picMap σ (clsK K F D)) = degPicK K F (clsK K F D)
    rw [picMap_clsK, degPicK_clsK, degPicK_clsK]
    exact deg_divMap σ D

theorem mem_Pic0K_picMap [IsAlgClosed K] (x : PicK K F) :
    picMap σ x ∈ Pic0K K F' ↔ x ∈ Pic0K K F := by
  rw [mem_Pic0K, mem_Pic0K, degPicK_picMap]

/-- Transport of degree-`0` classes. -/
noncomputable def pic0Map [IsAlgClosed K] : Pic0K K F ≃+ Pic0K K F' where
  toFun x := ⟨picMap σ x.1, (mem_Pic0K_picMap σ x.1).2 x.2⟩
  invFun y := ⟨(picMap σ).symm y, (mem_Pic0K_picMap σ _).1 (by rw [AddEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((picMap σ).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((picMap σ).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add (picMap σ) x.1 y.1)

theorem pic0Map_apply [IsAlgClosed K] (x : Pic0K K F) : (pic0Map σ x : PicK K F') = picMap σ x.1 := rfl

end Dict

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_AJConv =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJConv`: moving points from the chart synonym back to `F`

`F' = SynF K F c0` has coordinate `x' = 1/(x - c0)`. Every `w ∈ Rfin K F` has `x'^n w ∈ Rfin K F'`
(`exists_uc_pow_mul_chartRing`), so a `K`-point `e'` of `Rfin K F'` with `e'(x') ≠ 0` gives the `K`-point
`tpH e' : w ↦ e'(x'^n w)/e'(x')^n` of `Rfin K F` (`tp_eq`: independent of `n`), with the same place
(`synPlace_tpH`). `convSym`: a map `Sym^n(Rfin F') → R` with `N(x')` a unit becomes `Sym^n(Rfin F) → R`
(`liftPts`), with `divMap_Zdiv_convSym` for the divisors of its points.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym

universe u

section AJConv

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- `K[x] ⊆ F` as a `K`-subalgebra. -/
noncomputable abbrev polyX : Subalgebra K F := Algebra.adjoin K {algebraMap K[X] F X}

/-- `K[X] → K[x]`. -/
noncomputable def xPoly : K[X] →ₐ[K] polyX K F :=
  aeval (⟨algebraMap K[X] F X, Algebra.self_mem_adjoin_singleton K _⟩ : polyX K F)

theorem xPoly_coe (p : K[X]) : ((xPoly p : polyX K F) : F) = algebraMap K[X] F p := by
  rw [algebraMap_eq_aeval]
  exact (Polynomial.aeval_algHom_apply (polyX K F).val _ p).symm

theorem xPoly_surjective : Function.Surjective (xPoly (K := K) (F := F)) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ Algebra.adjoin K {algebraMap K[X] F X} := hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨p, rfl⟩ := hy'
  exact ⟨p, Subtype.ext (by rw [xPoly_coe, algebraMap_eq_aeval]; rfl)⟩

theorem algebraMap_polyX_comp :
    (algebraMap (polyX K F) F).comp (xPoly (K := K) (F := F)).toRingHom = algebraMap K[X] F :=
  RingHom.ext fun p => xPoly_coe p

theorem isIntegral_polyX_iff (y : F) : IsIntegral K[X] y ↔ IsIntegral (polyX K F) y := by
  constructor
  · intro h
    exact h.map_of_comp_eq (xPoly (K := K) (F := F)).toRingHom (RingHom.id F)
      (by rw [algebraMap_polyX_comp]; rfl)
  · rintro ⟨p, hp, hpy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (f := (xPoly (K := K) (F := F)).toRingHom) xPoly_surjective p) hp
    refine ⟨q, hqm, ?_⟩
    rw [← algebraMap_polyX_comp, ← eval₂_map, hq, hpy]

variable (c0 : K)

theorem uc_mul_x : uc (algebraMap K[X] F X) c0 * algebraMap K[X] F X =
    1 + algebraMap K F c0 * uc (algebraMap K[X] F X) c0 := by
  have h := sub_mul_uc (transcendental_xF K F) c0 0
  simp only [map_zero, sub_zero] at h
  rw [mul_comm]
  exact h

theorem uc_mul_sub : uc (algebraMap K[X] F X) c0 * (algebraMap K[X] F X - algebraMap K F c0) = 1 :=
  inv_mul_cancel₀ (sub_ne_zero_of_tr (transcendental_xF K F) c0)

theorem exists_uc_pow_mul_polyA {y : F} (hy : y ∈ polyX K F) :
    ∃ n : ℕ, uc (algebraMap K[X] F X) c0 ^ n * y ∈ polyA (algebraMap K[X] F X) {c0} := by
  have hw := uc_mem_polyA (algebraMap K[X] F X) (Finset.mem_singleton_self c0)
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨1, ?_⟩
    rw [pow_one, uc_mul_x]
    exact Subalgebra.add_mem _ (Subalgebra.one_mem _) (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c0) hw)
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (pow_mul_mem_of_le hw (Nat.le_add_right m n) hm)
      (pow_mul_mem_of_le hw (Nat.le_add_left n m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact Subalgebra.mul_mem _ hm hn

theorem exists_sub_pow_mul_polyX {y : F} (hy : y ∈ polyA (algebraMap K[X] F X) {c0}) :
    ∃ n : ℕ, (algebraMap K[X] F X - algebraMap K F c0) ^ n * y ∈ polyX K F := by
  have hw : algebraMap K[X] F X - algebraMap K F c0 ∈ polyX K F :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton K _) (Subalgebra.algebraMap_mem _ c0)
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' : c = c0 := Finset.mem_singleton.1 (Finset.mem_coe.1 hc)
    subst hc'
    exact ⟨1, by rw [pow_one, mul_comm, uc_mul_sub]; exact Subalgebra.one_mem _⟩
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (pow_mul_mem_of_le hw (Nat.le_add_right m n) hm)
      (pow_mul_mem_of_le hw (Nat.le_add_left n m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact Subalgebra.mul_mem _ hm hn

/-- **`Rfin K F ⊆ B_{c0}[1/x']`.** -/
theorem exists_uc_pow_mul_chartRing (w : Rfin K F) :
    ∃ n : ℕ, uc (algebraMap K[X] F X) c0 ^ n * (w : F) ∈ chartRing (algebraMap K[X] F X) {c0} :=
  exists_pow_mul_isIntegral (uc_mem_polyA _ (Finset.mem_singleton_self c0))
    (fun _ hy => exists_uc_pow_mul_polyA c0 hy) ((isIntegral_polyX_iff _).1 w.2)

/-- **`B_{c0} ⊆ Rfin K F [1/(x - c0)]`.** -/
theorem exists_sub_pow_mul_rfin {b : F} (hb : b ∈ chartRing (algebraMap K[X] F X) {c0}) :
    ∃ n : ℕ, ∃ w : Rfin K F, (w : F) = (algebraMap K[X] F X - algebraMap K F c0) ^ n * b := by
  have hw : algebraMap K[X] F X - algebraMap K F c0 ∈ polyX K F :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton K _) (Subalgebra.algebraMap_mem _ c0)
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral hw (fun _ hy => exists_sub_pow_mul_polyX c0 hy) hb
  exact ⟨n, ⟨_, (isIntegral_polyX_iff _).2 hn⟩, rfl⟩

variable (K F) in
/-- The coordinate `x'` of the chart synonym, as an element of its ring of `x'`-integers. -/
noncomputable abbrev xS : Rfin K (SynF K F c0) := algebraMap K[X] (Rfin K (SynF K F c0)) X

theorem coe_xS : ((xS K F c0 : Rfin K (SynF K F c0)) : SynF K F c0) =
    synEquiv K F c0 (uc (algebraMap K[X] F X) c0) :=
  synAlg_X K F c0

/-- The exponent `n` with `x'^n w ∈ Rfin K F'`. -/
noncomputable def convN (w : Rfin K F) : ℕ := (exists_uc_pow_mul_chartRing c0 w).choose

/-- `x'^n w` as an element of `Rfin K F'`. -/
noncomputable def convW (w : Rfin K F) : Rfin K (SynF K F c0) :=
  rfinG c0 ⟨_, (exists_uc_pow_mul_chartRing c0 w).choose_spec⟩

theorem coe_convW (w : Rfin K F) : ((convW c0 w : Rfin K (SynF K F c0)) : SynF K F c0) =
    synEquiv K F c0 (uc (algebraMap K[X] F X) c0 ^ convN c0 w * (w : F)) := rfl

/-- The transported value `e'(x'^n w) / e'(x')^n`. -/
noncomputable def tpFun (e' : Rfin K (SynF K F c0) →ₐ[K] K) (w : Rfin K F) : K :=
  e' (convW c0 w) / e' (xS K F c0) ^ convN c0 w

variable (e' : Rfin K (SynF K F c0) →ₐ[K] K) (hx : e' (xS K F c0) ≠ 0)

include hx in
/-- **Independence of the exponent.** -/
theorem tp_eq (w : Rfin K F) (n : ℕ) (b : Rfin K (SynF K F c0))
    (hb : (b : SynF K F c0) = synEquiv K F c0 (uc (algebraMap K[X] F X) c0 ^ n * (w : F))) :
    tpFun c0 e' w = e' b / e' (xS K F c0) ^ n := by
  have key : convW c0 w * xS K F c0 ^ n = b * xS K F c0 ^ convN c0 w := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_xS, coe_convW, hb]
    simp only [← map_pow, ← map_mul]
    congr 1
    ring
  have h := congrArg e' key
  rw [map_mul, map_mul, map_pow, map_pow] at h
  rw [tpFun, div_eq_div_iff (pow_ne_zero _ hx) (pow_ne_zero _ hx)]
  exact h

include hx in
theorem tpFun_one : tpFun c0 e' 1 = 1 := by
  rw [tp_eq c0 e' hx 1 0 1 (by simp), map_one, pow_zero, div_one]

include hx in
theorem tpFun_zero : tpFun c0 e' 0 = 0 := by
  rw [tp_eq c0 e' hx 0 0 0 (by simp), map_zero, zero_div]

include hx in
theorem tpFun_mul (w1 w2 : Rfin K F) : tpFun c0 e' (w1 * w2) = tpFun c0 e' w1 * tpFun c0 e' w2 := by
  rw [tp_eq c0 e' hx (w1 * w2) (convN c0 w1 + convN c0 w2) (convW c0 w1 * convW c0 w2)
    (by simp only [MulMemClass.coe_mul, coe_convW, ← map_mul]; congr 1; ring), map_mul, pow_add,
    mul_div_mul_comm]
  rfl

include hx in
theorem tpFun_add (w1 w2 : Rfin K F) : tpFun c0 e' (w1 + w2) = tpFun c0 e' w1 + tpFun c0 e' w2 := by
  rw [tp_eq c0 e' hx (w1 + w2) (convN c0 w1 + convN c0 w2)
    (convW c0 w1 * xS K F c0 ^ convN c0 w2 + convW c0 w2 * xS K F c0 ^ convN c0 w1)
    (by simp only [AddMemClass.coe_add, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_xS, coe_convW]
        simp only [← map_pow, ← map_mul, ← map_add]; congr 1; ring)]
  simp only [tpFun]
  rw [map_add, map_mul, map_mul, map_pow, map_pow, div_add_div _ _ (pow_ne_zero _ hx) (pow_ne_zero _ hx), pow_add]
  ring

include hx in
theorem tpFun_algebraMap (r : K) : tpFun c0 e' (algebraMap K (Rfin K F) r) = algebraMap K K r := by
  rw [tp_eq c0 e' hx _ 0 (algebraMap K (Rfin K (SynF K F c0)) r) (by rw [pow_zero, one_mul]; rfl),
    AlgHom.commutes, pow_zero, div_one]

/-- **The transported `K`-point** of `Rfin K F`. -/
noncomputable def tpH : Rfin K F →ₐ[K] K where
  toFun := tpFun c0 e'
  map_one' := tpFun_one c0 e' hx
  map_mul' := tpFun_mul c0 e' hx
  map_zero' := tpFun_zero c0 e' hx
  map_add' := tpFun_add c0 e' hx
  commutes' := tpFun_algebraMap c0 e' hx

theorem tpH_apply (w : Rfin K F) : tpH c0 e' hx w = tpFun c0 e' w := rfl

/-- On `Rfin K F ∩ B_{c0}` the transported point is `e'` itself. -/
theorem tpH_of_mem (w : Rfin K F) (hw : (w : F) ∈ chartRing (algebraMap K[X] F X) {c0}) :
    tpH c0 e' hx w = e' (rfinG c0 ⟨_, hw⟩) := by
  rw [tpH_apply, tp_eq c0 e' hx w 0 (rfinG c0 ⟨_, hw⟩) (by rw [pow_zero, one_mul]; rfl), pow_zero, div_one]

theorem tpH_sub : tpH c0 e' hx (algebraMap K[X] (Rfin K F) (X - C c0)) = (e' (xS K F c0))⁻¹ := by
  rw [tpH_apply, tp_eq c0 e' hx _ 1 1 ?_, map_one, pow_one, one_div]
  rw [pow_one, OneMemClass.coe_one]
  show (1 : F) = uc (algebraMap K[X] F X) c0 * algebraMap K[X] F (X - C c0)
  rw [map_sub, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, uc_mul_sub]

variable [IsAlgClosed K]

theorem placeVal_ptP_eq_one (φ : Rfin K F →ₐ[K] K) {w : Rfin K F} (hw : φ w ≠ 0) :
    placeVal (Sum.inl (ptP φ) : Place K F) (algebraMap (Rfin K F) F w) = 1 := by
  rw [placeVal_inl]
  refine le_antisymm (HeightOneSpectrum.valuation_le_one (K := F) _ _) (not_lt.1 fun h => hw ?_)
  exact mem_ptP.1 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) _ _).1 h)

theorem sub_eq_algebraMap : algebraMap K[X] F X - algebraMap K F c0 =
    algebraMap (Rfin K F) F (algebraMap K[X] (Rfin K F) (X - C c0)) := by
  show _ = algebraMap K[X] F (X - C c0)
  rw [map_sub, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem placeVal_uc_eq_one (φ : Rfin K F →ₐ[K] K) (hφ : φ (algebraMap K[X] (Rfin K F) (X - C c0)) ≠ 0) :
    placeVal (Sum.inl (ptP φ) : Place K F) (uc (algebraMap K[X] F X) c0) = 1 := by
  rw [uc, map_inv₀, sub_eq_algebraMap, placeVal_ptP_eq_one φ hφ, inv_one]

theorem not_inr_of_uc (R : Place K F) (hR : placeVal R (uc (algebraMap K[X] F X) c0) = 1)
    (Q : HeightOneSpectrum (Rinf K (SynF K F c0))) : synPlace c0 R ≠ Sum.inr Q := fun hRc => by
  have h1 := one_lt_placeVal_inr_x (K := K) (F := SynF K F c0) Q
  rw [← hRc, synAlg_X, placeVal_synPlace, hR] at h1
  exact lt_irrefl _ h1

/-- **Place dictionary**: `tpH e'` has the place of `e'`. -/
theorem synPlace_tpH : synPlace c0 (Sum.inl (ptP (tpH c0 e' hx))) = Sum.inl (ptP e') := by
  have hφ : tpH c0 e' hx (algebraMap K[X] (Rfin K F) (X - C c0)) ≠ 0 := by
    rw [tpH_sub]; exact inv_ne_zero hx
  have hv1 := placeVal_uc_eq_one c0 _ hφ
  have hv2 : placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (algebraMap K[X] F X - algebraMap K F c0) = 1 := by
    rw [sub_eq_algebraMap, placeVal_ptP_eq_one _ hφ]
  rcases hRc : synPlace c0 (Sum.inl (ptP (tpH c0 e' hx))) with P | Q
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    suffices hφe : φ = e' by rw [hφe]
    have h1 : ∀ b, e' b = 0 → φ b = 0 := fun b hb0 => by
      set y : chartRing (algebraMap K[X] F X) {c0} := (rfinG c0).symm b with hy
      have eb : (b : SynF K F c0) = synEquiv K F c0 (y : F) := by
        rw [hy, ← rfinG_coe, AlgEquiv.apply_symm_apply]
      obtain ⟨n, w, hw⟩ := exists_sub_pow_mul_rfin c0 y.2
      have htw : tpH c0 e' hx w = 0 := by
        rw [tpH_apply, tp_eq c0 e' hx w n b ?_, hb0, zero_div]
        rw [eb, hw, ← mul_assoc, ← mul_pow, uc_mul_sub, one_pow, one_mul]
      have hlt : placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (algebraMap (Rfin K F) F w) < 1 := by
        rw [placeVal_inl]
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) _ _).2 (mem_ptP.2 htw)
      have heq : placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (algebraMap (Rfin K F) F w) =
          placeVal (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (y : F) := by
        show placeVal _ (w : F) = _
        rw [hw, map_mul, map_pow, hv2, one_pow, one_mul]
      have h2 := placeVal_synPlace c0 (Sum.inl (ptP (tpH c0 e' hx)) : Place K F) (y : F)
      rw [hRc, ← heq, ← eb, placeVal_inl] at h2
      exact mem_ptP.1 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := SynF K F c0) (ptP φ) b).1 (h2 ▸ hlt))
    refine AlgHom.ext fun b => ?_
    have ht := h1 (b - algebraMap K _ (e' b))
      (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at ht
    exact ht
  · exact absurd hRc (not_inr_of_uc c0 _ hv1 Q)

omit hx in
theorem eq_of_tpH_eq {e1 e2 : Rfin K (SynF K F c0) →ₐ[K] K} {h1 : e1 (xS K F c0) ≠ 0} {h2 : e2 (xS K F c0) ≠ 0}
    (h : tpH c0 e1 h1 = tpH c0 e2 h2) : e1 = e2 := by
  have h3 := synPlace_tpH c0 e1 h1
  rw [h, synPlace_tpH] at h3
  exact ptP_injective (Sum.inl_injective h3).symm

omit hx in
/-- Every `K`-point of `Rfin K F` off `x = c0` comes from the chart synonym. -/
theorem exists_tpH_eq (φ : Rfin K F →ₐ[K] K) (hφ : φ (algebraMap K[X] (Rfin K F) (X - C c0)) ≠ 0) :
    ∃ e' : Rfin K (SynF K F c0) →ₐ[K] K, ∃ h : e' (xS K F c0) ≠ 0, tpH c0 e' h = φ := by
  have hv1 := placeVal_uc_eq_one c0 φ hφ
  rcases hP : synPlace c0 (Sum.inl (ptP φ)) with P | Q
  · obtain ⟨e', rfl⟩ := exists_ptP P
    have hx' : e' (xS K F c0) ≠ 0 := fun h0 => by
      have h1 : placeVal (Sum.inl (ptP e') : Place K (SynF K F c0))
          (algebraMap (Rfin K (SynF K F c0)) (SynF K F c0) (xS K F c0)) < 1 := by
        rw [placeVal_inl]
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := SynF K F c0) _ _).2 (mem_ptP.2 h0)
      rw [← hP, (show algebraMap (Rfin K (SynF K F c0)) (SynF K F c0) (xS K F c0) =
        synEquiv K F c0 (uc (algebraMap K[X] F X) c0) from synAlg_X K F c0), placeVal_synPlace, hv1] at h1
      exact lt_irrefl _ h1
    refine ⟨e', hx', ptP_injective (Sum.inl_injective ((synPlace c0).injective ?_))⟩
    rw [synPlace_tpH, hP]
  · exact absurd hP (not_inr_of_uc c0 _ hv1 Q)

open Classical in
theorem Zdiv_apply_eq {G : Type u} [Field G] [Algebra K G] [Algebra K[X] G] [Algebra (RatFunc K) G]
    [IsScalarTower K[X] (RatFunc K) G] [IsScalarTower K K[X] G] [FunctionField K G]
    [Algebra.IsSeparable (RatFunc K) G] (S : Finset (Rfin K G →ₐ[K] K)) (P : Place K G) :
    Zdiv S P = if ∃ φ ∈ S, P = Sum.inl (ptP φ) then 1 else 0 := by
  rcases P with P | Q
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP]
    refine if_congr ⟨fun h => ⟨φ, h, rfl⟩, fun ⟨φ2, h2, he⟩ => ?_⟩ rfl rfl
    rwa [ptP_injective (Sum.inl_injective he)]
  · rw [Zdiv_inr, if_neg]
    rintro ⟨φ, -, h⟩
    exact Sum.inl_ne_inr h.symm

open Classical in
/-- **Transport of reduced divisors** under a matching of points with equal places. -/
theorem divMap_Zdiv (S : Finset (Rfin K F →ₐ[K] K)) (S' : Finset (Rfin K (SynF K F c0) →ₐ[K] K))
    (h1 : ∀ φ ∈ S, ∃ e' ∈ S', synPlace c0 (Sum.inl (ptP φ)) = Sum.inl (ptP e'))
    (h2 : ∀ e' ∈ S', ∃ φ ∈ S, synPlace c0 (Sum.inl (ptP φ)) = Sum.inl (ptP e')) :
    divMap (synEquiv K F c0) (Zdiv S) = Zdiv S' := by
  ext P'
  rw [divMap_apply, Zdiv_apply_eq, Zdiv_apply_eq]
  have hs : placeEquiv (synEquiv K F c0) = synPlace c0 := rfl
  rw [hs]
  refine if_congr ⟨fun ⟨φ, hφ, hR⟩ => ?_, fun ⟨e', he', hP⟩ => ?_⟩ rfl rfl
  · obtain ⟨e', he', he⟩ := h1 φ hφ
    refine ⟨e', he', ?_⟩
    rw [← he, ← hR, Equiv.apply_symm_apply]
  · obtain ⟨φ, hφ, he⟩ := h2 e' he'
    exact ⟨φ, hφ, by rw [hP, ← he, Equiv.symm_apply_apply]⟩

section ConvSym

variable {R : Type*} [CommRing R] [Algebra K R] {n n' : ℕ}
variable (φ' : SymRing K (Rfin K (SynF K F c0)) n' →ₐ[K] R) (hu : IsUnit (φ' (normS K (xS K F c0))))

omit hx in
include hu in
theorem tuple_ne_zero (y : R →ₐ[K] K) (l : Fin n') : liftTuple (y.comp φ') l (xS K F c0) ≠ 0 := by
  have h := hu.map y
  have e := symPt_normS (liftTuple (y.comp φ')) (xS K F c0)
  rw [symPt_liftTuple, AlgHom.comp_apply] at e
  rw [e] at h
  exact Finset.prod_ne_zero_iff.1 h.ne_zero l (Finset.mem_univ l)

/-- The transported tuple of points. -/
noncomputable def convPt (hn : n = n') (y : R →ₐ[K] K) : Fin n → (Rfin K F →ₐ[K] K) :=
  fun i => tpH c0 (liftTuple (y.comp φ') (Fin.cast hn i)) (tuple_ne_zero c0 φ' hu y _)

omit hx in
theorem convPt_normS (hn : n = n') (w : Rfin K F) :
    ∃ r : R, ∀ y : R →ₐ[K] K, y r = symPt (convPt c0 φ' hu hn y) (normS K w) := by
  subst hn
  refine ⟨φ' (normS K (convW c0 w)) * ↑(hu.unit⁻¹) ^ convN c0 w, fun y => ?_⟩
  have e1 : ∀ b : Rfin K (SynF K F c0), y (φ' (normS K b)) = ∏ l, liftTuple (y.comp φ') l b := fun b => by
    have h := symPt_normS (liftTuple (y.comp φ')) b
    rwa [symPt_liftTuple, AlgHom.comp_apply] at h
  have hinv : y ↑(hu.unit⁻¹) = (y (φ' (normS K (xS K F c0))))⁻¹ := by
    have h0 := congrArg y hu.mul_val_inv
    rw [map_mul, map_one] at h0
    exact eq_inv_of_mul_eq_one_right h0
  rw [map_mul, map_pow, hinv, e1, e1, symPt_normS]
  simp only [convPt, tpH_apply, tpFun, Fin.cast_eq_self]
  rw [Finset.prod_div_distrib, Finset.prod_pow, div_eq_mul_inv, inv_pow]

/-- **Conversion `Sym^n(Rfin F') → R` to `Sym^n(Rfin F) → R`** (when `N(x')` is a unit). -/
noncomputable def convSym [IsReduced R] [Algebra.FiniteType K R] (hn : n = n') :
    SymRing K (Rfin K F) n →ₐ[K] R :=
  liftPts (fun y => symPt (convPt c0 φ' hu hn y)) (convPt_normS c0 φ' hu hn)

omit hx in
theorem comp_convSym [IsReduced R] [Algebra.FiniteType K R] (hn : n = n') (y : R →ₐ[K] K) :
    y.comp (convSym c0 φ' hu hn) = symPt (convPt c0 φ' hu hn y) :=
  comp_liftPts _ _ y

omit hx in
open Classical in
/-- **The divisor of a converted point** is the transported divisor. -/
theorem divMap_Zdiv_convSym [IsReduced R] [Algebra.FiniteType K R] (hn : n = n') (y : R →ₐ[K] K) :
    divMap (synEquiv K F c0) (Zdiv (ptSet (y.comp (convSym c0 φ' hu hn)))) = Zdiv (ptSet (y.comp φ')) := by
  rw [comp_convSym, ptSet_symPt]
  apply divMap_Zdiv c0
  · intro φ hφ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hφ
    exact ⟨_, (mem_ptSet _ _).2 ⟨_, rfl⟩, synPlace_tpH c0 _ _⟩
  · intro e' he'
    obtain ⟨l, rfl⟩ := (mem_ptSet _ _).1 he'
    subst hn
    refine ⟨convPt c0 φ' hu rfl y l, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    exact synPlace_tpH c0 _ _

end ConvSym

end AJConv

end RamanujanPetersson.JacComplete

end


