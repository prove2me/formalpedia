-- Prove2me | Definitions.Def_RPLib_S4_CDPack43c
-- name    : RPLib_S4_CDPack43c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:43:08.080341+00:00
-- url     : https://prove2.me/theorems/1a72a586-59c9-40e2-806e-d5a40faf2312
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 43c of 71
-- statement:
--   Part 43c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ThetaSquare_PlusC`: Unit S4-ThetaSquare, file PlusC: the ring `R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`
--   * `Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack27
import Definitions.Def_RPLib_S4_CDPack40
import Definitions.Def_RPLib_S4_CDPack43
import Definitions.Def_RPLib_S4_CDPack41w
import Definitions.Def_RPLib_S4_CDPack43b

/-!
# Curve-duality library package, part 43c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ThetaSquare_PlusC`: Unit S4-ThetaSquare, file PlusC: the ring `R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`
* `Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_PlusC =====
section

/-!
# Unit S4-ThetaSquare, file PlusC: the ring `R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`

The plus-curve is placed on `R1 c0 := B_{c0} ⊔ Rfin ⊆ F`, which is both the localization of the chart ring
`B_{c0}` at `x' = 1/(x - c0)` (`isLocalization_bc_R1`) and the localization of `Rfin` at `x - c0`
(`isLocalization_rfin_R1`); both inclusions are open immersions on spectra. Also `Sym¹ B ≃ B` (`sym1Equiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial AlgebraicGeometry

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete

universe u

section Sym1

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- `Sym¹ B → B`, the inverse of `diag1`. -/
noncomputable def undiag1 : SymRing k B 1 →ₐ[k] B :=
  (ptOfR (fun _ : Fin 1 => AlgHom.id k B)).comp (SymRing k B 1).val

theorem undiag1_diag1 (b : B) : undiag1 (diag1 (k := k) b) = b := by
  change ptOfR _ (diag1 (k := k) b : XPow k B 1) = b
  rw [diag1_coe, ptOfR_inc]
  rfl

theorem inc_comp_ptOfR_id :
    (inc (k := k) (B := B) (g := 1) 0).comp (ptOfR (fun _ : Fin 1 => AlgHom.id k B)) =
      AlgHom.id k (XPow k B 1) := by
  apply PiTensorProduct.algHom_ext
  intro i
  rw [Subsingleton.elim i 0]
  change ((inc 0).comp (ptOfR (fun _ : Fin 1 => AlgHom.id k B))).comp (inc 0) = (AlgHom.id k _).comp (inc 0)
  rw [AlgHom.comp_assoc, ptOfR_comp_inc, AlgHom.comp_id, AlgHom.id_comp]

theorem diag1_undiag1 (x : SymRing k B 1) : diag1 (undiag1 x) = x := by
  apply Subtype.ext
  rw [diag1_coe]
  change ((inc 0).comp (ptOfR (fun _ : Fin 1 => AlgHom.id k B))) (x : XPow k B 1) = _
  rw [inc_comp_ptOfR_id]
  rfl

/-- **`Sym¹ B ≃ B`.** -/
noncomputable def sym1Equiv : SymRing k B 1 ≃ₐ[k] B :=
  AlgEquiv.ofAlgHom undiag1 diag1 (AlgHom.ext undiag1_diag1) (AlgHom.ext diag1_undiag1)

@[simp] theorem sym1Equiv_apply (x : SymRing k B 1) : sym1Equiv x = undiag1 x := rfl

@[simp] theorem sym1Equiv_symm_apply (b : B) : sym1Equiv.symm b = diag1 (k := k) b := rfl

end Sym1

section PlusC

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable (F) in
/-- The chart ring `B_{c0}` of the curve. -/
noncomputable abbrev Bc : Subalgebra K F := chartRing (algebraMap K[X] F X) {c0}

variable (F) in
/-- **`R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`** inside `F`. -/
noncomputable def R1 : Subalgebra K F := Bc F c0 ⊔ (FunctionField.ringOfIntegers K F).restrictScalars K

theorem bc_le_R1 : Bc F c0 ≤ R1 F c0 := le_sup_left

theorem rfin_mem_R1 (w : Rfin K F) : (w : F) ∈ R1 F c0 :=
  (le_sup_right : (FunctionField.ringOfIntegers K F).restrictScalars K ≤ R1 F c0) w.2

/-- `B_{c0} → R1`. -/
noncomputable def inclB : Bc F c0 →ₐ[K] R1 F c0 := Subalgebra.inclusion (bc_le_R1 c0)

/-- `Rfin → R1`. -/
noncomputable def inclR : Rfin K F →ₐ[K] R1 F c0 :=
  (IsScalarTower.toAlgHom K (Rfin K F) F).codRestrict (R1 F c0) (rfin_mem_R1 c0)

@[simp] theorem coe_inclB (b : Bc F c0) : ((inclB c0 b : R1 F c0) : F) = b := rfl

@[simp] theorem coe_inclR (w : Rfin K F) : ((inclR c0 w : R1 F c0) : F) = w := rfl

noncomputable instance algBR1 : Algebra (Bc F c0) (R1 F c0) := (inclB c0).toRingHom.toAlgebra

noncomputable instance algRR1 : Algebra (Rfin K F) (R1 F c0) := (inclR c0).toRingHom.toAlgebra

@[simp] theorem algebraMap_bc_R1 (b : Bc F c0) : algebraMap (Bc F c0) (R1 F c0) b = inclB c0 b := rfl

@[simp] theorem algebraMap_rfin_R1 (w : Rfin K F) : algebraMap (Rfin K F) (R1 F c0) w = inclR c0 w := rfl

variable (F) in
/-- `x' = 1/(x - c0)` in `B_{c0}`. -/
noncomputable def uc0 : Bc F c0 :=
  ⟨uc (algebraMap K[X] F X) c0, polyA_le_chartRing _ _ (uc_mem_polyA _ (Finset.mem_singleton_self c0))⟩

@[simp] theorem coe_uc0 : ((uc0 F c0 : Bc F c0) : F) = uc (algebraMap K[X] F X) c0 := rfl

variable (F) in
/-- `x - c0` in `Rfin`. -/
noncomputable def xcR : Rfin K F := algebraMap K[X] (Rfin K F) (X - C c0)

theorem coe_xcR : ((xcR F c0 : Rfin K F) : F) = algebraMap K[X] F X - algebraMap K F c0 := by
  change algebraMap K[X] F (X - C c0) = _
  rw [map_sub, IsScalarTower.algebraMap_apply K K[X] F c0, Polynomial.algebraMap_eq]

theorem uc_mem_bc : uc (algebraMap K[X] F X) c0 ∈ Bc F c0 := (uc0 F c0).2

/-- `R1 ⊆ B_{c0}[1/x']`. -/
theorem exists_uc_pow_mul_bc {z : F} (hz : z ∈ R1 F c0) :
    ∃ n : ℕ, uc (algebraMap K[X] F X) c0 ^ n * z ∈ Bc F c0 := by
  have hu := uc_mem_bc (F := F) c0
  rw [R1, Algebra.sup_def] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact ⟨0, by simpa using hz⟩
    · exact exists_uc_pow_mul_chartRing c0 ⟨z, hz⟩
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem (Bc F c0) r⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have e : uc (algebraMap K[X] F X) c0 ^ (m + n) * (a + b) =
        uc (algebraMap K[X] F X) c0 ^ n * (uc (algebraMap K[X] F X) c0 ^ m * a) +
          uc (algebraMap K[X] F X) c0 ^ m * (uc (algebraMap K[X] F X) c0 ^ n * b) := by ring
    rw [e]
    exact add_mem (mul_mem (pow_mem hu n) hm) (mul_mem (pow_mem hu m) hn)
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact mul_mem hm hn

/-- `R1 ⊆ Rfin[1/(x - c0)]`. -/
theorem exists_sub_pow_mul_rfin_R1 {z : F} (hz : z ∈ R1 F c0) :
    ∃ n : ℕ, ∃ w : Rfin K F, (w : F) = (algebraMap K[X] F X - algebraMap K F c0) ^ n * z := by
  rw [R1, Algebra.sup_def] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact exists_sub_pow_mul_rfin c0 hz
    · exact ⟨0, ⟨z, hz⟩, by rw [pow_zero, one_mul]⟩
  | algebraMap r =>
    refine ⟨0, algebraMap K[X] (Rfin K F) (C r), ?_⟩
    rw [pow_zero, one_mul]
    change algebraMap K[X] F (C r) = _
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  | add a b _ _ ha hb =>
    obtain ⟨m, w1, hw1⟩ := ha
    obtain ⟨n, w2, hw2⟩ := hb
    refine ⟨m + n, xcR F c0 ^ n * w1 + xcR F c0 ^ m * w2, ?_⟩
    push_cast
    rw [coe_xcR, hw1, hw2]
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨m, w1, hw1⟩ := ha
    obtain ⟨n, w2, hw2⟩ := hb
    refine ⟨m + n, w1 * w2, ?_⟩
    push_cast
    rw [hw1, hw2]
    ring

theorem uc_mul_xcR : (inclB c0 (uc0 F c0)) * inclR c0 (xcR F c0) = 1 := by
  apply Subtype.ext
  change uc (algebraMap K[X] F X) c0 * ((xcR F c0 : Rfin K F) : F) = 1
  rw [coe_xcR, uc_mul_sub]

/-- **`R1 = B_{c0}[1/x']`.** -/
instance isLocalization_bc_R1 : IsLocalization.Away (uc0 F c0) (R1 F c0) := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · exact IsUnit.of_mul_eq_one _ (uc_mul_xcR c0)
  · intro s
    obtain ⟨n, hn⟩ := exists_uc_pow_mul_bc c0 s.2
    refine ⟨n, ⟨_, hn⟩, Subtype.ext ?_⟩
    rw [algebraMap_bc_R1, algebraMap_bc_R1]
    push_cast
    rw [coe_inclB, coe_inclB, coe_uc0]
    ring
  · intro a b h
    refine ⟨0, ?_⟩
    have e0 := congrArg Subtype.val h
    have e : (a : F) = b := e0
    rw [Subtype.ext e]

/-- **`R1 = Rfin[1/(x - c0)]`.** -/
instance isLocalization_rfin_R1 : IsLocalization.Away (xcR F c0) (R1 F c0) := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans (uc_mul_xcR c0))
  · intro s
    obtain ⟨n, w, hw⟩ := exists_sub_pow_mul_rfin_R1 c0 s.2
    refine ⟨n, w, Subtype.ext ?_⟩
    rw [algebraMap_rfin_R1, algebraMap_rfin_R1]
    push_cast
    rw [coe_inclR, coe_inclR, hw, coe_xcR]
    ring
  · intro a b h
    refine ⟨0, ?_⟩
    have e0 := congrArg Subtype.val h
    have e : (a : F) = b := e0
    rw [Subtype.ext e]

theorem isOpenImmersion_bc_R1 :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Bc F c0) (R1 F c0)))) :=
  IsOpenImmersion.of_isLocalization (uc0 F c0)

theorem isOpenImmersion_rfin_R1 :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Rfin K F) (R1 F c0)))) :=
  IsOpenImmersion.of_isLocalization (xcR F c0)

end PlusC

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaSquare_PlusJ =====
section

/-!
# Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula

For `g` points `a_i` of `Rfin` and a slot `i0`, `plusR = plusMap inclR a i0 : Sym^g Rfin → R1`; with `h = plusR(u0)`
and `R2 = R1[1/h]` it induces **`lawMapPlus : LawRing → R2`**, whose `K`-points have class
`[P] + [E] - [Θ]` (`psiJ_lawMapPlus`), `P` the point of `Rfin` under `x`, `E = Σ_{i ≠ i0} a_i` (`plusE`).
Also: the center of a `K`-point `y` of `R1` restricted to `B_{c0}` is the finite place of `y|Rfin` (`isCenter_R1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial AlgebraicGeometry

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.RR

universe u

section PlusJ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable [IsAlgClosed K]

theorem placeVal_inl_coe (P : HeightOneSpectrum (Rfin K F)) (w : Rfin K F) :
    placeVal (Sum.inl P : Place K F) (w : F) = P.valuation F (algebraMap (Rfin K F) F w) := rfl

theorem inclR_xcR_ne (y : R1 F c0 →ₐ[K] K) : y (inclR c0 (xcR F c0)) ≠ 0 := by
  intro h
  have e := congrArg y (uc_mul_xcR c0)
  rw [map_mul, h, mul_zero, map_one] at e
  exact zero_ne_one e

/-- **Centers on `R1`**: the center of `y|B_{c0}` is the finite place of `y|Rfin`. -/
theorem isCenter_R1 (y : R1 F c0 →ₐ[K] K) :
    IsCenter (Sum.inl (ptP (y.comp (inclR c0))) : Place K F) (y.comp (inclB c0)) := by
  have hxc : (ptP (y.comp (inclR c0))).valuation F (algebraMap (Rfin K F) F (xcR F c0)) = 1 := by
    refine le_antisymm (HeightOneSpectrum.valuation_le_one (K := F) (ptP (y.comp (inclR c0))) _) (not_lt.1 fun hlt => ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), mem_ptP] at hlt
    exact inclR_xcR_ne c0 y hlt
  have key : ∀ b : Bc F c0, ∃ n : ℕ, ∃ w : Rfin K F, placeVal (Sum.inl (ptP (y.comp (inclR c0))) : Place K F) (b : F) =
      (ptP (y.comp (inclR c0))).valuation F (algebraMap (Rfin K F) F w) ∧ (y.comp (inclR c0) w = 0 ↔ y.comp (inclB c0) b = 0) := by
    intro b
    obtain ⟨n, w, hw⟩ := exists_sub_pow_mul_rfin c0 b.2
    refine ⟨n, w, ?_, ?_⟩
    · rw [placeVal_inl]
      change _ = (ptP (y.comp (inclR c0))).valuation F (w : F)
      rw [hw, map_mul, map_pow, ← coe_xcR]
      change _ = (ptP (y.comp (inclR c0))).valuation F (algebraMap (Rfin K F) F (xcR F c0)) ^ n * _
      rw [hxc, one_pow, one_mul]
    · have e : inclR c0 w = inclR c0 (xcR F c0) ^ n * inclB c0 b := by
        apply Subtype.ext
        push_cast
        rw [coe_inclR, coe_inclR, coe_inclB, hw, coe_xcR]
      rw [AlgHom.comp_apply, AlgHom.comp_apply, e, map_mul, map_pow, mul_eq_zero,
        or_iff_right (pow_ne_zero n (inclR_xcR_ne c0 y))]
  refine ⟨fun b => ?_, fun b => ?_⟩
  · obtain ⟨n, w, h1, -⟩ := key b
    rw [h1]
    exact HeightOneSpectrum.valuation_le_one (K := F) (ptP (y.comp (inclR c0))) _
  · obtain ⟨n, w, h1, h2⟩ := key b
    rw [h1, HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), mem_ptP, h2]

/-- The chart index `{c0}`. -/
noncomputable abbrev idx0 : ChartIdx K := ⟨{c0}, Finset.singleton_nonempty c0⟩

theorem plA_R1 (y : R1 F c0 →ₐ[K] K) :
    plA (idx0 c0) (y.comp (inclB c0)) = (Sum.inl (ptP (y.comp (inclR c0))) : Place K F) :=
  plA_eq_of_isCenter (idx0 c0) (isCenter_R1 c0 y)

variable (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- The plus-curve on `R1`. -/
noncomputable abbrev plusR : SymRing K (Rfin K F) (genusFK K F) →ₐ[K] R1 F c0 := plusMap (inclR c0) a i0

/-- `h = plus(u0)`. -/
noncomputable def plusH : R1 F c0 := plusR c0 a i0 (lawPre K F).u0

/-- **The coordinate ring of the plus-curve**, `R2 = R1[1/h]`. -/
abbrev R2 : Type u := Localization.Away (plusH c0 a i0)

theorem isUnit_plusH :
    IsUnit (((awayι (K := K) (plusH c0 a i0)).comp (plusR c0 a i0)) (lawPre K F).u0) :=
  IsLocalization.Away.algebraMap_isUnit (plusH c0 a i0)

/-- **The plus-curve `Spec R2 → X0`** as `LawRing K F → R2`. -/
noncomputable def lawMapPlus : LawRing K F →ₐ[K] R2 c0 a i0 :=
  IsLocalization.Away.liftAlgHom (f := (awayι (K := K) (plusH c0 a i0)).comp (plusR c0 a i0)) (lawPre K F).u0
    (isUnit_plusH c0 a i0)

theorem lawMapPlus_comp : (lawMapPlus c0 a i0).comp (awayι (K := K) (lawPre K F).u0) =
    (awayι (K := K) (plusH c0 a i0)).comp (plusR c0 a i0) :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, awayι_apply, lawMapPlus, IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq]
    rfl

theorem comp_lawMapPlus (x : R2 c0 a i0 →ₐ[K] K) :
    (x.comp (lawMapPlus c0 a i0)).comp (awayι (K := K) (lawPre K F).u0) =
      symPt (Function.update a i0 ((x.comp (awayι (K := K) (plusH c0 a i0))).comp (inclR c0))) := by
  rw [AlgHom.comp_assoc, lawMapPlus_comp, ← AlgHom.comp_assoc]
  exact comp_plusMap _ _ _ _

/-- The point of `Rfin` under a `K`-point `x` of `R2`. -/
noncomputable abbrev ptR2 (x : R2 c0 a i0 →ₐ[K] K) : Rfin K F →ₐ[K] K :=
  (x.comp (awayι (K := K) (plusH c0 a i0))).comp (inclR c0)

/-- `E = Σ_{i ≠ i0} [a_i]`. -/
noncomputable def plusE : Places.Divisor K F :=
  ∑ i ∈ Finset.univ.erase i0, Finsupp.single (Sum.inl (ptP (a i))) 1

open Classical in
theorem injective_update (x : R2 c0 a i0 →ₐ[K] K) :
    Function.Injective (Function.update a i0 (ptR2 c0 a i0 x)) := by
  have hc := card_lawPt (K := K) (F := F) (yR := x.comp (lawMapPlus c0 a i0))
  rw [comp_lawMapPlus, ptSet_symPt] at hc
  have h2 : (Finset.univ.image (Function.update a i0 (ptR2 c0 a i0 x))).card = (Finset.univ : Finset (Fin (genusFK K F))).card := by
    rw [hc, Finset.card_univ, Fintype.card_fin]
  intro i j hij
  exact Finset.card_image_iff.1 h2 (Finset.mem_coe.2 (Finset.mem_univ i)) (Finset.mem_coe.2 (Finset.mem_univ j)) hij

open Classical in
/-- **Class formula of the plus-curve**: `ψ(plus(x)) = [P] + [E] - [Θ]`. -/
theorem psiJ_lawMapPlus (x : R2 c0 a i0 →ₐ[K] K) :
    psiJ K F (kpt (x.comp (lawMapPlus c0 a i0))) =
      clsK K F (Finsupp.single (Sum.inl (ptP (ptR2 c0 a i0 x))) 1) + clsK K F (plusE a i0) - thetaK K F := by
  have hinj := injective_update c0 a i0 x
  have e : ∑ i ∈ Finset.univ.erase i0,
      Finsupp.single (Sum.inl (ptP (Function.update a i0 (ptR2 c0 a i0 x) i)) : Place K F) (1 : ℤ) = plusE a i0 :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [psiJ, psiS_kpt]
  change clsK K F (Zdiv (ptSet ((x.comp (lawMapPlus c0 a i0)).comp (awayι (K := K) (lawPre K F).u0)))) -
    thetaK K F = _
  rw [comp_lawMapPlus, ptSet_symPt, Zdiv, Finset.sum_image (fun i _ j _ h => hinj h),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), Function.update_self, clsK_add, e]

end PlusJ

end RamanujanPetersson.ThetaSquare

end


