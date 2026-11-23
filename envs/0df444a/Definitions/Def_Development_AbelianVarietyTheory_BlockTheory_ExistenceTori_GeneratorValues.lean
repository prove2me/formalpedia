-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:26.327781+00:00
-- url     : https://prove2.me/theorems/fca2e8f5-4655-40c0-971f-938e3b11f7a2
-- title:
--   Generator Values
-- statement:
--   Definitions and structural lemmas for Generator Values, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
def genVal {M : LB (TK R).left} (t : LB.Gen M) (j : M.ι) (h : ⊤ ≤ M.U j) : (FractionRing R)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom (res h (t.s j))
def IsIntChart (D : DegPre R) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (i : D.P.L.ι) :
    Prop :=
  ⊤ ≤ x.left ⁻¹ᵁ D.P.L.U i
def IsPsiCoord (D : DegPre R) (χ : D.X) (x : (FractionRing R)ˣ) : Prop :=
  ∃ (j : PUnit → D.P.L.ι) (h : ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ)
      (fun _ => -1)).U j), IsIntChart D (D.c χ) (j PUnit.unit) ∧ x = genVal (D.psi χ) j h
def IsTauCoord (D : DegPre R) (a b : D.X) (x : (FractionRing R)ˣ) : Prop :=
  ∃ (j : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → D.P.L.ι) (h : ⊤ ≤ _),
    IsIntChart D (D.c (a + b)) (j (.inl (.inl (.inl PUnit.unit)))) ∧
    IsIntChart D (D.c a) (j (.inl (.inl (.inr PUnit.unit)))) ∧
    IsIntChart D (D.c b) (j (.inl (.inr PUnit.unit))) ∧
    IsIntChart D η[D.P.A] (j (.inr PUnit.unit)) ∧ x = genVal (D.tau a b) j h
theorem exists_isPsiCoord [IsLocalRing R] (D : DegPre R) (χ : D.X) : ∃ x, IsPsiCoord D χ x := by
  have hc : (D.c χ).left (closedPoint R) ∈ ⨆ i, D.P.L.U i := by
    rw [D.P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  have ht : IsIntChart D (D.c χ) i :=
    ((closedPoint_mem_iff (R := R) ((D.c χ).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge
  refine ⟨_, fun _ => i, ?_, ht, rfl⟩
  intro y _
  exact Set.mem_iInter.2 fun _ => ht (Set.mem_univ (jK R y))
def psiCoord [IsLocalRing R] (D : DegPre R) (χ : D.X) : (FractionRing R)ˣ :=
  (exists_isPsiCoord D χ).choose
structure LatticeVal (R : Type) [CommRing R] [IsDomain R] (Γ : Type) [AddCommGroup Γ] where
  toFun : (FractionRing R)ˣ → Γ
  map_mul : ∀ x y, toFun (x * y) = toFun x + toFun y
  map_unit : ∀ u : Rˣ, toFun (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 0
section General
variable [IsLocalRing R] {Γ : Type} [AddCommGroup Γ] (v : LatticeVal R Γ)
def psiVal (D : DegPre R) (χ : D.X) : Γ := v.toFun (psiCoord D χ)
def periodForm (D : DegPre R) (a b : D.X) : Γ := psiVal v D (a + b) - psiVal v D a - psiVal v D b
end General
def psiOrd [IsLocalRing R] (D : DegData R (maximalIdeal R)) (χ : D.toPre.X) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : D.toPre.PsiIn χ (maximalIdeal R ^ n)), (n : ℕ∞)
section DVR
variable (R) [IsDiscreteValuationRing R]
lemma valuation_ne_zero (x : (FractionRing R)ˣ) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) x.val ≠ 0 :=
  (Valuation.ne_zero_iff _).2 x.ne_zero
def ord_vw : LatticeVal R ℤ where
  toFun x := - WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) x.val)
  map_mul x y := by
    rw [Units.val_mul, map_mul, WithZero.log_mul (valuation_ne_zero R x) (valuation_ne_zero R y),
      neg_add]
  map_unit u := by
    have : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
        (algebraMap R (FractionRing R) u) = 1 := by
      erw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (mem_maximalIdeal _).1 h u.isUnit
    change - WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
        (algebraMap R (FractionRing R) u)) = 0
    rw [this]; simp
end DVR
def toUnitK (r : R) (hr : r ≠ 0) : (FractionRing R)ˣ :=
  Units.mk0 (algebraMap R (FractionRing R) r)
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
structure IsOverPrime (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ) : Prop where
  prime : p.Prime
  ne_zero : (p : R) ≠ 0
  mem : (p : R) ∈ maximalIdeal R
section DVR
variable [IsDiscreteValuationRing R]
theorem ord_vw_uniformiser {ϖ : R} (h0 : ϖ ≠ 0) (h : maximalIdeal R = Ideal.span {ϖ}) :
    (ord_vw R).toFun (toUnitK ϖ h0) = 1 := by
  change - WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
        (algebraMap R (FractionRing R) ϖ)) = 1
  erw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ h0 h]
  simp
def ramIdx {p : ℕ} (hp : IsOverPrime R p) : ℤ := (ord_vw R).toFun (toUnitK (p : R) hp.ne_zero)
def ord_vp {p : ℕ} (hp : IsOverPrime R p) : LatticeVal R ℚ where
  toFun x := ((ord_vw R).toFun x : ℚ) / (ramIdx hp : ℚ)
  map_mul x y := by rw [(ord_vw R).map_mul]; push_cast; ring
  map_unit u := by rw [(ord_vw R).map_unit]; simp
def psiOrd_vw (D : DegPre R) (χ : D.X) : ℤ := psiVal (ord_vw R) D χ
def periodForm_vw (D : DegPre R) (a b : D.X) : ℤ := periodForm (ord_vw R) D a b
def psiOrd_vp {p : ℕ} (hp : IsOverPrime R p) (D : DegPre R) (χ : D.X) : ℚ :=
  psiVal (ord_vp hp) D χ
def periodForm_vp {p : ℕ} (hp : IsOverPrime R p) (D : DegPre R) (a b : D.X) : ℚ :=
  periodForm (ord_vp hp) D a b
end DVR
section Normed
variable [IsLocalRing R] {F : Type} [NormedField F]
structure IsCentred (φ : FractionRing R →+* F) : Prop where
  le_one : ∀ r : R, ‖φ (algebraMap R (FractionRing R) r)‖ ≤ 1
  lt_one : ∀ r ∈ maximalIdeal R, ‖φ (algebraMap R (FractionRing R) r)‖ < 1
variable {φ : FractionRing R →+* F}
omit [IsDomain R] in
theorem IsCentred.norm_unit (hφ : IsCentred φ) (u : Rˣ) :
    ‖φ (algebraMap R (FractionRing R) u)‖ = 1 := by
  have h1 := hφ.le_one u
  have h2 := hφ.le_one (u⁻¹ : Rˣ)
  have h3 : ‖φ (algebraMap R (FractionRing R) u)‖ * ‖φ (algebraMap R (FractionRing R) (u⁻¹ : Rˣ))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  nlinarith [norm_nonneg (φ (algebraMap R (FractionRing R) u))]
def normVal_vp (hφ : IsCentred φ) {p : ℕ} (_hp : IsOverPrime R p) : LatticeVal R ℝ where
  toFun x := Real.log ‖φ x.val‖ / Real.log ‖(p : F)‖
  map_mul x y := by
    rw [Units.val_mul, map_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero φ).2 x.ne_zero))
        (norm_ne_zero_iff.2 ((map_ne_zero φ).2 y.ne_zero)), add_div]
  map_unit u := by
    change Real.log ‖φ (algebraMap R (FractionRing R) u)‖ / _ = 0
    rw [hφ.norm_unit, Real.log_one, zero_div]
def psiOrdAt_vp (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) (D : DegPre R) (χ : D.X) : ℝ :=
  psiVal (normVal_vp hφ hp) D χ
def periodFormAt_vp (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) (D : DegPre R)
    (a b : D.X) : ℝ :=
  periodForm (normVal_vp hφ hp) D a b
end Normed
theorem isOverPrime_padicInt (p : ℕ) [hp : Fact p.Prime] : IsOverPrime ℤ_[p] p where
  prime := hp.out
  ne_zero := Nat.cast_ne_zero.2 hp.out.ne_zero
  mem := by rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
example (p : ℕ) [Fact p.Prime] : ramIdx (isOverPrime_padicInt p) = 1 :=
  ord_vw_uniformiser _ PadicInt.maximalIdeal_eq_span_p
def PsiIntegral : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (χ : D.toPre.X), D.toPre.PsiIn χ (maximalIdeal R ^ 0)
def PsiOrdFinite : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D : DegData R (maximalIdeal R)) (χ : D.toPre.X), psiOrd D χ ≠ ⊤
def PsiOrdEqVal : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
    (∀ (D : DegPre R) (χ : D.X) (n : ℕ), D.PsiIn χ (maximalIdeal R ^ n) ↔ (n : ℤ) ≤ psiOrd_vw D χ) ∧
    ∀ (D : DegData R (maximalIdeal R)) (χ : D.toPre.X),
      ∃ n : ℕ, psiOrd D χ = n ∧ psiOrd_vw D.toPre χ = n
def PeriodFormEqValTau : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X),
    (∃ x, IsTauCoord D a b x) ∧
    ∀ (Γ : Type) [AddCommGroup Γ] (v : LatticeVal R Γ) (x : (FractionRing R)ˣ),
      IsTauCoord D a b x → periodForm v D a b = v.toFun x
def PeriodFormBilinear : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (Γ : Type) [AddCommGroup Γ] (v : LatticeVal R Γ),
    (∀ a a' b, periodForm v D.toPre (a + a') b = periodForm v D.toPre a b + periodForm v D.toPre a' b) ∧
    (∀ a b b', periodForm v D.toPre a (b + b') = periodForm v D.toPre a b + periodForm v D.toPre a b') ∧
    ∀ x, 2 • psiVal v D.toPre x = periodForm v D.toPre x x
def PeriodFormBalanced : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (_ : D.OAct O)
    (Γ : Type) [AddCommGroup Γ] (v : LatticeVal R Γ) (a : O) (x x' : D.toPre.X),
    periodForm v D.toPre (a • x) x' = periodForm v D.toPre x (star a • x')
def PsiOrdEqHalfForm : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (D : DegData R (maximalIdeal R))
    (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (_ : D.OAct O) (w₀ : O),
    w₀ + star w₀ = 1 → ∀ x : D.toPre.X,
      psiOrd_vw D.toPre x = periodForm_vw D.toPre x (w₀ • x) ∧
      psiOrd_vw D.toPre x = periodForm_vw D.toPre x (star w₀ • x)
def PeriodFormPos : Prop :=
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (D : DegData R (maximalIdeal R)) (x : D.toPre.X), x ≠ 0 →
      0 < psiOrd_vw D.toPre x ∧ 0 < periodForm_vw D.toPre x x) ∧
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (F : Type) [NormedField F] (φ : FractionRing R →+* F) (hφ : IsCentred φ)
    (p : ℕ) (hp : IsOverPrime R p) (x : D.toPre.X), x ≠ 0 →
      0 < psiOrdAt_vp hφ hp D.toPre x ∧ 0 < periodFormAt_vp hφ hp D.toPre x x
def PeriodFormAtEq : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (D : DegPre R)
    (F : Type) [NormedField F] (φ : FractionRing R →+* F) (hφ : IsCentred φ)
    (p : ℕ) (hp : IsOverPrime R p),
    (∀ χ, psiOrdAt_vp hφ hp D χ = (psiOrd_vp hp D χ : ℝ)) ∧
    ∀ a b, periodFormAt_vp hφ hp D a b = (periodForm_vp hp D a b : ℝ)
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues


