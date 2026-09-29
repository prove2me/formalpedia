-- Prove2me | solution 1 for AutomorphicForm.exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9608d6f8-c417-5425-9030-34b55e152994

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal Topology

namespace R4Fi

variable {F : Type} [Field F] [NumberField F]

abbrev L (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  (finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))

theorem L_apply (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    L v g i j = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v := rfl

theorem L_mul (v : HeightOneSpectrum (𝓞 F)) (g h : AdelicGL2 (𝓞 F) F) : L v (g * h) = L v g * L v h := by
  simp only [L, map_mul, Units.val_mul]

theorem L_one (v : HeightOneSpectrum (𝓞 F)) : L v (1 : AdelicGL2 (𝓞 F) F) = 1 := by
  simp only [L, map_one, Units.val_one]

theorem L_inv_mul (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) : L v g⁻¹ * L v g = 1 := by
  rw [← L_mul, inv_mul_cancel, L_one]

theorem L_mul_inv (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) : L v g * L v g⁻¹ = 1 := by
  rw [← L_mul, mul_inv_cancel, L_one]

def IsKf (g : AdelicGL2 (𝓞 F) F) : Prop := g ∈ adelicMaximalCompact F ∧ glArch (𝓞 F) F g = 1

theorem IsKf.mul {g h : AdelicGL2 (𝓞 F) F} (hg : IsKf g) (hh : IsKf h) : IsKf (g * h) :=
  ⟨(adelicMaximalCompact F).mul_mem hg.1 hh.1, by rw [map_mul, hg.2, hh.2, mul_one]⟩

theorem IsKf.inv {g : AdelicGL2 (𝓞 F) F} (hg : IsKf g) : IsKf g⁻¹ :=
  ⟨(adelicMaximalCompact F).inv_mem hg.1, by rw [map_inv, hg.2, inv_one]⟩

theorem isKf_one : IsKf (1 : AdelicGL2 (𝓞 F) F) :=
  ⟨(adelicMaximalCompact F).one_mem, map_one _⟩

theorem IsKf.valued_le_one {g : AdelicGL2 (𝓞 F) F} (hg : IsKf g) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    Valued.v (L v g i j) ≤ 1 ∧ Valued.v (L v g⁻¹ i j) ≤ 1 :=
  valued_finComponent_apply_le_one hg.1 v i j

theorem IsKf.mem_integers {g : AdelicGL2 (𝓞 F) F} (hg : IsKf g) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F ∧
    (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v
      ∈ v.adicCompletionIntegers F :=
  ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hg.valued_le_one v i j).1,
   (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hg.valued_le_one v i j).2⟩

theorem isKf_of (g : AdelicGL2 (𝓞 F) F) (h1 : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F)
    (h2 : glArch (𝓞 F) F g = 1) : IsKf g := by
  refine ⟨⟨h1, fun w => ?_⟩, h2⟩
  rw [h2, map_one]; exact isRowIsometry_one

abbrev rad (e : ℕ) : WithZero (Multiplicative ℤ) := WithZero.exp (-(e : ℤ))

theorem rad_lt_one {e : ℕ} (he : 1 ≤ e) : rad e < 1 := by
  rw [rad, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem rad_le_one (e : ℕ) : rad e ≤ 1 := by
  rw [rad, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

def IsLevel (T : Finset (HeightOneSpectrum (𝓞 F))) (e : ℕ) (g : AdelicGL2 (𝓞 F) F) : Prop :=
  ∀ v ∈ T, ∀ i j : Fin 2,
    Valued.v (L v g i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ rad e ∧
    Valued.v (L v g⁻¹ i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ rad e

section Ultra

variable {Kv : Type*} [Field Kv] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation Kv Γ)

theorem val_mul_entry_le {P N : Matrix (Fin 2) (Fin 2) Kv} {γ : Γ}
    (hP : ∀ i j, w (P i j) ≤ 1) (hN : ∀ i j, w (N i j) ≤ γ) (i j : Fin 2) : w ((P * N) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine w.map_sum_le fun a _ => ?_
  rw [map_mul]
  calc w (P i a) * w (N a j) ≤ 1 * γ := mul_le_mul' (hP i a) (hN a j)
    _ = γ := one_mul γ

theorem val_entry_mul_le {N Q : Matrix (Fin 2) (Fin 2) Kv} {γ : Γ}
    (hN : ∀ i j, w (N i j) ≤ γ) (hQ : ∀ i j, w (Q i j) ≤ 1) (i j : Fin 2) : w ((N * Q) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine w.map_sum_le fun a _ => ?_
  rw [map_mul]
  calc w (N i a) * w (Q a j) ≤ γ * 1 := mul_le_mul' (hN i a) (hQ a j)
    _ = γ := mul_one γ

theorem val_sub_le {a b : Kv} {γ : Γ} (ha : w a ≤ γ) (hb : w b ≤ γ) : w (a - b) ≤ γ :=
  (w.map_sub a b).trans (max_le ha hb)

theorem val_add_le {a b : Kv} {γ : Γ} (ha : w a ≤ γ) (hb : w b ≤ γ) : w (a + b) ≤ γ :=
  (w.map_add a b).trans (max_le ha hb)

end Ultra

theorem IsLevel.conj {T : Finset (HeightOneSpectrum (𝓞 F))} {e : ℕ} {m k : AdelicGL2 (𝓞 F) F}
    (hm : IsLevel T e m) (hk : IsKf k) : IsLevel T e (k⁻¹ * m * k) := by
  intro v hv i j
  have hk1 : ∀ i j, Valued.v (L v k i j) ≤ 1 := fun i j => (hk.valued_le_one v i j).1
  have hk2 : ∀ i j, Valued.v (L v k⁻¹ i j) ≤ 1 := fun i j => (hk.valued_le_one v i j).2
  have key : ∀ n : AdelicGL2 (𝓞 F) F,
      (∀ i j, Valued.v (L v n i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ rad e) →
      ∀ i j, Valued.v (L v (k⁻¹ * n * k) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ rad e := by
    intro n hn i j
    have hexp : L v (k⁻¹ * n * k) - 1 = L v k⁻¹ * (L v n - 1) * L v k := by
      rw [L_mul, L_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, L_inv_mul]
    have := congrFun (congrFun hexp i) j
    rw [Matrix.sub_apply] at this
    rw [this]
    exact val_entry_mul_le Valued.v (val_mul_entry_le Valued.v hk2 (fun a b => by
      rw [Matrix.sub_apply]; exact hn a b)) hk1 i j
  refine ⟨key m (fun a b => (hm v hv a b).1) i j, ?_⟩
  have hinv : (k⁻¹ * m * k)⁻¹ = k⁻¹ * m⁻¹ * k := by group
  rw [hinv]
  exact key m⁻¹ (fun a b => (hm v hv a b).2) i j

theorem IsLevel.one (T : Finset (HeightOneSpectrum (𝓞 F))) (e : ℕ) : IsLevel T e (1 : AdelicGL2 (𝓞 F) F) := by
  intro v _ i j
  simp [L_one, inv_one]

section Upper

variable {R : Type*} [CommRing R]

def bU (α δ : Rˣ) (β : R) : GL (Fin 2) R where
  val := !![(α : R), β; 0, (δ : R)]
  inv := !![((α⁻¹ : Rˣ) : R), -(((α⁻¹ : Rˣ) : R) * β * ((δ⁻¹ : Rˣ) : R)); 0, ((δ⁻¹ : Rˣ) : R)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_assoc, Units.mul_inv_cancel_left, neg_add_cancel]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem bU_apply_00 (α δ : Rˣ) (β : R) : ((bU α δ β : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = α := rfl
@[scoped simp] theorem bU_apply_01 (α δ : Rˣ) (β : R) : ((bU α δ β : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = β := rfl
@[scoped simp] theorem bU_apply_10 (α δ : Rˣ) (β : R) : ((bU α δ β : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := rfl
@[scoped simp] theorem bU_apply_11 (α δ : Rˣ) (β : R) : ((bU α δ β : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = δ := rfl
@[scoped simp] theorem bU_inv_apply_00 (α δ : Rˣ) (β : R) :
    (((bU α δ β)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = ((α⁻¹ : Rˣ) : R) := rfl
@[scoped simp] theorem bU_inv_apply_01 (α δ : Rˣ) (β : R) :
    (((bU α δ β)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = -(((α⁻¹ : Rˣ) : R) * β * ((δ⁻¹ : Rˣ) : R)) := rfl
@[scoped simp] theorem bU_inv_apply_10 (α δ : Rˣ) (β : R) :
    (((bU α δ β)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := rfl
@[scoped simp] theorem bU_inv_apply_11 (α δ : Rˣ) (β : R) :
    (((bU α δ β)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = ((δ⁻¹ : Rˣ) : R) := rfl

theorem bU_mem_borel (α δ : Rˣ) (β : R) : bU α δ β ∈ borelSubgroup R := rfl

theorem borelDiagFst_bU (α δ : Rˣ) (β : R) :
    borelDiagFst (⟨bU α δ β, bU_mem_borel α δ β⟩ : ↥(borelSubgroup R)) = α := Units.ext rfl

theorem borelDiagSnd_bU (α δ : Rˣ) (β : R) :
    borelDiagSnd (⟨bU α δ β, bU_mem_borel α δ β⟩ : ↥(borelSubgroup R)) = δ := Units.ext rfl

theorem det_bU (α δ : Rˣ) (β : R) : Matrix.GeneralLinearGroup.det (bU α δ β) = α * δ := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

end Upper

abbrev finIdele (a : (FiniteAdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ := Units.map (finIncl (𝓞 F) F) a

def IsLevelUnit (T : Finset (HeightOneSpectrum (𝓞 F))) (e : ℕ) (a : (FiniteAdeleRing (𝓞 F) F)ˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 ∧
      Valued.v (((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1) ∧
    ∀ v ∈ T, Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v - 1) ≤ rad e

theorem IsLevelUnit.valued_inv_sub_one_le {T : Finset (HeightOneSpectrum (𝓞 F))} {e : ℕ}
    {a : (FiniteAdeleRing (𝓞 F) F)ˣ} (ha : IsLevelUnit T e a) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ T) :
    Valued.v (((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v - 1) ≤ rad e := by
  have h : ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v - 1
      = -(((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
          * ((a : FiniteAdeleRing (𝓞 F) F) v - 1)) := by
    have hu : ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v * (a : FiniteAdeleRing (𝓞 F) F) v = 1 := by
      rw [← coe_mul_apply, Units.inv_mul]; rfl
    rw [mul_sub, hu, mul_one, neg_sub]
  rw [h, Valuation.map_neg, map_mul]
  calc _ ≤ 1 * rad e := mul_le_mul' (ha.1 v).2 (ha.2 v hv)
    _ = rad e := one_mul _

theorem IsLevelUnit.mul {T : Finset (HeightOneSpectrum (𝓞 F))} {e : ℕ} {a b : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (ha : IsLevelUnit T e a) (hb : IsLevelUnit T e b) : IsLevelUnit T e (a * b) := by
  refine ⟨fun v => ⟨?_, ?_⟩, fun v hv => ?_⟩
  · rw [Units.val_mul, coe_mul_apply, map_mul]; exact mul_le_one' (ha.1 v).1 (hb.1 v).1
  · rw [mul_inv_rev, Units.val_mul, coe_mul_apply, map_mul]; exact mul_le_one' (hb.1 v).2 (ha.1 v).2
  · have h : ((a * b : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v - 1
        = (a : FiniteAdeleRing (𝓞 F) F) v * ((b : FiniteAdeleRing (𝓞 F) F) v - 1)
          + ((a : FiniteAdeleRing (𝓞 F) F) v - 1) := by
      rw [Units.val_mul, coe_mul_apply]; ring
    rw [h]
    refine val_add_le _ ?_ (ha.2 v hv)
    rw [map_mul]
    calc _ ≤ 1 * rad e := mul_le_mul' (ha.1 v).1 (hb.2 v hv)
      _ = rad e := one_mul _

theorem isLevelUnit_localUnit {T : Finset (HeightOneSpectrum (𝓞 F))} {e : ℕ} (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ) (ht : Valued.v (t : v.adicCompletion F) ≤ 1)
    (ht' : Valued.v ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1)
    (hlev : v ∈ T → Valued.v ((t : v.adicCompletion F) - 1) ≤ rad e) :
    IsLevelUnit T e (localUnit (𝓞 F) F v t) := by
  classical
  refine ⟨fun w => ⟨?_, ?_⟩, fun w hw => ?_⟩
  · by_cases h : w = v
    · subst h; rw [localUnit_apply_self]; exact ht
    · rw [localUnit_apply_of_ne (𝓞 F) F v t h, map_one]
  · by_cases h : w = v
    · subst h; rw [← map_inv, localUnit_apply_self]; exact ht'
    · rw [← map_inv, localUnit_apply_of_ne (𝓞 F) F v t⁻¹ h, map_one]
  · by_cases h : w = v
    · subst h; rw [localUnit_apply_self]; exact hlev hw
    · rw [localUnit_apply_of_ne (𝓞 F) F v t h, sub_self, map_zero]; exact zero_le'

theorem isKf_bU (α δ : (AdeleRing (𝓞 F) F)ˣ) (β : AdeleRing (𝓞 F) F)
    (hα1 : (α : AdeleRing (𝓞 F) F).1 = 1) (hδ1 : (δ : AdeleRing (𝓞 F) F).1 = 1) (hβ : β.1 = 0)
    (hA : ∀ v, Valued.v ((α : AdeleRing (𝓞 F) F).2 v) ≤ 1 ∧
      Valued.v (((α⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ 1)
    (hD : ∀ v, Valued.v ((δ : AdeleRing (𝓞 F) F).2 v) ≤ 1 ∧
      Valued.v (((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ 1)
    (hβi : ∀ v, Valued.v (β.2 v) ≤ 1) :
    IsKf (bU α δ β) := by
  have hint : ∀ (x : FiniteAdeleRing (𝓞 F) F), (∀ v, Valued.v (x v) ≤ 1) → x ∈ integralFiniteAdeles (𝓞 F) F :=
    fun x hx v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hx v)
  refine isKf_of _ (mem_finiteIntegralGL2_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩) ?_
  · rw [glFin_apply]
    fin_cases i <;> fin_cases j
    · exact hint _ fun v => (hA v).1
    · exact hint _ hβi
    · simp; exact zero_mem_integralFiniteAdeles
    · exact hint _ fun v => (hD v).1
  · rw [← map_inv, glFin_apply]
    fin_cases i <;> fin_cases j
    · exact hint _ fun v => (hA v).2
    · show (-(((α⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * β
        * ((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))).2 ∈ _
      refine hint _ fun v => ?_
      have hneg : ∀ (p : AdeleRing (𝓞 F) F), (-p).2 v = -(p.2 v) := fun p => rfl
      have hmul : ∀ (p q : AdeleRing (𝓞 F) F), (p * q).2 v = p.2 v * q.2 v := fun p q => rfl
      rw [hneg, Valuation.map_neg, hmul, hmul, map_mul, map_mul]
      exact mul_le_one' (mul_le_one' (hA v).2 (hβi v)) (hD v).2
    · simp; exact zero_mem_integralFiniteAdeles
    · exact hint _ fun v => (hD v).2
  · ext i j
    rw [glArch_apply]
    fin_cases i <;> fin_cases j
    · exact hα1
    · exact hβ
    · rfl
    · exact hδ1

theorem finIdele_fst (A : (FiniteAdeleRing (𝓞 F) F)ˣ) : ((finIdele A : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 :=
  rfl

theorem finIdele_snd (A : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((finIdele A : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = (A : FiniteAdeleRing (𝓞 F) F) := rfl

theorem finIdele_inv (A : (FiniteAdeleRing (𝓞 F) F)ˣ) : (finIdele A)⁻¹ = finIdele A⁻¹ := (map_inv _ _).symm

theorem isKf_bU_fin (A D : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hA : ∀ v, Valued.v ((A : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 ∧
      Valued.v (((A⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1)
    (hD : ∀ v, Valued.v ((D : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 ∧
      Valued.v (((D⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1) :
    IsKf (bU (finIdele A) (finIdele D) (0 : AdeleRing (𝓞 F) F)) :=
  isKf_bU _ _ _ rfl rfl rfl (fun v => by rw [finIdele_inv]; exact hA v) (fun v => by rw [finIdele_inv]; exact hD v)
    (fun v => by show Valued.v ((0 : FiniteAdeleRing (𝓞 F) F) v) ≤ 1; rw [coe_zero_apply, map_zero]; exact zero_le')

theorem L_bU (v : HeightOneSpectrum (𝓞 F)) (A D : (AdeleRing (𝓞 F) F)ˣ) (β : AdeleRing (𝓞 F) F) (i j : Fin 2) :
    L v (bU A D β) i j = !![(A : AdeleRing (𝓞 F) F).2 v, β.2 v; 0, (D : AdeleRing (𝓞 F) F).2 v] i j := by
  rw [L_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem isLevel_bU {T : Finset (HeightOneSpectrum (𝓞 F))} {e : ℕ} (A D : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hA : IsLevelUnit T e A) (hD : IsLevelUnit T e D) :
    IsLevel T e (bU (finIdele A) (finIdele D) 0) := by
  intro v hv i j
  have hinv : (bU (finIdele A) (finIdele D) (0 : AdeleRing (𝓞 F) F))⁻¹ = bU (finIdele A⁻¹) (finIdele D⁻¹) 0 := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bU, Matrix.mul_apply, Fin.sum_univ_two, ← Units.val_mul, ← map_mul]
  rw [hinv]
  constructor
  · rw [L_bU]
    fin_cases i <;> fin_cases j
    · have h__af := hA.2 v hv
      simp at h__af
      exact h__af
    · show Valued.v ((0 : FiniteAdeleRing (𝓞 F) F) v - 0) ≤ rad e
      rw [sub_zero, coe_zero_apply, map_zero]; exact zero_le'
    · simp
    · have h__af := hD.2 v hv
      simp at h__af
      exact h__af
  · rw [L_bU]
    fin_cases i <;> fin_cases j
    · have h__af := hA.valued_inv_sub_one_le v hv
      simp at h__af
      exact h__af
    · show Valued.v ((0 : FiniteAdeleRing (𝓞 F) F) v - 0) ≤ rad e
      rw [sub_zero, coe_zero_apply, map_zero]; exact zero_le'
    · simp
    · have h__af := hD.valued_inv_sub_one_le v hv
      simp at h__af
      exact h__af

theorem isLevelUnit_one (T : Finset (HeightOneSpectrum (𝓞 F))) (e : ℕ) : IsLevelUnit T e (1 : (FiniteAdeleRing (𝓞 F) F)ˣ) := by
  refine ⟨fun v => ⟨?_, ?_⟩, fun v _ => ?_⟩
  · rw [Units.val_one, coe_one_apply, map_one]
  · rw [inv_one, Units.val_one, coe_one_apply, map_one]
  · rw [Units.val_one, coe_one_apply, sub_self, map_zero]; exact zero_le'

open FLT.SmoothVectors in

theorem exists_level_rightInvariant (n : ℕ) (U : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hU : ∀ i, IsKfSmooth F (U i)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (e : ℕ), 1 ≤ e ∧
      ∀ i (g : AdelicGL2 (𝓞 F) F), IsKf g → IsLevel T e g → ∀ x, U i (x * g) = U i x := by
  classical
  set Γ : Subgroup (AdelicGL2 (𝓞 F) F) := finiteAdelicGL2Subgroup F with hΓ
  obtain ⟨V, hVo, hV⟩ := exists_isOpen_subgroup_forall_smul_eq (G := ↥Γ) Finset.univ
    (fun i => (RightTranslationFn.mk (U i) : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) (fun i _ => hU i)
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.1 hVo
  have h1 : O ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F) := hO.mem_nhds (by
    have : (1 : ↥Γ) ∈ (V : Set ↥Γ) := V.one_mem
    rw [← hOV] at this; exact this)
  obtain ⟨T, e, hTe⟩ := NumberField.AdelicLevel.exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one F O h1
  refine ⟨T, e + 1, Nat.le_add_left 1 e, fun i g hg hlev x => ?_⟩
  have hgΓ : g ∈ Γ := (mem_finiteAdelicGL2Subgroup_iff F g).2 hg.2
  have hrad : rad (e + 1) ≤ rad e := by
    rw [rad, rad, WithZero.exp_le_exp]; push_cast; omega
  have hgO : g ∈ O := hTe g hg.2 (fun v i j => hg.mem_integers v i j)
    (fun v hv i j => ⟨((hlev v hv i j).1).trans hrad, ((hlev v hv i j).2).trans hrad⟩)
  have hgV : (⟨g, hgΓ⟩ : ↥Γ) ∈ V := by
    have : (⟨g, hgΓ⟩ : ↥Γ) ∈ Subtype.val ⁻¹' O := hgO
    rw [hOV] at this; exact this
  have := hV i (Finset.mem_univ i) ⟨g, hgΓ⟩ hgV
  have h' := congrArg (fun f => RightTranslationFn.toFun f x) this
  simpa [Subgroup.smul_def, RightTranslationFn.toFun_smul] using h'

theorem chars_eq_one_of_ne_zero {n : ℕ} (U : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (e : ℕ)
    (hinv : ∀ i (g : AdelicGL2 (𝓞 F) F), IsKf g → IsLevel T e g → ∀ x, U i (x * g) = U i x)
    (hUB : ∀ (i : Fin n) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glArch (𝓞 F) F b = 1 → glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U i (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U i g)
    (i₀ : Fin n) (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : IsKf g₀) (hne : U i₀ g₀ ≠ 0)
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (ha : IsLevelUnit T e a) :
    μ (finIdele a) = 1 ∧ ν (finIdele a) = 1 := by
  have key : ∀ D : (FiniteAdeleRing (𝓞 F) F)ˣ, IsLevelUnit T e D →
      ((μ (finIdele a) : ℂˣ) : ℂ) * ((ν (finIdele D) : ℂˣ) : ℂ) = 1 := by
    intro D hD
    set b : AdelicGL2 (𝓞 F) F := bU (finIdele a) (finIdele D) 0 with hb_def
    have hbK : IsKf b := isKf_bU_fin a D ha.1 hD.1
    have hbL : IsLevel T e b := isLevel_bU a D ha hD
    have h1 := hUB i₀ b (bU_mem_borel _ _ _) hbK.2 hbK.1.1 g₀
    rw [borelDiagFst_bU, borelDiagSnd_bU] at h1
    have h2 : U i₀ (b * g₀) = U i₀ g₀ := by
      have : b * g₀ = g₀ * (g₀⁻¹ * b * g₀) := by group
      rw [this]
      exact hinv i₀ _ ((hg₀.inv.mul hbK).mul hg₀) (hbL.conj hg₀) g₀
    rw [h2] at h1
    exact (mul_eq_right₀ hne).1 h1.symm
  have hμ : μ (finIdele a) = 1 := by
    have h := key 1 (isLevelUnit_one T e)
    have h1 : finIdele (1 : (FiniteAdeleRing (𝓞 F) F)ˣ) = 1 := map_one _
    rw [h1, map_one, Units.val_one, mul_one] at h
    exact Units.val_eq_one.1 h
  refine ⟨hμ, ?_⟩
  have h := key a ha
  rw [hμ, Units.val_one, one_mul] at h
  exact Units.val_eq_one.1 h

theorem isLevel_of_forward {T : Finset (HeightOneSpectrum (𝓞 F))} {e : ℕ} {g : AdelicGL2 (𝓞 F) F} (hg : IsKf g)
    (h : ∀ v ∈ T, ∀ i j : Fin 2, Valued.v (L v g i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ rad e) :
    IsLevel T e g := by
  intro v hv i j
  refine ⟨h v hv i j, ?_⟩
  have hexp : L v g⁻¹ - 1 = -(L v g⁻¹ * (L v g - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, L_inv_mul, neg_sub]
  have := congrFun (congrFun hexp i) j
  rw [Matrix.sub_apply] at this
  rw [this, Matrix.neg_apply, Valuation.map_neg]
  exact val_mul_entry_le Valued.v (fun a b => (hg.valued_le_one v a b).2) (fun a b => by
    rw [Matrix.sub_apply]; exact h v hv a b) i j

structure Ctx (F : Type) [Field F] [NumberField F] (n : ℕ) where
  U : Fin n → AdelicGL2 (𝓞 F) F → ℂ
  μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ
  ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ
  T : Finset (HeightOneSpectrum (𝓞 F))
  e : ℕ
  he : 1 ≤ e
  hinv : ∀ i (g : AdelicGL2 (𝓞 F) F), IsKf g → IsLevel T e g → ∀ x, U i (x * g) = U i x
  hUB : ∀ (i : Fin n) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
    glArch (𝓞 F) F b = 1 → glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F →
    ∀ g : AdelicGL2 (𝓞 F) F,
      U i (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U i g
  hchar : ∀ a : (FiniteAdeleRing (𝓞 F) F)ˣ, IsLevelUnit T e a → μ (finIdele a) = 1 ∧ ν (finIdele a) = 1

namespace Ctx

variable {n : ℕ} (C : Ctx F n)

abbrev χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := C.μ * C.ν⁻¹

def W (i : Fin n) (k : AdelicGL2 (𝓞 F) F) : ℂ :=
  (((C.μ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) * C.U i k

theorem U_eq_mul_W (i : Fin n) (k : AdelicGL2 (𝓞 F) F) :
    C.U i k = ((C.μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * C.W i k := by
  rw [W, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem chi_finIdele_eq_one {a : (FiniteAdeleRing (𝓞 F) F)ˣ} (ha : IsLevelUnit C.T C.e a) : C.χ (finIdele a) = 1 := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, (C.hchar a ha).1, (C.hchar a ha).2, inv_one, mul_one]

theorem W_diag_mul (i : Fin n) (D : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hD : ∀ v, Valued.v ((D : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 ∧
      Valued.v (((D⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1)
    (k : AdelicGL2 (𝓞 F) F) :
    C.W i (bU (finIdele 1) (finIdele D) (0 : AdeleRing (𝓞 F) F) * k)
      = (((C.χ (finIdele D))⁻¹ : ℂˣ) : ℂ) * C.W i k := by
  set b : AdelicGL2 (𝓞 F) F := bU (finIdele 1) (finIdele D) (0 : AdeleRing (𝓞 F) F) with hb
  have hbK : IsKf b := isKf_bU_fin 1 D (isLevelUnit_one ∅ 0).1 hD
  have h1 := C.hUB i b (bU_mem_borel _ _ _) hbK.2 hbK.1.1 k
  rw [borelDiagFst_bU, borelDiagSnd_bU] at h1
  have h1' : finIdele (1 : (FiniteAdeleRing (𝓞 F) F)ˣ) = 1 := map_one _
  rw [W, h1, map_mul, det_bU, h1', one_mul, map_mul, map_one, Units.val_one, one_mul, W, MonoidHom.mul_apply,
    MonoidHom.inv_apply]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv]
  ring

theorem L_diag_mul_row (D : (FiniteAdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F))
    (j : Fin 2) :
    L v (bU (finIdele 1) (finIdele D) (0 : AdeleRing (𝓞 F) F) * k) 1 j = (D : FiniteAdeleRing (𝓞 F) F) v * L v k 1 j := by
  rw [L_mul, Matrix.mul_apply, Fin.sum_univ_two, L_bU, L_bU]
  show (0 : FiniteAdeleRing (𝓞 F) F) v * L v k 0 j + (D : FiniteAdeleRing (𝓞 F) F) v * L v k 1 j = _
  rw [coe_zero_apply, zero_mul, zero_add]

theorem det_fst_eq_one {g : AdelicGL2 (𝓞 F) F} (hg : glArch (𝓞 F) F g = 1) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  have h : ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
      = (glArch (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    have : (glArch (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = (adeleArch (𝓞 F) F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
      ext i j; rfl
    rw [this, ← RingHom.map_det]; rfl
  rw [h, hg, Units.val_one, Matrix.det_one]

theorem det_snd_apply (g : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = (L v g).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have : L v g = ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    ext i j; rfl
  rw [this, ← RingHom.map_det]; rfl

theorem W_eq_of_rowCong (i : Fin n) {k k' : AdelicGL2 (𝓞 F) F} (hk : IsKf k) (hk' : IsKf k')
    (h : ∀ v ∈ C.T, ∀ j : Fin 2, Valued.v (L v k' 1 j - L v k 1 j) ≤ rad C.e) :
    C.W i k' = C.W i k := by
  set g : AdelicGL2 (𝓞 F) F := k' * k⁻¹ with hg_def
  have hg : IsKf g := hk'.mul hk.inv
  have hk'g : k' = g * k := by rw [hg_def, inv_mul_cancel_right]

  have hrow : ∀ v ∈ C.T, ∀ j : Fin 2,
      Valued.v (L v g 1 j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 j) ≤ rad C.e := by
    intro v hv j
    have hexp : L v g - 1 = (L v k' - L v k) * L v k⁻¹ := by
      rw [hg_def, L_mul, Matrix.sub_mul, L_mul_inv]
    have := congrFun (congrFun hexp 1) j
    rw [Matrix.sub_apply] at this
    rw [this, Matrix.mul_apply]
    refine Valued.v.map_sum_le fun l _ => ?_
    rw [map_mul, Matrix.sub_apply]
    calc _ ≤ rad C.e * 1 := mul_le_mul' (h v hv l) (hk.valued_le_one v l j).2
      _ = rad C.e := mul_one _

  set δ : (AdeleRing (𝓞 F) F)ˣ := Matrix.GeneralLinearGroup.det g with hδ
  set β : AdeleRing (𝓞 F) F := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 with hβ
  set b : AdelicGL2 (𝓞 F) F := bU δ 1 β with hb
  have hδv : ∀ v, Valued.v ((δ : AdeleRing (𝓞 F) F).2 v) = 1 := fun v => by
    rw [hδ, det_snd_apply]; exact valued_det_finComponent_eq_one hg.1 v
  have hδv' : ∀ v, Valued.v (((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = 1 := fun v => by
    rw [hδ, ← map_inv, det_snd_apply]; exact valued_det_finComponent_eq_one hg.inv.1 v
  have hbK : IsKf b := by
    refine isKf_bU δ 1 β (det_fst_eq_one hg.2) rfl ?_ (fun v => ⟨(hδv v).le, (hδv' v).le⟩)
      (fun v => ⟨by rw [Units.val_one]; exact (map_one _).le, by rw [inv_one, Units.val_one]; exact (map_one _).le⟩)
      (fun v => (hg.valued_le_one v 0 1).1)
    rw [hβ, ← glArch_apply, hg.2]; rfl

  set k'' : AdelicGL2 (𝓞 F) F := b⁻¹ * g with hk''
  have hk''K : IsKf k'' := hbK.inv.mul hg
  have hlev : IsLevel C.T C.e k'' := by
    refine isLevel_of_forward hk''K fun v hv i j => ?_

    set a := L v g 0 0 with ha
    set b' := L v g 0 1 with hb'
    set c := L v g 1 0 with hc
    set d := L v g 1 1 with hd
    set D := (δ : AdeleRing (𝓞 F) F).2 v with hD
    have hDdet : D = a * d - b' * c := by rw [hD, hδ, det_snd_apply, Matrix.det_fin_two]
    have hD0 : D ≠ 0 := fun h0 => by have := hδv v; rw [← hD, h0, map_zero] at this; exact zero_ne_one this
    have hDinv : ((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = D⁻¹ := by
      have : ((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * D = 1 := by
        rw [hD, show ((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * (δ : AdeleRing (𝓞 F) F).2 v
          = ((((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (δ : AdeleRing (𝓞 F) F)).2 v) from rfl,
          Units.inv_mul]; rfl
      exact eq_inv_of_mul_eq_one_left this
    have hc_le : Valued.v c ≤ rad C.e := by have := hrow v hv 0; rwa [Matrix.one_apply_ne (by decide), sub_zero] at this
    have hd_le : Valued.v (d - 1) ≤ rad C.e := by have := hrow v hv 1; rwa [Matrix.one_apply_eq] at this
    have hd_le' : Valued.v (1 - d) ≤ rad C.e := by rw [← neg_sub, Valuation.map_neg]; exact hd_le
    have ha_le : Valued.v a ≤ 1 := (hg.valued_le_one v 0 0).1
    have hb_le : Valued.v b' ≤ 1 := (hg.valued_le_one v 0 1).1
    have hDi : Valued.v D⁻¹ = 1 := by rw [map_inv₀, hD, hδv v, inv_one]

    have hLb : ∀ i j, L v b⁻¹ i j = !![D⁻¹, -(D⁻¹ * b'); 0, 1] i j := by
      intro i j
      rw [L_apply, hb]
      fin_cases i <;> fin_cases j
      · exact hDinv
      · show (-(((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * β * (((1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ :
            (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))).2 v = -(D⁻¹ * b')
        rw [inv_one, Units.val_one, mul_one]
        show -((((δ⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v * β.2 v) = _
        rw [hDinv]; rfl
      · rfl
      · show (((1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1
        rw [inv_one]; rfl
    have hLk'' : ∀ i j, L v k'' i j = (!![D⁻¹, -(D⁻¹ * b'); 0, 1] * !![a, b'; c, d]) i j := by
      intro i j
      rw [hk'', L_mul, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hLb]
      congr 1
      fin_cases l <;> fin_cases j <;> rfl
    set M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) := !![D⁻¹, -(D⁻¹ * b'); 0, 1] * !![a, b'; c, d] with hM
    have e00 : Valued.v (M 0 0 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0) ≤ rad C.e := by
      have : M 0 0 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 = D⁻¹ * a * (1 - d) := by
        simp [hM]
        rw [hDdet]
        have hne : a * d - b' * c ≠ 0 := hDdet ▸ hD0
        field_simp
        ring
      rw [this, map_mul, map_mul, hDi, one_mul]
      calc _ ≤ 1 * rad C.e := mul_le_mul' ha_le hd_le'
        _ = _ := one_mul _
    have e01 : Valued.v (M 0 1 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1) ≤ rad C.e := by
      have : M 0 1 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 = D⁻¹ * b' * (1 - d) := by
        simp [hM]; ring
      rw [this, map_mul, map_mul, hDi, one_mul]
      calc _ ≤ 1 * rad C.e := mul_le_mul' hb_le hd_le'
        _ = _ := one_mul _
    have e10 : Valued.v (M 1 0 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ≤ rad C.e := by
      have : M 1 0 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = c := by
        simp [hM]
      rw [this]; exact hc_le
    have e11 : Valued.v (M 1 1 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) ≤ rad C.e := by
      have : M 1 1 - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = d - 1 := by
        simp [hM]
      rw [this]; exact hd_le
    rw [hLk'']
    fin_cases i <;> fin_cases j
    exacts [e00, e01, e10, e11]

  have hgk : g * k = b * (k * (k⁻¹ * k'' * k)) := by
    rw [hk'']; group
  have hU : C.U i k' = ((C.μ δ : ℂˣ) : ℂ) * C.U i k := by
    rw [hk'g, hgk, C.hUB i b (bU_mem_borel _ _ _) hbK.2 hbK.1.1, borelDiagFst_bU, borelDiagSnd_bU, map_one,
      Units.val_one, mul_one, C.hinv i _ ((hk.inv.mul hk''K).mul hk) (hlev.conj hk) k]
  rw [W, W, hU, hk'g, map_mul, ← hδ, map_mul, mul_inv_rev, Units.val_mul, mul_assoc, ← mul_assoc _ ((C.μ δ : ℂˣ) : ℂ),
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

def Rel (v : HeightOneSpectrum (𝓞 F)) (x y : AdelicGL2 (𝓞 F) F) : Prop :=
  ∃ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 ∧
    ∀ j : Fin 2, Valued.v ((u : v.adicCompletion F) * L v x 1 j - L v y 1 j) ≤ rad C.e

theorem rel_refl (v : HeightOneSpectrum (𝓞 F)) (x : AdelicGL2 (𝓞 F) F) : C.Rel v x x :=
  ⟨1, by simp, fun j => by rw [Units.val_one, one_mul, sub_self, map_zero]; exact zero_le'⟩

theorem rel_symm {v : HeightOneSpectrum (𝓞 F)} {x y : AdelicGL2 (𝓞 F) F} (h : C.Rel v x y) : C.Rel v y x := by
  obtain ⟨u, hu, hj⟩ := h
  refine ⟨u⁻¹, by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one], fun j => ?_⟩
  have : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * L v y 1 j - L v x 1 j
      = -(((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ((u : v.adicCompletion F) * L v x 1 j - L v y 1 j)) := by
    rw [mul_sub, ← mul_assoc, Units.inv_mul, one_mul, neg_sub]
  rw [this, Valuation.map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_mul]
  exact hj j

theorem rel_trans {v : HeightOneSpectrum (𝓞 F)} {x y w : AdelicGL2 (𝓞 F) F} (h1 : C.Rel v x y) (h2 : C.Rel v y w) :
    C.Rel v x w := by
  obtain ⟨u, hu, hj⟩ := h1
  obtain ⟨u', hu', hj'⟩ := h2
  refine ⟨u' * u, by rw [Units.val_mul, map_mul, hu, hu', one_mul], fun j => ?_⟩
  have : ((u' * u : (v.adicCompletion F)ˣ) : v.adicCompletion F) * L v x 1 j - L v w 1 j
      = (u' : v.adicCompletion F) * ((u : v.adicCompletion F) * L v x 1 j - L v y 1 j)
        + ((u' : v.adicCompletion F) * L v y 1 j - L v w 1 j) := by
    rw [Units.val_mul]; ring
  rw [this]
  refine val_add_le _ ?_ (hj' j)
  rw [map_mul, hu', one_mul]; exact hj j

def RelT (x y : AdelicGL2 (𝓞 F) F) : Prop := ∀ v ∈ C.T, C.Rel v x y

theorem relT_refl (x : AdelicGL2 (𝓞 F) F) : C.RelT x x := fun v _ => C.rel_refl v x
theorem relT_symm {x y : AdelicGL2 (𝓞 F) F} (h : C.RelT x y) : C.RelT y x := fun v hv => C.rel_symm (h v hv)
theorem relT_trans {x y w : AdelicGL2 (𝓞 F) F} (h1 : C.RelT x y) (h2 : C.RelT y w) : C.RelT x w :=
  fun v hv => C.rel_trans (h1 v hv) (h2 v hv)

theorem continuous_L_apply (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => L v g i j :=
  (Continuous.matrix_elem (Units.continuous_val.comp ((continuous_finComponent (𝓞 F) F v).comp
    (continuous_glFin (𝓞 F) F))) i j)

theorem isOpen_ball (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (e : ℕ) :
    IsOpen {z : v.adicCompletion F | Valued.v (z - c) ≤ rad e} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := F) v e
  have : {z : v.adicCompletion F | Valued.v (z - c) ≤ rad e}
      = (fun z => z - c) ⁻¹' {y : v.adicCompletion F | Valued.v y ≤ Valued.v t} := by
    ext z; simp [rad, hvt]
  rw [this]
  exact (isOpen_setOf_valued_le v t ht).preimage (continuous_id.sub continuous_const)

theorem isClosed_ball (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (e : ℕ) :
    IsClosed {z : v.adicCompletion F | Valued.v (z - c) ≤ rad e} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := F) v e
  have : {z : v.adicCompletion F | Valued.v (z - c) ≤ rad e}
      = (fun z => z - c) ⁻¹' {y : v.adicCompletion F | Valued.v y ≤ Valued.v t} := by
    ext z; simp [rad, hvt]
  rw [this]
  exact (isClosed_setOf_valued_le v t ht).preimage (continuous_id.sub continuous_const)

theorem exists_cover :
    ∃ (ι : Type) (_ : Fintype ι) (rep : ι → AdelicGL2 (𝓞 F) F), (∀ r, IsKf (rep r)) ∧
      ∀ k, IsKf k → ∃ r, ∀ v ∈ C.T, ∀ j : Fin 2, Valued.v (L v k 1 j - L v (rep r) 1 j) ≤ rad C.e := by
  classical
  set Kf : Set (AdelicGL2 (𝓞 F) F) := {k | IsKf k} with hKf
  have hKfc : IsCompact Kf := by
    have : Kf = (maximalCompactAway F ∅ : Set (AdelicGL2 (𝓞 F) F)) := by
      ext k
      simp only [hKf, Set.mem_setOf_eq, SetLike.mem_coe, mem_maximalCompactAway_iff, Finset.notMem_empty,
        false_imp_iff, imp_true_iff, and_true]
      rfl
    rw [this]; exact isCompact_maximalCompactAway F ∅
  let O : ↥Kf → Set (AdelicGL2 (𝓞 F) F) := fun k₀ =>
    {g | ∀ v ∈ C.T, ∀ j : Fin 2, Valued.v (L v g 1 j - L v (k₀ : AdelicGL2 (𝓞 F) F) 1 j) ≤ rad C.e}
  have hO : ∀ k₀, IsOpen (O k₀) := by
    intro k₀
    have : O k₀ = ⋂ v ∈ C.T, ⋂ j : Fin 2,
        (fun g => L v g 1 j) ⁻¹' {z | Valued.v (z - L v (k₀ : AdelicGL2 (𝓞 F) F) 1 j) ≤ rad C.e} := by
      ext g; simp [O]
    rw [this]
    exact isOpen_biInter_finset fun v _ => isOpen_iInter_of_finite fun j =>
      (isOpen_ball v _ C.e).preimage (continuous_L_apply v 1 j)
  have hcov : Kf ⊆ ⋃ k₀, O k₀ := fun k hk =>
    Set.mem_iUnion.2 ⟨⟨k, hk⟩, fun v _ j => by rw [sub_self, map_zero]; exact zero_le'⟩
  obtain ⟨t, ht⟩ := hKfc.elim_finite_subcover O hO hcov
  refine ⟨↥t, inferInstance, fun r => ((r : ↥Kf) : AdelicGL2 (𝓞 F) F), fun r => (r : ↥Kf).2, fun k hk => ?_⟩
  have := ht hk
  simp only [Set.mem_iUnion] at this
  obtain ⟨k₀, hk₀, hmem⟩ := this
  exact ⟨⟨k₀, hk₀⟩, hmem⟩

theorem sum_inv_mult_eq_one {ι : Type} [Fintype ι] (rep : ι → AdelicGL2 (𝓞 F) F)
    [∀ k, DecidablePred fun r : ι => C.RelT (rep r) k]
    (k : AdelicGL2 (𝓞 F) F) (hk : ∃ r, C.RelT (rep r) k) :
    (∑ r, if C.RelT (rep r) k then
        (((Finset.univ.filter fun r' : ι => C.RelT (rep r') (rep r)).card : ℂ))⁻¹ else 0) = 1 := by
  set A : Finset ι := Finset.univ.filter fun r : ι => C.RelT (rep r) k with hA
  have hAne : A.card ≠ 0 := by
    obtain ⟨r, hr⟩ := hk
    exact Finset.card_ne_zero.2 ⟨r, Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩⟩
  have hcard : ∀ r ∈ A, (Finset.univ.filter fun r' : ι => C.RelT (rep r') (rep r)).card = A.card := by
    intro r hr
    have hr' : C.RelT (rep r) k := (Finset.mem_filter.1 hr).2
    congr 1
    ext r'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
    exact ⟨fun h => C.relT_trans h hr', fun h => C.relT_trans h (C.relT_symm hr')⟩
  rw [← Finset.sum_filter]
  rw [Finset.sum_congr rfl fun r hr => by rw [hcard r hr]]
  rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀]
  exact_mod_cast hAne

section LocalZeta

open LanglandsTunnell.TateLocal

variable (v : HeightOneSpectrum (𝓞 F))

def ball : Set (v.adicCompletion F) := {y | Valued.v y ≤ rad C.e}

open scoped Classical in

def Φloc [MeasurableSpace (v.adicCompletion F)] (μv : Measure (v.adicCompletion F)) (a : ℂ)
    (c y : Fin 2 → v.adicCompletion F) : ℂ :=
  if ∀ j, Valued.v (y j - c j) ≤ rad C.e then a * (((μv.real (C.ball v))⁻¹ : ℝ) : ℂ) else 0

variable {v}

theorem valued_eq_one_of_cong {c x : Fin 2 → v.adicCompletion F} (hc : ∀ j, Valued.v (c j) ≤ 1)
    (hc1 : ∃ j, Valued.v (c j) = 1) (hx : ∀ j, Valued.v (x j) ≤ 1) (hx1 : ∃ j, Valued.v (x j) = 1)
    {t : v.adicCompletion F} (ht : ∀ j, Valued.v (t * x j - c j) ≤ rad C.e) : Valued.v t = 1 := by
  have hlt : rad C.e < 1 := rad_lt_one C.he
  obtain ⟨j₀, hj₀⟩ := hc1
  obtain ⟨j₁, hj₁⟩ := hx1
  have h1 : Valued.v (t * x j₀) = 1 := by
    rw [← hj₀]; exact Valuation.map_eq_of_sub_lt _ (by rw [hj₀]; exact (ht j₀).trans_lt hlt)
  refine le_antisymm ?_ ?_
  · have h2 : Valued.v (t * x j₁) ≤ 1 := by
      have : t * x j₁ = (t * x j₁ - c j₁) + c j₁ := by ring
      rw [this]
      exact val_add_le _ ((ht j₁).trans (rad_le_one _)) (hc j₁)
    rw [map_mul, hj₁, mul_one] at h2; exact h2
  · rw [map_mul] at h1
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v t * Valued.v (x j₀) := h1.symm
      _ ≤ Valued.v t * 1 := mul_le_mul' le_rfl (hx j₀)
      _ = Valued.v t := mul_one _

theorem cong_iff_sub_le {c x : Fin 2 → v.adicCompletion F} (hx : ∀ j, Valued.v (x j) ≤ 1)
    (hx1 : ∃ j, Valued.v (x j) = 1) {t₀ : v.adicCompletion F}
    (ht₀ : ∀ j, Valued.v (t₀ * x j - c j) ≤ rad C.e) (t : v.adicCompletion F) :
    (∀ j, Valued.v (t * x j - c j) ≤ rad C.e) ↔ Valued.v (t - t₀) ≤ rad C.e := by
  constructor
  · intro ht
    obtain ⟨j₁, hj₁⟩ := hx1
    have : t - t₀ = ((t * x j₁ - c j₁) - (t₀ * x j₁ - c j₁)) * (x j₁)⁻¹ := by
      have hx0 : x j₁ ≠ 0 := fun h => by rw [h, map_zero] at hj₁; exact zero_ne_one hj₁
      field_simp
      ring
    rw [this, map_mul, map_inv₀, hj₁, inv_one, mul_one]
    exact val_sub_le _ (ht j₁) (ht₀ j₁)
  · intro ht j
    have : t * x j - c j = (t - t₀) * x j + (t₀ * x j - c j) := by ring
    rw [this]
    refine val_add_le _ ?_ (ht₀ j)
    rw [map_mul]
    calc _ ≤ rad C.e * 1 := mul_le_mul' ht (hx j)
      _ = _ := mul_one _

theorem localChar_eq_of_sub_le {t₀ : (v.adicCompletion F)ˣ}
    (ht₀ : Valued.v (t₀ : v.adicCompletion F) = 1) {t : v.adicCompletion F} (ht1 : Valued.v t = 1)
    (hnear : Valued.v (t - t₀) ≤ rad C.e) (ht0 : t ≠ 0) :
    localChar C.χ v (Units.mk0 t ht0) = localChar C.χ v t₀ := by
  set u : (v.adicCompletion F)ˣ := Units.mk0 t ht0 * t₀⁻¹ with hu
  have hu1 : Valued.v (u : v.adicCompletion F) = 1 := by
    rw [hu, Units.val_mul, map_mul, Units.val_mk0, ht1, Units.val_inv_eq_inv_val, map_inv₀, ht₀, inv_one, mul_one]
  have hu2 : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]
  have hu3 : Valued.v ((u : v.adicCompletion F) - 1) ≤ rad C.e := by
    have : (u : v.adicCompletion F) - 1 = (t - t₀) * (t₀ : v.adicCompletion F)⁻¹ := by
      rw [hu, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ t₀.ne_zero]
    rw [this, map_mul, map_inv₀, ht₀, inv_one, mul_one]; exact hnear
  have hlev : IsLevelUnit C.T C.e (localUnit (𝓞 F) F v u) :=
    isLevelUnit_localUnit v u hu1.le hu2.le (fun _ => hu3)
  have hχ : localChar C.χ v u = 1 := C.chi_finIdele_eq_one hlev
  have : Units.mk0 t ht0 = u * t₀ := by rw [hu, inv_mul_cancel_right]
  rw [this, map_mul, hχ, one_mul]

variable (v) in

theorem ball_measure_ne [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure] : μv (C.ball v) ≠ 0 ∧ μv (C.ball v) ≠ ⊤ := by
  constructor
  · have hopen : IsOpen (C.ball v) := by
      have := isOpen_ball v (0 : v.adicCompletion F) C.e
      simpa [ball] using this
    exact (hopen.measure_pos μv ⟨0, by simp [ball]⟩).ne'
  · have hsub : C.ball v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun y hy =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_trans hy (rad_le_one _))
    have hK : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
    exact ((hK.of_isClosed_subset (by
      have := isClosed_ball v (0 : v.adicCompletion F) C.e
      simpa [ball] using this) hsub).measure_lt_top).ne

theorem measure_near_eq [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure] (t₀ : v.adicCompletion F) :
    μv {t | Valued.v (t - t₀) ≤ rad C.e} = μv (C.ball v) := by
  have : {t : v.adicCompletion F | Valued.v (t - t₀) ≤ rad C.e} = (fun h => -t₀ + h) ⁻¹' C.ball v := by
    ext t; simp [ball, neg_add_eq_sub]
  rw [this, measure_preimage_add]

theorem modulus_eq_one_of_valued {t : v.adicCompletion F} (ht : Valued.v t = 1) : modulus t = 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v t]
  have h : ‖t‖ = 1 := by rw [NumberField.FinitePlace.norm_def, ht, map_one]; rfl
  apply NNReal.coe_injective
  rw [coe_nnnorm, h, NNReal.coe_one]

theorem localZeta_Φloc [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure] (a : ℂ)
    {c x : Fin 2 → v.adicCompletion F} (hc : ∀ j, Valued.v (c j) ≤ 1) (hc1 : ∃ j, Valued.v (c j) = 1)
    (hx : ∀ j, Valued.v (x j) ≤ 1) (hx1 : ∃ j, Valued.v (x j) = 1) (z : ℂ) :
    (∀ t₀ : (v.adicCompletion F)ˣ, Valued.v (t₀ : v.adicCompletion F) = 1 →
      (∀ j, Valued.v ((t₀ : v.adicCompletion F) * x j - c j) ≤ rad C.e) →
        localZeta μv (fun t => C.Φloc v μv a c (fun l => t * x l)) (localChar C.χ v) z
          = a * ((localChar C.χ v t₀ : ℂˣ) : ℂ)) ∧
    ((∀ t₀ : (v.adicCompletion F)ˣ, Valued.v (t₀ : v.adicCompletion F) = 1 →
        ¬ ∀ j, Valued.v ((t₀ : v.adicCompletion F) * x j - c j) ≤ rad C.e) →
      localZeta μv (fun t => C.Φloc v μv a c (fun l => t * x l)) (localChar C.χ v) z = 0) := by
  classical
  constructor
  · intro t₀ ht₀ hcong
    set S : Set (v.adicCompletion F) := {t | Valued.v (t - t₀) ≤ rad C.e} with hS
    have hSm : MeasurableSet S := (isClosed_ball v (t₀ : v.adicCompletion F) C.e).measurableSet
    set ρ : ℝ := μv.real (C.ball v) with hρ
    have hρ0 : ρ ≠ 0 := by
      rw [hρ, measureReal_def]
      exact ENNReal.toReal_ne_zero.2 ⟨(C.ball_measure_ne v μv).1, (C.ball_measure_ne v μv).2⟩
    set K : ℂ := a * ((ρ⁻¹ : ℝ) : ℂ) * ((localChar C.χ v t₀ : ℂˣ) : ℂ) with hK
    have hint : (fun t => C.Φloc v μv a c (fun l => t * x l) * charExt (localChar C.χ v) t
        * ((modulus t : ℝ) : ℂ) ^ z) = S.indicator (fun _ => K) := by
      funext t
      by_cases ht : t ∈ S
      · have hcg : ∀ j, Valued.v (t * x j - c j) ≤ rad C.e := (C.cong_iff_sub_le hx hx1 hcong t).2 ht
        have ht1 : Valued.v t = 1 := C.valued_eq_one_of_cong hc hc1 hx hx1 hcg
        have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at ht1; exact zero_ne_one ht1
        rw [Set.indicator_of_mem ht, Φloc, if_pos hcg, charExt_of_ne_zero _ ht0,
          C.localChar_eq_of_sub_le ht₀ ht1 ht ht0, modulus_eq_one_of_valued ht1]
        simp [hK, hρ]
      · have hcg : ¬ ∀ j, Valued.v (t * x j - c j) ≤ rad C.e := fun h => ht ((C.cong_iff_sub_le hx hx1 hcong t).1 h)
        rw [Set.indicator_of_notMem ht, Φloc, if_neg hcg, zero_mul, zero_mul]
    have hmS : (mulMeasure μv) S = μv (C.ball v) := by
      rw [mulMeasure, withDensity_apply _ hSm]
      have h1 : ∫⁻ t in S, ((modulus t : ℝ≥0) : ENNReal)⁻¹ ∂(μv.restrict {0}ᶜ) = ∫⁻ t in S, 1 ∂(μv.restrict {0}ᶜ) := by
        refine setLIntegral_congr_fun hSm fun t ht => ?_
        have hcg : ∀ j, Valued.v (t * x j - c j) ≤ rad C.e := (C.cong_iff_sub_le hx hx1 hcong t).2 ht
        rw [modulus_eq_one_of_valued (C.valued_eq_one_of_cong hc hc1 hx hx1 hcg)]
        simp
      rw [h1, setLIntegral_one, Measure.restrict_apply hSm]
      have h2 : S ∩ {0}ᶜ = S := by
        refine Set.inter_eq_left.2 fun t ht h0 => ?_
        have hcg : ∀ j, Valued.v (t * x j - c j) ≤ rad C.e := (C.cong_iff_sub_le hx hx1 hcong t).2 ht
        have ht1 := C.valued_eq_one_of_cong hc hc1 hx hx1 hcg
        rw [Set.mem_singleton_iff.1 h0, map_zero] at ht1
        exact zero_ne_one ht1
      rw [h2, hS, C.measure_near_eq μv]
    rw [localZeta, hint, integral_indicator_const K hSm, measureReal_def, hmS, ← measureReal_def, ← hρ, hK]
    have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ0
    simp only [Complex.real_smul, Complex.ofReal_inv]
    field_simp
  · intro hno
    have : (fun t => C.Φloc v μv a c (fun l => t * x l)) = 0 := by
      funext t
      rw [Φloc, if_neg, Pi.zero_apply]
      intro hcg
      have ht1 : Valued.v t = 1 := C.valued_eq_one_of_cong hc hc1 hx hx1 hcg
      have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at ht1; exact zero_ne_one ht1
      exact hno (Units.mk0 t ht0) ht1 hcg
    rw [this, localZeta_zero_fun]

theorem Φloc_eq_of_near [MeasurableSpace (v.adicCompletion F)] (μv : Measure (v.adicCompletion F)) (a : ℂ)
    (c : Fin 2 → v.adicCompletion F) {y y' : Fin 2 → v.adicCompletion F}
    (h : ∀ l, Valued.v (y' l - y l) ≤ rad C.e) : C.Φloc v μv a c y' = C.Φloc v μv a c y := by
  classical
  have key : ∀ (y y' : Fin 2 → v.adicCompletion F), (∀ l, Valued.v (y' l - y l) ≤ rad C.e) →
      (∀ j, Valued.v (y j - c j) ≤ rad C.e) → ∀ j, Valued.v (y' j - c j) ≤ rad C.e := by
    intro y y' h hy j
    have : y' j - c j = (y' j - y j) + (y j - c j) := by ring
    rw [this]; exact val_add_le _ (h j) (hy j)
  by_cases hy : ∀ j, Valued.v (y j - c j) ≤ rad C.e
  · rw [Φloc, Φloc, if_pos hy, if_pos (key y y' h hy)]
  · have hy' : ¬ ∀ j, Valued.v (y' j - c j) ≤ rad C.e := fun h' =>
      hy (key y' y (fun l => by rw [Valuation.map_sub_swap]; exact h l) h')
    rw [Φloc, Φloc, if_neg hy, if_neg hy']

theorem Φloc_eq_zero_of_not_integral [MeasurableSpace (v.adicCompletion F)] (μv : Measure (v.adicCompletion F))
    (a : ℂ) {c : Fin 2 → v.adicCompletion F} (hc : ∀ j, Valued.v (c j) ≤ 1) {y : Fin 2 → v.adicCompletion F}
    (hy : ¬ ∀ l, Valued.v (y l) ≤ 1) : C.Φloc v μv a c y = 0 := by
  classical
  rw [Φloc, if_neg]
  intro h
  apply hy
  intro l
  have : y l = (y l - c l) + c l := by ring
  rw [this]; exact val_add_le _ ((h l).trans (rad_le_one _)) (hc l)

end LocalZeta

section TestFn

variable (Φv : (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ)

open scoped Classical in

def hfun (y : Fin 2 → FiniteAdeleRing (𝓞 F) F) : ℂ :=
  if ∀ v ∉ C.T, ∀ l, y l v ∈ v.adicCompletionIntegers F then ∏ v ∈ C.T, Φv v (fun l => y l v) else 0

theorem isOpen_integralOutside :
    IsOpen {y : Fin 2 → FiniteAdeleRing (𝓞 F) F | ∀ v ∉ C.T, ∀ l, y l v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ C.T → a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ C.T)
  have : {y : Fin 2 → FiniteAdeleRing (𝓞 F) F | ∀ v ∉ C.T, ∀ l, y l v ∈ v.adicCompletionIntegers F}
      = ⋂ l : Fin 2, (fun y => y l) ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ C.T → a v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h l v hv => h v hv l, fun h v hv l => h l v hv⟩
  rw [this]
  exact isOpen_iInter_of_finite fun l => h1.preimage (continuous_apply l)

theorem isLocallyConstant_hfun
    (hΦ : ∀ v (y y' : Fin 2 → v.adicCompletion F), (∀ l, Valued.v (y' l - y l) ≤ rad C.e) → Φv v y' = Φv v y) :
    IsLocallyConstant (C.hfun Φv) := by
  classical
  refine (IsLocallyConstant.iff_exists_open _).2 fun y => ?_
  by_cases hy : ∀ v ∉ C.T, ∀ l, y l v ∈ v.adicCompletionIntegers F
  · refine ⟨{y' | ∀ v ∉ C.T, ∀ l, y' l v ∈ v.adicCompletionIntegers F} ∩
      ⋂ v ∈ C.T, ⋂ l : Fin 2, (fun y' : Fin 2 → FiniteAdeleRing (𝓞 F) F => y' l v) ⁻¹'
        {z | Valued.v (z - y l v) ≤ rad C.e}, ?_, ⟨hy, ?_⟩, fun y' hy' => ?_⟩
    · refine C.isOpen_integralOutside.inter (isOpen_biInter_finset fun v _ => isOpen_iInter_of_finite fun l => ?_)
      exact (isOpen_ball v _ C.e).preimage ((continuous_finAdeleEval (𝓞 F) F v).comp (continuous_apply l))
    · simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, sub_self, map_zero]
      exact fun _ _ _ => zero_le'
    · obtain ⟨hy'1, hy'2⟩ := hy'
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq] at hy'2
      have hy'1 : ∀ v ∉ C.T, ∀ l, y' l v ∈ v.adicCompletionIntegers F := hy'1
      rw [hfun, hfun, if_pos hy'1, if_pos hy]
      exact Finset.prod_congr rfl fun v hv => hΦ v _ _ fun l => hy'2 v hv l
  · push Not at hy
    obtain ⟨v, hv, l, hl⟩ := hy
    refine ⟨(fun y' : Fin 2 → FiniteAdeleRing (𝓞 F) F => y' l v) ⁻¹' (v.adicCompletionIntegers F : Set _)ᶜ, ?_,
      fun h => hl h, fun y' hy' => ?_⟩
    · exact (isClosed_adicCompletionIntegers v).isOpen_compl.preimage
        ((continuous_finAdeleEval (𝓞 F) F v).comp (continuous_apply l))
    · have h1 : ¬ ∀ v ∉ C.T, ∀ l, y' l v ∈ v.adicCompletionIntegers F := fun h => hy' (h v hv l)
      have h2 : ¬ ∀ v ∉ C.T, ∀ l, y l v ∈ v.adicCompletionIntegers F := fun h => hl (h v hv l)
      rw [hfun, hfun, if_neg h1, if_neg h2]

theorem hasCompactSupport_hfun (hΦ : ∀ v (y : Fin 2 → v.adicCompletion F), (¬ ∀ l, Valued.v (y l) ≤ 1) → Φv v y = 0) :
    HasCompactSupport (C.hfun Φv) := by
  classical
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ : Fin 2 => integralFiniteAdeles (𝓞 F) F)
    (isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles (𝓞 F) F) fun y hy => ?_
  simp only [Set.mem_univ_pi, not_forall] at hy
  obtain ⟨l, hl⟩ := hy
  have hl' : ∃ v, y l v ∉ v.adicCompletionIntegers F := by
    by_contra h; push Not at h; exact hl h
  obtain ⟨v, hv⟩ := hl'
  rw [hfun]
  by_cases hT : v ∈ C.T
  · split_ifs
    · refine Finset.prod_eq_zero hT (hΦ v _ fun h => hv ?_)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h l)
    · rfl
  · rw [if_neg]
    exact fun h => hv (h v hT l)

theorem hfun_of_not (y : Fin 2 → FiniteAdeleRing (𝓞 F) F)
    (hy : ∃ v ∉ C.T, ∃ l, y l v ∉ v.adicCompletionIntegers F) : C.hfun Φv y = 0 := by
  classical
  rw [hfun, if_neg]
  intro h
  obtain ⟨v, hv, l, hl⟩ := hy
  exact hl (h v hv l)

theorem hfun_of (y : Fin 2 → FiniteAdeleRing (𝓞 F) F) (hy : ∀ v ∉ C.T, ∀ l, y l v ∈ v.adicCompletionIntegers F) :
    C.hfun Φv y = ∏ v ∈ C.T, Φv v (fun l => y l v) := by
  classical
  rw [hfun, if_pos hy]

end TestFn

theorem prod_localUnit_apply (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((∏ w ∈ T, localUnit (𝓞 F) F w (u w) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
      = ∏ w ∈ T, ((localUnit (𝓞 F) F w (u w) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v := by
  rw [Units.coe_prod, ← finAdeleEval_apply (𝓞 F) F v, map_prod]; rfl

theorem prod_localUnit_apply_of_mem {T : Finset (HeightOneSpectrum (𝓞 F))}
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ T) :
    ((∏ w ∈ T, localUnit (𝓞 F) F w (u w) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
      = (u v : v.adicCompletion F) := by
  rw [prod_localUnit_apply, Finset.prod_eq_single v (fun w _ hw => localUnit_apply_of_ne (𝓞 F) F w (u w) (Ne.symm hw))
    (fun h => (h hv).elim), localUnit_apply_self]

theorem prod_localUnit_apply_of_not_mem {T : Finset (HeightOneSpectrum (𝓞 F))}
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T) :
    ((∏ w ∈ T, localUnit (𝓞 F) F w (u w) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := by
  rw [prod_localUnit_apply]
  exact Finset.prod_eq_one fun w hw => localUnit_apply_of_ne (𝓞 F) F w (u w) (fun h => hv (h ▸ hw))

theorem exists_valued_row_eq_one {k : AdelicGL2 (𝓞 F) F} (hk : IsKf k) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ j : Fin 2, Valued.v (L v k 1 j) = 1 := by
  have hle : ∀ i j, Valued.v (L v k i j) ≤ 1 := fun i j => (hk.valued_le_one v i j).1
  have hdet : Valued.v (L v k).det = 1 := valued_det_finComponent_eq_one hk.1 v
  by_contra hcon
  push Not at hcon
  have hlt : ∀ j : Fin 2, Valued.v (L v k 1 j) < 1 := fun j => lt_of_le_of_ne (hle 1 j) (hcon j)
  have h1 : Valued.v (L v k 0 0 * L v k 1 1) < 1 := by
    rw [Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (L v k 1 1) := mul_le_mul_left (hle 0 0) _
      _ < 1 := by rw [one_mul]; exact hlt 1
  have h2 : Valued.v (L v k 0 1 * L v k 1 0) < 1 := by
    rw [Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (L v k 1 0) := mul_le_mul_left (hle 0 1) _
      _ < 1 := by rw [one_mul]; exact hlt 0
  have : Valued.v (L v k).det < 1 := by
    rw [Matrix.det_fin_two]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h2)
  rw [hdet] at this
  exact lt_irrefl _ this

open LanglandsTunnell.TateLocal in

theorem main [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (v₀ : HeightOneSpectrum (𝓞 F)) (hv₀ : v₀ ∈ C.T) :
    ∃ (m : Fin n → ℕ)
      (h : (i : Fin n) → Fin (m i) → (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (Φf : (i : Fin n) → Fin (m i) → (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ),
      (∀ i j, IsLocallyConstant (h i j)) ∧
      (∀ i j, HasCompactSupport (h i j)) ∧
      (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
        (∃ v ∉ C.T, ∃ l, y l v ∉ v.adicCompletionIntegers F) → h i j y = 0) ∧
      (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
        (∀ v ∉ C.T, ∀ l, y l v ∈ v.adicCompletionIntegers F) →
          h i j y = ∏ v ∈ C.T, Φf i j v (fun l => y l v)) ∧
      ∀ (i : Fin n) (z : ℂ) (k : AdelicGL2 (𝓞 F) F),
        k ∈ adelicMaximalCompact F → glArch (𝓞 F) F k = 1 →
          (∑ j, ((C.μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
              * ∏ v ∈ C.T, localZeta (μf v)
                  (fun t => Φf i j v (fun l => t * L v k 1 l)) (localChar C.χ v) z)
            = C.U i k := by
  classical
  obtain ⟨ι, _, rep, hrep, hcov⟩ := C.exists_cover
  set M : ℕ := Fintype.card ι
  let eqv : ι ≃ Fin M := Fintype.equivFin ι

  let nmult : ι → ℕ := fun r => (Finset.univ.filter fun r' : ι => C.RelT (rep r') (rep r)).card
  let coef : Fin n → ι → HeightOneSpectrum (𝓞 F) → ℂ := fun i r v =>
    if v = v₀ then C.W i (rep r) * ((nmult r : ℂ))⁻¹ else 1
  let Φι : Fin n → ι → (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ := fun i r v =>
    C.Φloc v (μf v) (coef i r v) (fun l => L v (rep r) 1 l)
  refine ⟨fun _ => M, fun i j => C.hfun (Φι i (eqv.symm j)), fun i j v => Φι i (eqv.symm j) v,
    fun i j => ?_, fun i j => ?_, fun i j y hy => C.hfun_of_not _ y hy, fun i j y hy => C.hfun_of _ y hy,
    fun i z k hk hka => ?_⟩
  · exact C.isLocallyConstant_hfun _ fun v y y' h => C.Φloc_eq_of_near (μf v) _ _ h
  · exact C.hasCompactSupport_hfun _ fun v y hy =>
      C.Φloc_eq_zero_of_not_integral (μf v) _ (fun l => ((hrep _).valued_le_one v 1 l).1) hy

  have hkK : IsKf k := ⟨hk, hka⟩
  have hxle : ∀ v (l : Fin 2), Valued.v (L v k 1 l) ≤ 1 := fun v l => (hkK.valued_le_one v 1 l).1

  rw [show (∑ j : Fin M, ((C.μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
      * ∏ v ∈ C.T, localZeta (μf v) (fun t => Φι i (eqv.symm j) v (fun l => t * L v k 1 l)) (localChar C.χ v) z)
      = ∑ r : ι, ((C.μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
      * ∏ v ∈ C.T, localZeta (μf v) (fun t => Φι i r v (fun l => t * L v k 1 l)) (localChar C.χ v) z from
    Equiv.sum_comp eqv.symm (fun r => ((C.μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
      * ∏ v ∈ C.T, localZeta (μf v) (fun t => Φι i r v (fun l => t * L v k 1 l)) (localChar C.χ v) z)]

  have hterm : ∀ r : ι,
      (∏ v ∈ C.T, localZeta (μf v) (fun t => Φι i r v (fun l => t * L v k 1 l)) (localChar C.χ v) z)
        = if C.RelT (rep r) k then C.W i k * ((nmult r : ℂ))⁻¹ else 0 := by
    intro r
    by_cases hP : C.RelT (rep r) k
    · rw [if_pos hP]

      have hu : ∀ v, ∃ u : (v.adicCompletion F)ˣ, v ∈ C.T →
          Valued.v (u : v.adicCompletion F) = 1 ∧
            ∀ j, Valued.v ((u : v.adicCompletion F) * L v k 1 j - L v (rep r) 1 j) ≤ rad C.e := by
        intro v
        by_cases hv : v ∈ C.T
        · obtain ⟨u, hu1, hu2⟩ := C.rel_symm (hP v hv)
          exact ⟨u, fun _ => ⟨hu1, hu2⟩⟩
        · exact ⟨1, fun h => (hv h).elim⟩
      choose u hu using hu
      have hZ : ∀ v ∈ C.T, localZeta (μf v) (fun t => Φι i r v (fun l => t * L v k 1 l)) (localChar C.χ v) z
          = coef i r v * ((localChar C.χ v (u v) : ℂˣ) : ℂ) := fun v hv =>
        (C.localZeta_Φloc (μf v) (coef i r v) (fun l => ((hrep r).valued_le_one v 1 l).1)
          (exists_valued_row_eq_one (hrep r) v) (hxle v) (exists_valued_row_eq_one hkK v) z).1
          (u v) (hu v hv).1 (hu v hv).2
      rw [Finset.prod_congr rfl hZ, Finset.prod_mul_distrib]

      have hcoef : ∏ v ∈ C.T, coef i r v = C.W i (rep r) * ((nmult r : ℂ))⁻¹ := by
        rw [Finset.prod_ite_eq' C.T v₀, if_pos hv₀]

      set a : (FiniteAdeleRing (𝓞 F) F)ˣ := ∏ v ∈ C.T, localUnit (𝓞 F) F v (u v) with ha
      have hchar : ∏ v ∈ C.T, ((localChar C.χ v (u v) : ℂˣ) : ℂ) = ((C.χ (finIdele a) : ℂˣ) : ℂ) := by
        rw [ha]
        unfold finIdele
        rw [map_prod, map_prod, Units.coe_prod]; rfl

      have haint : ∀ v, Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 ∧
          Valued.v (((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 := by
        intro v
        have hinv : a⁻¹ = ∏ w ∈ C.T, localUnit (𝓞 F) F w (u w)⁻¹ := by
          rw [ha, ← Finset.prod_inv_distrib]
          exact Finset.prod_congr rfl fun w _ => (map_inv _ _).symm
        by_cases hv : v ∈ C.T
        · rw [hinv, prod_localUnit_apply_of_mem u hv, prod_localUnit_apply_of_mem (fun w => (u w)⁻¹) hv,
            Units.val_inv_eq_inv_val, map_inv₀, (hu v hv).1, inv_one]
          exact ⟨le_rfl, le_rfl⟩
        · rw [hinv, prod_localUnit_apply_of_not_mem u hv, prod_localUnit_apply_of_not_mem (fun w => (u w)⁻¹) hv,
            map_one]
          exact ⟨le_rfl, le_rfl⟩
      have hW : C.W i (rep r) = (((C.χ (finIdele a))⁻¹ : ℂˣ) : ℂ) * C.W i k := by
        rw [← C.W_diag_mul i a haint k]
        refine C.W_eq_of_rowCong i ((isKf_bU_fin 1 a (isLevelUnit_one ∅ 0).1 haint).mul hkK) (hrep r) fun v hv j => ?_
        rw [L_diag_mul_row, prod_localUnit_apply_of_mem u hv, Valuation.map_sub_swap]
        exact (hu v hv).2 j
      rw [hcoef, hchar, hW]
      have hχ0 : ((C.χ (finIdele a) : ℂˣ) : ℂ) ≠ 0 := (C.χ (finIdele a)).ne_zero
      rw [Units.val_inv_eq_inv_val]
      field_simp
    · rw [if_neg hP]
      have : ∃ v ∈ C.T, ¬ C.Rel v (rep r) k := by
        by_contra h; push Not at h; exact hP h
      obtain ⟨v, hv, hnot⟩ := this
      apply Finset.prod_eq_zero hv
      refine (C.localZeta_Φloc (μf v) (coef i r v) (fun l => ((hrep r).valued_le_one v 1 l).1)
        (exists_valued_row_eq_one (hrep r) v) (hxle v) (exists_valued_row_eq_one hkK v) z).2 fun t₀ ht₀ hcg => ?_
      exact hnot (C.rel_symm ⟨t₀, ht₀, hcg⟩)
  simp_rw [hterm, mul_ite, mul_zero]
  have hex : ∃ r, C.RelT (rep r) k := by
    obtain ⟨r, hr⟩ := hcov k hkK
    exact ⟨r, fun v hv => ⟨1, by simp, fun j => by rw [Units.val_one, one_mul, Valuation.map_sub_swap]; exact hr v hv j⟩⟩
  have hsum := C.sum_inv_mult_eq_one rep k hex
  calc (∑ r : ι, if C.RelT (rep r) k then
          ((C.μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * (C.W i k * ((nmult r : ℂ))⁻¹) else 0)
      = ((C.μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * C.W i k
          * ∑ r : ι, (if C.RelT (rep r) k then ((nmult r : ℂ))⁻¹ else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        split_ifs <;> ring
    _ = C.U i k := by rw [hsum, mul_one, ← C.U_eq_mul_W]

end Ctx

theorem nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

theorem continuous_units_of_continuous_val (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : Continuous fun x => ((χ x : ℂˣ) : ℂ)) : Continuous χ := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  simp_rw [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun x => (χ x).ne_zero

theorem IsLevel.mono {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') {e : ℕ} {g : AdelicGL2 (𝓞 F) F}
    (h : IsLevel T' e g) : IsLevel T e g := fun v hv => h v (hT hv)

theorem IsLevelUnit.mono {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') {e : ℕ}
    {a : (FiniteAdeleRing (𝓞 F) F)ˣ} (h : IsLevelUnit T' e a) : IsLevelUnit T e a := ⟨h.1, fun v hv => h.2 v (hT hv)⟩

theorem isUnramifiedCharAt_of_levelUnit {T : Finset (HeightOneSpectrum (𝓞 F))} {e : ℕ} (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχ : ∀ a : (FiniteAdeleRing (𝓞 F) F)ˣ, IsLevelUnit T e a → χ (finIdele a) = 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T) : IsUnramifiedCharAt χ v := by
  intro t ht ht'
  rw [localChar_apply]
  exact hχ _ (isLevelUnit_localUnit v t ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ht)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ht') (fun h => (hv h).elim))

end R4Fi
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth.R4Fi"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth.R4Fi"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

open R4Fi in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (n : ℕ) (U : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
    (_hUf : ∀ i, IsKfSmooth F (U i))
    (_hUB : ∀ (i : Fin n) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glArch (𝓞 F) F b = 1 → glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U i (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U i g) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ v ∉ S, IsUnramifiedCharAt μ v ∧ IsUnramifiedCharAt ν v) ∧
      ∃ (m : Fin n → ℕ)
        (h : (i : Fin n) → Fin (m i) → (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)
        (Φf : (i : Fin n) → Fin (m i) → (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ),
        (∀ i j, IsLocallyConstant (h i j)) ∧
        (∀ i j, HasCompactSupport (h i j)) ∧
        (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
          (∃ v ∉ S, ∃ l, y l v ∉ v.adicCompletionIntegers F) → h i j y = 0) ∧
        (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
          (∀ v ∉ S, ∀ l, y l v ∈ v.adicCompletionIntegers F) →
            h i j y = ∏ v ∈ S, Φf i j v (fun l => y l v)) ∧
        ∀ (i : Fin n) (z : ℂ) (k : AdelicGL2 (𝓞 F) F),
          k ∈ adelicMaximalCompact F → glArch (𝓞 F) F k = 1 →
            (∑ j, ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf i j v (fun l => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 l))
                    (localChar (μ * ν⁻¹) v) z)
              = U i k := by
  classical
  obtain ⟨T, e, he, hinv⟩ := exists_level_rightInvariant n U _hUf
  by_cases hne : ∃ (i : Fin n) (g : AdelicGL2 (𝓞 F) F), IsKf g ∧ U i g ≠ 0
  · obtain ⟨i₀, g₀, hg₀, hU0⟩ := hne
    obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
    have hchar := chars_eq_one_of_ne_zero U μ ν T e hinv _hUB i₀ g₀ hg₀ hU0
    have hsub : T ⊆ insert v₀ T := Finset.subset_insert v₀ T
    let C : Ctx F n :=
      { U := U, μ := μ, ν := ν, T := insert v₀ T, e := e, he := he
        hinv := fun i g hg hlev x => hinv i g hg (hlev.mono hsub) x
        hUB := _hUB
        hchar := fun a ha => hchar a (ha.mono hsub) }
    obtain ⟨m, h, Φf, h1, h2, h3, h4, h5⟩ := C.main μf v₀ (Finset.mem_insert_self v₀ T)
    refine ⟨insert v₀ T, fun v hv => ⟨isUnramifiedCharAt_of_levelUnit μ (fun a ha => (C.hchar a ha).1) hv,
      isUnramifiedCharAt_of_levelUnit ν (fun a ha => (C.hchar a ha).2) hv⟩, m, h, Φf, h1, h2, h3, h4, ?_⟩
    intro i z k hk hka
    exact h5 i z k hk hka
  ·
    push Not at hne
    obtain ⟨Sμ, hSμ⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous F μ
      (continuous_units_of_continuous_val μ _hμc)
    obtain ⟨Sν, hSν⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous F ν
      (continuous_units_of_continuous_val ν _hνc)
    refine ⟨Sμ ∪ Sν, fun v hv => ⟨hSμ v fun h => hv (Finset.mem_union_left _ h),
      hSν v fun h => hv (Finset.mem_union_right _ h)⟩, fun _ => 0, fun _ j => j.elim0, fun _ j => j.elim0,
      fun _ j => j.elim0, fun _ j => j.elim0, fun _ j => j.elim0, fun _ j => j.elim0, fun i z k hk hka => ?_⟩
    rw [hne i k ⟨hk, hka⟩]
    exact Finset.sum_of_isEmpty _

end S_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth (solution)
