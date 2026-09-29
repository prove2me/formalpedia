-- Prove2me | solution 1 for AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b0a4b3b0-9e5c-58c0-bc93-1cf49e9ee1c6

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Theorems.Thm_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
import Theorems.Thm_LocalGL2_existsUnique_mem_doubleCoset_zpow
import Theorems.Thm_NumberField_eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace N3Main

open HeckeIntegralSeam LocalGL2

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem doubleCoset_mul_right_of_mem {U : Subgroup G} {g u : G} (hu : u ∈ U) :
    HeckePair.doubleCoset U (g * u) = HeckePair.doubleCoset U g := by
  ext x
  rw [HeckePair.mem_doubleCoset_iff, HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, u * b, U.mul_mem hu hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, u⁻¹ * b, U.mul_mem (U.inv_mem hu) hb, by group⟩

theorem doubleCoset_mul_left_of_mem {U : Subgroup G} {g u : G} (hu : u ∈ U) (x : G)
    (hx : x ∈ HeckePair.doubleCoset U g) : u * x ∈ HeckePair.doubleCoset U g := by
  rw [HeckePair.mem_doubleCoset_iff] at hx ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨u * a, U.mul_mem hu ha, b, hb, by group⟩

theorem IsHeckeCosetSystem.map_of_injective {U : Subgroup G} {U' : Subgroup G'} (φ : G →* G')
    (hφ : Function.Injective φ) (hU : U' = U.map φ) {g : G} {ι : Type*} {reps : ι → G}
    (h : IsHeckeCosetSystem U g reps) : IsHeckeCosetSystem U' (φ g) (fun i => φ (reps i)) := by
  have hmem : ∀ {x : G}, x ∈ U ↔ φ x ∈ U' := by
    intro x; rw [hU, Subgroup.mem_map]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => by rwa [← hφ hyx]⟩
  have himg : ∀ {x' : G'}, x' ∈ U' → ∃ x ∈ U, φ x = x' := by
    intro x' hx'; rw [hU, Subgroup.mem_map] at hx'; exact hx'
  refine ⟨fun i => ?_, fun x' hx' => ?_, fun i i' hii' => ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.1 (h.mem_doubleCoset i)
    exact HeckePair.mem_doubleCoset_iff.2 ⟨φ a, hmem.1 ha, φ b, hmem.1 hb, by rw [← map_mul, ← map_mul, hab]⟩
  · obtain ⟨a', ha', b', hb', rfl⟩ := HeckePair.mem_doubleCoset_iff.1 hx'
    obtain ⟨a, ha, rfl⟩ := himg ha'
    obtain ⟨b, hb, rfl⟩ := himg hb'
    obtain ⟨i, hi⟩ := h.covers (a * g * b) (HeckePair.mem_doubleCoset_iff.2 ⟨a, ha, b, hb, rfl⟩)
    refine ⟨i, ?_⟩
    rw [← map_mul, ← map_mul, QuotientGroup.eq, ← map_inv, ← map_mul]
    exact hmem.1 (QuotientGroup.eq.1 hi)
  · apply h.mk_injective
    have := QuotientGroup.eq.1 hii'
    rw [← map_inv, ← map_mul] at this
    exact QuotientGroup.eq.2 (hmem.2 this)

end Transport

section Integral

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Fv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K

theorem mem_integralSubgroup_iff_entries (g : GL (Fin 2) Fv) :
    g ∈ integralSubgroup Ov Fv ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) Fv) i j ∈ v.adicCompletionIntegers K) ∧
        ∀ i j, ((g⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) i j ∈ v.adicCompletionIntegers K := by
  rw [mem_integralSubgroup_iff]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (algebraMap Ov Fv) ((y : Matrix (Fin 2) (Fin 2) Ov) i j) ∈ _
      exact ((y : Matrix (Fin 2) (Fin 2) Ov) i j).2
    · rw [← map_inv]
      show (algebraMap Ov Fv) (((y⁻¹ : GL (Fin 2) Ov) : Matrix (Fin 2) (Fin 2) Ov) i j) ∈ _
      exact (((y⁻¹ : GL (Fin 2) Ov) : Matrix (Fin 2) (Fin 2) Ov) i j).2
  · rintro ⟨h1, h2⟩
    set A : Matrix (Fin 2) (Fin 2) Ov := Matrix.of fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) Fv) i j, h1 i j⟩ with hA
    set B : Matrix (Fin 2) (Fin 2) Ov := Matrix.of fun i j => ⟨((g⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) i j, h2 i j⟩ with hB
    have hAm : A.map (algebraMap Ov Fv) = (g : Matrix (Fin 2) (Fin 2) Fv) := by ext i j; rfl
    have hBm : B.map (algebraMap Ov Fv) = ((g⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) := by ext i j; rfl
    have hinj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) Ov => M.map (algebraMap Ov Fv)) :=
      Matrix.map_injective (fun a b h => Subtype.ext h)
    refine ⟨⟨A, B, ?_, ?_⟩, ?_⟩
    · apply hinj
      show (A * B).map (algebraMap Ov Fv) = (1 : Matrix (Fin 2) (Fin 2) Ov).map (algebraMap Ov Fv)
      rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    · apply hinj
      show (B * A).map (algebraMap Ov Fv) = (1 : Matrix (Fin 2) (Fin 2) Ov).map (algebraMap Ov Fv)
      rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    · ext i j; rfl

theorem coe_integralSubgroup_eq_localIntegralSet :
    ((integralSubgroup Ov Fv : Subgroup (GL (Fin 2) Fv)) : Set (GL (Fin 2) Fv)) = AutomorphicForm.localIntegralSet K v := by
  ext g
  rw [SetLike.mem_coe, mem_integralSubgroup_iff_entries, AutomorphicForm.mem_localIntegralSet]

end Integral

end N3Main

namespace N3Main

open HeckeIntegralSeam LocalGL2

section LocalIso

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  (e : w.adicCompletion L ≃+* v.adicCompletion K)
  (he : ∀ x : w.adicCompletion L, Valued.v (e x) = Valued.v x)

local notation "Fv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K
local notation "Lw" => w.adicCompletion L
local notation "Ow" => w.adicCompletionIntegers L

include he in
theorem valued_symm (y : Fv) : Valued.v (e.symm y) = Valued.v y := by
  conv_rhs => rw [← e.apply_symm_apply y]
  rw [he]

def intEquiv : Ow ≃+* Ov where
  toFun x := ⟨e x, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).2
    (by rw [he]; exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 L) L w).1 x.2)⟩
  invFun y := ⟨e.symm y, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 L) L w).2
    (by rw [valued_symm K L v w e he]; exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).1 y.2)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

theorem algebraMap_intEquiv (x : Ow) :
    algebraMap Ov Fv (intEquiv K L v w e he x) = e (algebraMap Ow Lw x) := rfl

theorem coe_intEquiv (x : Ow) : ((intEquiv K L v w e he x : Ov) : Fv) = e (x : Lw) := rfl

def GLe : GL (Fin 2) Lw →* GL (Fin 2) Fv := Matrix.GeneralLinearGroup.map e.toRingHom

theorem GLe_apply (g : GL (Fin 2) Lw) (i j : Fin 2) :
    ((GLe K L v w e g : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) i j = e ((g : Matrix (Fin 2) (Fin 2) Lw) i j) := rfl

theorem GLe_injective : Function.Injective (GLe K L v w e) := by
  intro g g' h
  apply Units.ext
  ext i j : 1
  apply e.injective
  rw [← GLe_apply, ← GLe_apply, h]

include he in
theorem map_integralSubgroup :
    integralSubgroup Ov Fv = (integralSubgroup Ow Lw).map (GLe K L v w e) := by
  ext g'
  rw [Subgroup.mem_map, mem_integralSubgroup_iff_entries K v]
  constructor
  · rintro ⟨h1, h2⟩
    set g : GL (Fin 2) Lw := Matrix.GeneralLinearGroup.map e.symm.toRingHom g' with hg
    have hgij : ∀ i j, (g : Matrix (Fin 2) (Fin 2) Lw) i j = e.symm ((g' : Matrix (Fin 2) (Fin 2) Fv) i j) := fun i j => rfl
    have hg' : GLe K L v w e g = g' := by
      apply Units.ext; ext i j
      rw [GLe_apply, hgij, e.apply_symm_apply]
    have hginv : ∀ i j, ((g⁻¹ : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) i j =
        e.symm (((g'⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) i j) := fun i j => by
      rw [hg, ← map_inv]; rfl
    refine ⟨g, ?_, hg'⟩
    rw [mem_integralSubgroup_iff_entries L w]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hgij, HeightOneSpectrum.mem_adicCompletionIntegers, valued_symm K L v w e he]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).1 (h1 i j)
    · rw [hginv, HeightOneSpectrum.mem_adicCompletionIntegers, valued_symm K L v w e he]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).1 (h2 i j)
  · rintro ⟨g, hg, rfl⟩
    rw [mem_integralSubgroup_iff_entries L w] at hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [GLe_apply, HeightOneSpectrum.mem_adicCompletionIntegers, he]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 L) L w).1 (hg.1 i j)
    · rw [← map_inv, GLe_apply, HeightOneSpectrum.mem_adicCompletionIntegers, he]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 L) L w).1 (hg.2 i j)

theorem algebraMap_intEquiv_ne_zero {ϖ : Ow} (hϖ0 : algebraMap Ow Lw ϖ ≠ 0) :
    algebraMap Ov Fv (intEquiv K L v w e he ϖ) ≠ 0 := by
  rw [algebraMap_intEquiv]; exact (map_ne_zero_iff _ e.injective).2 hϖ0

theorem GLe_diagPi (ϖ : Ow) (hϖ0 : algebraMap Ow Lw ϖ ≠ 0) :
    GLe K L v w e (diagPi ϖ hϖ0) = diagPi (intEquiv K L v w e he ϖ) (algebraMap_intEquiv_ne_zero K L v w e he hϖ0) := by
  apply Units.ext; ext i j
  rw [GLe_apply, coe_diagPi, coe_diagPi]
  fin_cases i <;> fin_cases j <;> simp [coe_intEquiv] <;> rfl

theorem irreducible_intEquiv {ϖ : Ow} (hϖ : Irreducible ϖ) : Irreducible (intEquiv K L v w e he ϖ) :=
  (MulEquiv.irreducible_iff (intEquiv K L v w e he).toMulEquiv).2 hϖ

end LocalIso

section Walk

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Fv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K

def W (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => (q + 1) * W q k 1
  | k + 1, d + 1 => W q k d + q * W q k (d + 2)

def scalarGL : Fvˣ →* GL (Fin 2) Fv := Units.map (Matrix.scalar (Fin 2) : Fv →+* Matrix (Fin 2) (Fin 2) Fv).toMonoidHom

theorem scalarGL_coe (t : Fvˣ) : ((scalarGL K v t : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) = (t : Fv) • 1 := by
  show Matrix.scalar (Fin 2) (t : Fv) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem scalarGL_comm (t : Fvˣ) (g : GL (Fin 2) Fv) : scalarGL K v t * g = g * scalarGL K v t := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (t : Fv) * (g : Matrix (Fin 2) (Fin 2) Fv) = (g : Matrix (Fin 2) (Fin 2) Fv) * Matrix.scalar (Fin 2) (t : Fv)
  exact (Matrix.scalar_commute (t : Fv) (fun r' => mul_comm _ r') _).eq

theorem eq_scalarGL_of_coe {Z : GL (Fin 2) Fv} {c : Fv} (hc : c ≠ 0) (hZ : (Z : Matrix (Fin 2) (Fin 2) Fv) = c • 1) :
    Z = scalarGL K v (Units.mk0 c hc) := by
  apply Units.ext; rw [hZ, scalarGL_coe, Units.val_mk0]

theorem scalarGL_mem (u : Ovˣ) : scalarGL K v (Units.map (algebraMap Ov Fv : Ov →* Fv) u) ∈ integralSubgroup Ov Fv := by
  rw [mem_integralSubgroup_iff_entries]
  have hinv : (scalarGL K v (Units.map (algebraMap Ov Fv : Ov →* Fv) u))⁻¹ = scalarGL K v (Units.map (algebraMap Ov Fv : Ov →* Fv) u⁻¹) := by
    rw [← map_inv, ← map_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [scalarGL_coe, Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · rw [smul_eq_mul, mul_one]; exact (u : Ov).2
    · rw [smul_zero]; exact ZeroMemClass.zero_mem _
  · rw [hinv, scalarGL_coe, Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · rw [smul_eq_mul, mul_one]; exact ((u⁻¹ : Ovˣ) : Ov).2
    · rw [smul_zero]; exact ZeroMemClass.zero_mem _

theorem commute_of_diag {g h : GL (Fin 2) Fv}
    (hg01 : (g : Matrix (Fin 2) (Fin 2) Fv) 0 1 = 0) (hg10 : (g : Matrix (Fin 2) (Fin 2) Fv) 1 0 = 0)
    (hh01 : (h : Matrix (Fin 2) (Fin 2) Fv) 0 1 = 0) (hh10 : (h : Matrix (Fin 2) (Fin 2) Fv) 1 0 = 0) :
    Commute g h := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg01, hg10, hh01, hh10, mul_comm]

def diagU1 (u : Ovˣ) : GL (Fin 2) Fv :=
  ⟨!![algebraMap Ov Fv u, 0; 0, 1], !![algebraMap Ov Fv ((u⁻¹ : Ovˣ) : Ov), 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul]⟩

def diag1U (u : Ovˣ) : GL (Fin 2) Fv :=
  ⟨!![1, 0; 0, algebraMap Ov Fv u], !![1, 0; 0, algebraMap Ov Fv ((u⁻¹ : Ovˣ) : Ov)], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul]⟩

@[scoped simp] theorem coe_diagU1 (u : Ovˣ) : (diagU1 K v u : Matrix (Fin 2) (Fin 2) Fv) = !![algebraMap Ov Fv u, 0; 0, 1] := rfl
@[scoped simp] theorem coe_diag1U (u : Ovˣ) : (diag1U K v u : Matrix (Fin 2) (Fin 2) Fv) = !![1, 0; 0, algebraMap Ov Fv u] := rfl

theorem diagU1_mem (u : Ovˣ) : diagU1 K v u ∈ integralSubgroup Ov Fv := by
  rw [mem_integralSubgroup_iff_entries]
  have hinv : ((diagU1 K v u)⁻¹ : GL (Fin 2) Fv) = diagU1 K v u⁻¹ := by
    rw [inv_eq_iff_mul_eq_one]; apply Units.ext; ext i j
    rw [Units.val_mul, coe_diagU1, coe_diagU1]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_diagU1]
    fin_cases i <;> fin_cases j <;>
      first | exact SetLike.coe_mem _ | exact ZeroMemClass.zero_mem _ | exact OneMemClass.one_mem _
  · rw [hinv, coe_diagU1]
    fin_cases i <;> fin_cases j <;>
      first | exact SetLike.coe_mem _ | exact ZeroMemClass.zero_mem _ | exact OneMemClass.one_mem _

theorem diag1U_mem (u : Ovˣ) : diag1U K v u ∈ integralSubgroup Ov Fv := by
  rw [mem_integralSubgroup_iff_entries]
  have hinv : ((diag1U K v u)⁻¹ : GL (Fin 2) Fv) = diag1U K v u⁻¹ := by
    rw [inv_eq_iff_mul_eq_one]; apply Units.ext; ext i j
    rw [Units.val_mul, coe_diag1U, coe_diag1U]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_diag1U]
    fin_cases i <;> fin_cases j <;>
      first | exact SetLike.coe_mem _ | exact ZeroMemClass.zero_mem _ | exact OneMemClass.one_mem _
  · rw [hinv, coe_diag1U]
    fin_cases i <;> fin_cases j <;>
      first | exact SetLike.coe_mem _ | exact ZeroMemClass.zero_mem _ | exact OneMemClass.one_mem _

theorem doubleCoset_eq_of_mul_unit (ϖ' ϖK : Ov) (h'0 : algebraMap Ov Fv ϖ' ≠ 0) (hK0 : algebraMap Ov Fv ϖK ≠ 0)
    (u : Ovˣ) (hu : ϖ' * u = ϖK) (a b : ℤ) :
    HeckePair.doubleCoset (integralSubgroup Ov Fv) (diagPi ϖK hK0 ^ a * localRepInf ϖK hK0 ^ b) =
      HeckePair.doubleCoset (integralSubgroup Ov Fv) (diagPi ϖ' h'0 ^ a * localRepInf ϖ' h'0 ^ b) := by
  have hu' : algebraMap Ov Fv ϖK = algebraMap Ov Fv ϖ' * algebraMap Ov Fv (u : Ov) := by
    rw [← map_mul, hu]
  have h1 : diagPi ϖK hK0 = diagPi ϖ' h'0 * diagU1 K v u := by
    apply Units.ext; ext i j
    rw [Units.val_mul, coe_diagPi, coe_diagPi, coe_diagU1]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu']
  have h2 : localRepInf ϖK hK0 = localRepInf ϖ' h'0 * diag1U K v u := by
    apply Units.ext; ext i j
    rw [Units.val_mul, coe_localRepInf, coe_localRepInf, coe_diag1U]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu']
  have c1 : Commute (diagPi ϖ' h'0) (diagU1 K v u) :=
    commute_of_diag K v (by simp [coe_diagPi]) (by simp [coe_diagPi]) (by simp) (by simp)
  have c2 : Commute (localRepInf ϖ' h'0) (diag1U K v u) :=
    commute_of_diag K v (by simp [coe_localRepInf]) (by simp [coe_localRepInf]) (by simp) (by simp)
  have c3 : Commute (diagU1 K v u) (localRepInf ϖ' h'0) :=
    commute_of_diag K v (by simp) (by simp) (by simp [coe_localRepInf]) (by simp [coe_localRepInf])
  have c4 : Commute (diagU1 K v u) (diag1U K v u) :=
    commute_of_diag K v (by simp) (by simp) (by simp) (by simp)
  rw [h1, h2, c1.mul_zpow, c2.mul_zpow]
  have : diagPi ϖ' h'0 ^ a * diagU1 K v u ^ a * (localRepInf ϖ' h'0 ^ b * diag1U K v u ^ b) =
      diagPi ϖ' h'0 ^ a * localRepInf ϖ' h'0 ^ b * (diagU1 K v u ^ a * diag1U K v u ^ b) := by
    rw [mul_assoc, ← mul_assoc (diagU1 K v u ^ a), (c3.zpow_zpow a b).eq, mul_assoc, mul_assoc]
  rw [this]
  exact doubleCoset_mul_right_of_mem ((integralSubgroup Ov Fv).mul_mem
    ((integralSubgroup Ov Fv).zpow_mem (diagU1_mem K v u) a) ((integralSubgroup Ov Fv).zpow_mem (diag1U_mem K v u) b))

theorem sum_indicator_eq_walk (ϖ₀ : Ov) (hirr : Irreducible ϖ₀) (h0 : algebraMap Ov Fv ϖ₀ ≠ 0)
    {m : ℕ} (r : Fin m → GL (Fin 2) Fv) (hr : IsHeckeCosetSystem (integralSubgroup Ov Fv) (diagPi ϖ₀ h0) r)
    (Z : GL (Fin 2) Fv) (hZ : (Z : Matrix (Fin 2) (Fin 2) Fv) = algebraMap Ov Fv ϖ₀ • (1 : Matrix (Fin 2) (Fin 2) Fv))
    (k j : ℕ) (x : GL (Fin 2) Fv) (a b : ℤ)
    (hx : (Z ^ j)⁻¹ * x ∈ HeckePair.doubleCoset (integralSubgroup Ov Fv) (diagPi ϖ₀ h0 ^ a * localRepInf ϖ₀ h0 ^ b)) :
    ∑ ι : Fin k → Fin m, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => r (ι i)).prod * Z ^ j)⁻¹ * x) =
      ((if a + b = (k : ℤ) then W (Nat.card (Ov ⧸ Ideal.span {ϖ₀})) k (a - b).natAbs else 0 : ℕ) : ℂ) := by
  classical
  haveI : Finite (Ov ⧸ Ideal.span {ϖ₀}) := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).1 hirr]
    exact (inferInstance : Finite (IsLocalRing.ResidueField Ov))

  have hZeq : Z = scalarGL K v (Units.mk0 _ h0) := eq_scalarGL_of_coe K v h0 hZ
  have hcomm : ∀ g : GL (Fin 2) Fv, Commute (Z ^ j)⁻¹ g := fun g => by
    rw [hZeq, ← map_pow, ← map_inv]; exact scalarGL_comm K v _ g
  have hterm : ∀ ι : Fin k → Fin m,
      ((List.ofFn fun i => r (ι i)).prod * Z ^ j)⁻¹ * x = ((List.ofFn fun i => r (ι i)).prod)⁻¹ * ((Z ^ j)⁻¹ * x) := by
    intro ι
    rw [mul_inv_rev, (hcomm _).eq, mul_assoc]
  simp_rw [hterm, ← coe_integralSubgroup_eq_localIntegralSet K v]
  have hcast : ∀ g : GL (Fin 2) Fv,
      ((integralSubgroup Ov Fv : Subgroup (GL (Fin 2) Fv)) : Set (GL (Fin 2) Fv)).indicator (fun _ => (1 : ℂ)) g =
        ((((integralSubgroup Ov Fv : Subgroup (GL (Fin 2) Fv)) : Set (GL (Fin 2) Fv)).indicator (fun _ => (1 : ℕ)) g : ℕ) : ℂ) := by
    intro g; simp only [Set.indicator_apply]; split_ifs <;> simp
  simp_rw [hcast]
  rw [← Nat.cast_sum]
  congr 1
  exact LocalGL2.sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow ϖ₀ h0 hirr r hr
    (W (Nat.card (Ov ⧸ Ideal.span {ϖ₀}))) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) k a b _ hx

end Walk

section Main

open AutomorphicForm

set_option maxHeartbeats 3200000 in
theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hsplit : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = 1)
    (ϖ : (ws v).1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) ((ws v).1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))

    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)

    (e : (ws v).1.adicCompletion L ≃+* v.adicCompletion K)
    (he : ∀ x : (ws v).1.adicCompletion L, Valued.v (e x) = Valued.v x) :
    (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
          SatakeCombination.slotCoeff K L ws v k j r *
            ∑ ι : Fin (r 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (r 1))⁻¹ * x)) =
      fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            ((Matrix.GeneralLinearGroup.map e.toRingHom ((List.ofFn fun m => rL (ι m)).prod * z ^ j))⁻¹ * x) := by
  classical

  have hϖ'irr := irreducible_intEquiv K L v (ws v).1 e he hϖ
  have hϖ'0 := algebraMap_intEquiv_ne_zero K L v (ws v).1 e he hϖ0
  set ϖ' : v.adicCompletionIntegers K := intEquiv K L v (ws v).1 e he ϖ with hϖ'def
  set r' : Fin n → GL (Fin 2) (v.adicCompletion K) := fun i => GLe K L v (ws v).1 e (rL i) with hr'def
  have hr' : IsHeckeCosetSystem (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (diagPi ϖ' hϖ'0) r' := by
    have := IsHeckeCosetSystem.map_of_injective (GLe K L v (ws v).1 e) (GLe_injective K L v (ws v).1 e)
      (map_integralSubgroup K L v (ws v).1 e he) hrL
    rwa [GLe_diagPi K L v (ws v).1 e he ϖ hϖ0] at this
  set z' : GL (Fin 2) (v.adicCompletion K) := GLe K L v (ws v).1 e z with hz'def
  have hz' : (z' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    ext i j
    rw [hz'def, GLe_apply, hz, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply,
      hϖ'def, algebraMap_intEquiv]
    split_ifs <;> simp [smul_eq_mul]

  have hn1 := NumberField.eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi L (ws v).1 ϖ hϖ hϖ0 n rL hrL
  have hn2 := NumberField.eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi K v ϖ' hϖ'irr hϖ'0 n r' hr'
  have habs : Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm v.asIdeal := by omega

  set r₀ : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 j with hr₀
  have hslot : SatakeCombination.slotWord K L ws v k j = MvPolynomial.monomial r₀ 1 := by
    show SatakeCombination.univWord (SatakeCombination.slotDeg K L ws v - 1) k j = _
    rw [show SatakeCombination.slotDeg K L ws v = 1 from hsplit]
    show AutomorphicForm.satakePow (1 - 1 + 1) (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) (MvPolynomial.X 1) ^ k *
        ((MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) ^ (1 - 1 + 1)) ^ j = _
    rw [show AutomorphicForm.satakePow (1 - 1 + 1) (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) (MvPolynomial.X 1) =
        MvPolynomial.X 0 from rfl, show (1 - 1 + 1 : ℕ) = 1 from rfl, pow_one,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]
  have hsupp : (SatakeCombination.slotWord K L ws v k j).support = {r₀} := by
    rw [hslot, MvPolynomial.support_monomial, if_neg one_ne_zero]
  have hr₀0 : r₀ 0 = k := by simp [hr₀]
  have hr₀1 : r₀ 1 = j := by simp [hr₀]
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hcoeff : SatakeCombination.slotCoeff K L ws v k j r₀ = 1 := by
    show (SatakeCombination.slotWord K L ws v k j).coeff r₀ * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (r₀ 1) /
        ((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℂ) ^ j = 1
    rw [hslot, MvPolynomial.coeff_monomial, if_pos rfl, hr₀1, habs, one_mul, div_self (pow_ne_zero _ hq0)]

  have hker : ∀ x : GL (Fin 2) (v.adicCompletion K),
      (∑ ι : Fin k → Fin nK, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rK (ι m)).prod * zK ^ j)⁻¹ * x)) =
        ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          ((Matrix.GeneralLinearGroup.map e.toRingHom ((List.ofFn fun m => rL (ι m)).prod * z ^ j))⁻¹ * x) := by
    intro x
    obtain ⟨p, ⟨hab, hyK⟩, -⟩ := LocalGL2.existsUnique_mem_doubleCoset_zpow ϖK hϖK0 hϖK ((zK ^ j)⁻¹ * x)
    rw [sum_indicator_eq_walk K v ϖK hϖK hϖK0 rK hrK zK hzK k j x p.1 p.2 hyK]
    have hmapprod : ∀ ι : Fin k → Fin n,
        Matrix.GeneralLinearGroup.map e.toRingHom ((List.ofFn fun m => rL (ι m)).prod * z ^ j) =
          (List.ofFn fun m => r' (ι m)).prod * z' ^ j := by
      intro ι
      show GLe K L v (ws v).1 e ((List.ofFn fun m => rL (ι m)).prod * z ^ j) = _
      rw [map_mul, map_pow, MonoidHom.map_list_prod, List.map_ofFn]
      rfl
    simp_rw [hmapprod]
    obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible (v.adicCompletionIntegers K) hϖ'irr hϖK
    have hy' : (z' ^ j)⁻¹ * x ∈ HeckePair.doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (diagPi ϖ' hϖ'0 ^ p.1 * localRepInf ϖ' hϖ'0 ^ p.2) := by
      rw [← doubleCoset_eq_of_mul_unit K v ϖ' ϖK hϖ'0 hϖK0 u hu p.1 p.2]
      have hc : (z' ^ j)⁻¹ * x = ((z' ^ j)⁻¹ * zK ^ j) * ((zK ^ j)⁻¹ * x) := by group
      rw [hc]
      refine doubleCoset_mul_left_of_mem ?_ _ hyK
      rw [eq_scalarGL_of_coe K v hϖ'0 hz', eq_scalarGL_of_coe K v hϖK0 hzK, ← map_pow, ← map_pow, ← map_inv, ← map_mul]
      have hunits : (Units.mk0 _ hϖ'0 ^ j)⁻¹ * Units.mk0 _ hϖK0 ^ j =
          (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) :
            v.adicCompletionIntegers K →* v.adicCompletion K) u) ^ j := by
        rw [← inv_pow, ← mul_pow]
        congr 1
        rw [inv_mul_eq_iff_eq_mul]
        apply Units.ext
        rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe, ← map_mul, hu]
      rw [hunits, map_pow]
      exact (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)).pow_mem (scalarGL_mem K v u) j
    rw [sum_indicator_eq_walk K v ϖ' hϖ'irr hϖ'0 r' hr' z' hz' k j x p.1 p.2 hy',
      Ideal.span_singleton_eq_span_singleton.2 ⟨u, hu⟩]

  funext x
  rw [hsupp, Finset.sum_singleton, hcoeff, one_mul, hr₀1]
  have key : ∀ d : ℕ, d = k →
      (∑ ι : Fin d → Fin nK, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rK (ι m)).prod * zK ^ j)⁻¹ * x)) =
        ∑ ι : Fin k → Fin nK, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rK (ι m)).prod * zK ^ j)⁻¹ * x) := by
    rintro d rfl; rfl
  rw [key _ hr₀0]
  exact hker x

end Main

end N3Main
p2m_reactivate "P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one.N3Main"

end
p2m_reactivate "P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one.N3Main"

open N3Main AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hsplit : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = 1)
    (ϖ : (ws v).1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) ((ws v).1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))

    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)

    (e : (ws v).1.adicCompletion L ≃+* v.adicCompletion K)
    (he : ∀ x : (ws v).1.adicCompletion L, Valued.v (e x) = Valued.v x) :
    (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
          SatakeCombination.slotCoeff K L ws v k j r *
            ∑ ι : Fin (r 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (r 1))⁻¹ * x)) =
      fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            ((Matrix.GeneralLinearGroup.map e.toRingHom ((List.ofFn fun m => rL (ι m)).prod * z ^ j))⁻¹ * x) := by
  exact N3Main.main K L v ws hsplit ϖ hϖ hϖ0 n rL hrL z hz ϖK hϖK hϖK0 nK rK hrK zK hzK k j e he

end S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one
end P2MW
export P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one (solution)
