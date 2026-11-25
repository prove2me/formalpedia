-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:53.466209+00:00
-- url     : https://prove2.me/theorems/840a6af7-dbda-41f4-8c50-fa757354fc09
-- title:
--   Monodromy Zero Of Weil Deligne Rep Class Iff
-- statement:
--   Definitions and structural lemmas for Monodromy Zero Of Weil Deligne Rep Class Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_IsPurePair_of_equiv
import Theorems.Thm_GlobalTheory_WeilDeligne_aeval_dualMap
import Theorems.Thm_GlobalTheory_WeilDeligne_charpoly_diagEnd
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow_one
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_isNilpotent_shiftEnd
import Theorems.Thm_GlobalTheory_WeilDeligne_isPurePair_diagEnd_shiftEnd
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_diagEnd
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_dualMap
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_map
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_prodMap
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_tensorMap
import Theorems.Thm_GlobalTheory_WeilDeligne_norm_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_add
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_shiftEnd_apply
import Theorems.Thm_GlobalTheory_WeilDeligne_shiftEnd_ne_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_ReciprocityTheory_Gal_isPlaceOver_placeOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
namespace GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
def IsSmooth {h : IsPlaceOver A w} {M : Type*} [Monoid M] (f : Weil h →* M) : Prop :=
  IsOpen {σ : Ine (F := E) A | f (ineIncl h σ) = 1}
theorem IsSmooth.of_open {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    {U : Set (Ine (F := E) A)} (hU : IsOpen U) (h1 : 1 ∈ U)
    (hf : ∀ σ ∈ U, f (ineIncl h σ) = 1) : IsSmooth f :=
  Subgroup.isOpen_of_mem_nhds (f.comp (ineIncl h)).ker (g := 1)
    (Filter.mem_of_superset (hU.mem_nhds h1) hf)
theorem IsSmooth.of_le {h : IsPlaceOver A w} {M M' : Type*} [Monoid M] [Monoid M']
    {f : Weil h →* M} {g : Weil h →* M'} (hf : IsSmooth f) (hg : ∀ σ, f σ = 1 → g σ = 1) :
    IsSmooth g :=
  .of_open hf (by simp) fun _ hσ => hg _ hσ
theorem IsSmooth.of_le₂ {h : IsPlaceOver A w} {M M' M'' : Type*} [Monoid M] [Monoid M']
    [Monoid M''] {f : Weil h →* M} {f' : Weil h →* M'} {g : Weil h →* M''} (hf : IsSmooth f)
    (hf' : IsSmooth f') (hg : ∀ σ, f σ = 1 → f' σ = 1 → g σ = 1) : IsSmooth g :=
  .of_open (hf.inter hf') (by simp) fun _ hσ => hg _ hσ.1 hσ.2
theorem IsSmooth.of_trivial {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    (hf : ∀ σ, f (ineIncl h σ) = 1) : IsSmooth f :=
  .of_open isOpen_univ trivial fun σ _ => hf σ
structure WDRep [IsAlgClosure E Ω] (h : IsPlaceOver A w) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] where

  ρ : Representation ℂ (Weil h) V

  N : End ℂ V
  smooth : IsSmooth ρ
  semisimple : ∀ σ, End.IsSemisimple (ρ σ)
  nilpotent : IsNilpotent N
  comm : ∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)
variable [IsAlgClosure E Ω]
theorem isSmooth_unrChar (h : IsPlaceOver A w) (c : ℂˣ) : IsSmooth (unrChar h c) :=
  .of_trivial fun σ => by simp
namespace WDRep
variable {h : IsPlaceOver A w}
variable {V V' V'' V''' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
  [AddCommGroup V'''] [Module ℂ V'''] [FiniteDimensional ℂ V''']
theorem comm_apply (a : WDRep h V) (σ : Weil h) (v : V) :
    a.ρ σ (a.N v) = ((normV w : ℕ) : ℂ) ^ deg σ • a.N (a.ρ σ v) :=
  LinearMap.congr_fun (a.comm σ) v
def Iso (a : WDRep h V) (b : WDRep h V') : Prop :=
  ∃ e : V ≃ₗ[ℂ] V', (∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) ∧ ∀ v, e (a.N v) = b.N (e v)
theorem Iso.refl (a : WDRep h V) : a.Iso a := ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩
theorem Iso.symm {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : b.Iso a := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e.symm, fun σ v => by simp [e.symm_apply_eq, h1], fun v => by simp [e.symm_apply_eq, h2]⟩
theorem Iso.trans {a : WDRep h V} {b : WDRep h V'} {c : WDRep h V''} (hab : a.Iso b) (hbc : b.Iso c) :
    a.Iso c := by
  obtain ⟨e, h1, h2⟩ := hab
  obtain ⟨e', h1', h2'⟩ := hbc
  exact ⟨e.trans e', fun σ v => by simp [h1, h1'], fun v => by simp [h2, h2']⟩
def transport (a : WDRep h V) (e : V ≃ₗ[ℂ] V') : WDRep h V' where
  ρ := (e.conjAlgEquiv ℂ : End ℂ V →* End ℂ V').comp a.ρ
  N := e.conjAlgEquiv ℂ a.N
  smooth := a.smooth.of_le fun σ hσ => by simp [hσ]
  semisimple σ := isSemisimple_map (e.conjAlgEquiv ℂ : End ℂ V →ₐ[ℂ] End ℂ V') (a.semisimple σ)
  nilpotent := a.nilpotent.map (e.conjAlgEquiv ℂ)
  comm σ := by
    show e.conjAlgEquiv ℂ (a.ρ σ) * _ = _ • (_ * e.conjAlgEquiv ℂ (a.ρ σ))
    rw [← map_mul, a.comm, map_smul, map_mul]
theorem iso_transport (a : WDRep h V) (e : V ≃ₗ[ℂ] V') : a.Iso (a.transport e) :=
  ⟨e, fun σ v => by
    show _ = e.conjAlgEquiv ℂ (a.ρ σ) (e v)
    simp, fun v => by simp [transport]⟩
def sum (a : WDRep h V) (b : WDRep h V') : WDRep h (V × V') where
  ρ := a.ρ.prod b.ρ
  N := a.N.prodMap b.N
  smooth := a.smooth.of_le₂ b.smooth fun σ h1 h2 => by
    show (a.ρ σ).prodMap (b.ρ σ) = 1
    rw [h1, h2]; exact LinearMap.prodMap_one
  semisimple σ := isSemisimple_prodMap (a.semisimple σ) (b.semisimple σ)
  nilpotent := by
    have h1 : ∀ n : ℕ, (a.N.prodMap b.N : End ℂ (V × V')) ^ n = (a.N ^ n).prodMap (b.N ^ n) :=
      fun n => (map_pow (LinearMap.prodMapRingHom ℂ V V') (a.N, b.N) n).symm
    obtain ⟨m, hm⟩ := a.nilpotent
    obtain ⟨n, hn⟩ := b.nilpotent
    exact ⟨m + n, by
      rw [h1, pow_add, hm, zero_mul, pow_add, hn, mul_zero, LinearMap.prodMap_zero]⟩
  comm σ := LinearMap.ext fun v => Prod.ext (a.comm_apply σ v.1) (b.comm_apply σ v.2)
@[simp] theorem sum_ρ (a : WDRep h V) (b : WDRep h V') (σ : Weil h) :
    (a.sum b).ρ σ = (a.ρ σ).prodMap (b.ρ σ) := rfl
@[simp] theorem sum_N (a : WDRep h V) (b : WDRep h V') : (a.sum b).N = a.N.prodMap b.N := rfl
theorem Iso.sum {a : WDRep h V} {a' : WDRep h V'} {b : WDRep h V''} {b' : WDRep h V'''} (ha : a.Iso a')
    (hb : b.Iso b') : (a.sum b).Iso (a'.sum b') := by
  obtain ⟨e, h1, h2⟩ := ha
  obtain ⟨e', h1', h2'⟩ := hb
  exact ⟨e.prodCongr e', fun σ v => Prod.ext (h1 σ v.1) (h1' σ v.2),
    fun v => Prod.ext (h2 v.1) (h2' v.2)⟩
def twist (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WDRep h V where
  ρ := { toFun := fun σ => (χ σ : ℂ) • a.ρ σ
         map_one' := by simp
         map_mul' := fun σ τ => by simp [smul_smul, mul_comm] }
  N := a.N
  smooth := a.smooth.of_le₂ hχ fun σ h1 h2 => by simp [h1, h2]
  semisimple σ := End.IsSemisimple_smul _ (a.semisimple σ)
  nilpotent := a.nilpotent
  comm σ := by
    show ((χ σ : ℂ) • a.ρ σ) * a.N = _ • (a.N * ((χ σ : ℂ) • a.ρ σ))
    rw [smul_mul_assoc, a.comm, mul_smul_comm, smul_comm]
@[simp] theorem twist_ρ (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (σ : Weil h) :
    (a.twist χ hχ).ρ σ = (χ σ : ℂ) • a.ρ σ := rfl
@[simp] theorem twist_N (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    (a.twist χ hχ).N = a.N := rfl
theorem Iso.twist {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (χ : Weil h →* ℂˣ)
    (hχ : IsSmooth χ) : (a.twist χ hχ).Iso (b.twist χ hχ) := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e, fun σ v => by simp [h1], h2⟩
def tw (a : WDRep h V) (s : ℝ) : WDRep h V := a.twist (unrChar h (qPow w s)) (isSmooth_unrChar h _)
@[simp] theorem tw_ρ (a : WDRep h V) (s : ℝ) (σ : Weil h) :
    (a.tw s).ρ σ = (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ deg σ • a.ρ σ := by
  simp [tw]
@[simp] theorem tw_N (a : WDRep h V) (s : ℝ) : (a.tw s).N = a.N := rfl
def tensor (a : WDRep h V) (b : WDRep h V') : WDRep h (V ⊗[ℂ] V') where
  ρ := a.ρ.tprod b.ρ
  N := a.N.rTensor V' + b.N.lTensor V
  smooth := a.smooth.of_le₂ b.smooth fun σ h1 h2 => by
    rw [Representation.tprod_apply, h1, h2, TensorProduct.map_one]
  semisimple σ := isSemisimple_tensorMap (a.semisimple σ) (b.semisimple σ)
  nilpotent := by
    refine Commute.isNilpotent_add ?_ (a.nilpotent.map (End.rTensorAlgHom ℂ V V'))
      (b.nilpotent.map (End.lTensorAlgHom ℂ V' V))
    show _ = _
    ext; simp
  comm σ := by
    ext x y
    simp [a.comm_apply, b.comm_apply, smul_tmul']
@[simp] theorem tensor_ρ (a : WDRep h V) (b : WDRep h V') (σ : Weil h) :
    (a.tensor b).ρ σ = TensorProduct.map (a.ρ σ) (b.ρ σ) := rfl
@[simp] theorem tensor_N (a : WDRep h V) (b : WDRep h V') :
    (a.tensor b).N = a.N.rTensor V' + b.N.lTensor V := rfl
theorem Iso.tensor {a : WDRep h V} {a' : WDRep h V'} {b : WDRep h V''} {b' : WDRep h V'''} (ha : a.Iso a')
    (hb : b.Iso b') : (a.tensor b).Iso (a'.tensor b') := by
  obtain ⟨e, h1, h2⟩ := ha
  obtain ⟨e', h1', h2'⟩ := hb
  refine ⟨TensorProduct.congr e e', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [h1, h1']
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [h2, h2']
    | add x y hx hy => simp only [map_add, hx, hy]
def dual (a : WDRep h V) : WDRep h (Dual ℂ V) where
  ρ := a.ρ.dual
  N := -a.N.dualMap
  smooth := a.smooth.of_le fun σ hσ => by
    have : a.ρ σ⁻¹ = 1 := by
      rw [← one_mul (a.ρ σ⁻¹), ← hσ, ← map_mul, mul_inv_cancel, map_one, hσ]
    ext; simp [Dual.transpose_apply, this]
  semisimple σ := isSemisimple_dualMap (a.semisimple σ⁻¹)
  nilpotent := by
    obtain ⟨n, hn⟩ := a.nilpotent
    refine IsNilpotent.neg ⟨n, ?_⟩
    rw [← aeval_X_pow (R := ℂ), aeval_dualMap, aeval_X_pow, hn]
    ext; simp
  comm σ := by
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
    ext f v
    simp [Dual.transpose_apply, a.comm_apply, zpow_ne_zero _ hq]
@[simp] theorem dual_ρ (a : WDRep h V) (σ : Weil h) : a.dual.ρ σ = (a.ρ σ⁻¹).dualMap := rfl
@[simp] theorem dual_N (a : WDRep h V) : a.dual.N = -a.N.dualMap := rfl
theorem Iso.dual {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : a.dual.Iso b.dual := by
  obtain ⟨e, h1, h2⟩ := hab.symm
  exact ⟨e.dualMap, fun σ f => by ext; simp [h1], fun f => by ext; simp [h2]⟩
variable (h) in

def ofChars {ι : Type*} [Finite ι] (χ : ι → Weil h →* ℂˣ) (hχ : ∀ i, IsSmooth (χ i)) :
    WDRep h (ι → ℂ) where
  ρ := { toFun := fun σ => diagEnd fun i => (χ i σ : ℂ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => LinearMap.ext fun v => funext fun i => by simp [mul_assoc] }
  N := 0
  smooth := .of_open (isOpen_iInter_of_finite hχ) (by simp) fun σ hσ =>
    LinearMap.ext fun v => funext fun i => by
      have : χ i (ineIncl h σ) = 1 := Set.mem_iInter.mp hσ i
      simp [this]
  semisimple σ := isSemisimple_diagEnd _
  nilpotent := IsNilpotent.zero
  comm σ := by simp
@[simp] theorem ofChars_ρ {ι : Type*} [Finite ι] (χ : ι → Weil h →* ℂˣ)
    (hχ : ∀ i, IsSmooth (χ i)) (σ : Weil h) :
    (ofChars h χ hχ).ρ σ = diagEnd fun i => (χ i σ : ℂ) := rfl
@[simp] theorem ofChars_N {ι : Type*} [Finite ι] (χ : ι → Weil h →* ℂˣ)
    (hχ : ∀ i, IsSmooth (χ i)) : (ofChars h χ hχ).N = 0 := rfl
variable (h) in

def diag {ι : Type*} [Finite ι] (c : ι → ℂˣ) : WDRep h (ι → ℂ) :=
  ofChars h (fun i => unrChar h (c i)) fun _ => isSmooth_unrChar h _
@[simp] theorem diag_ρ {ι : Type*} [Finite ι] (c : ι → ℂˣ) (σ : Weil h) :
    (diag h c).ρ σ = diagEnd fun i => (c i : ℂ) ^ deg σ := by
  simp [diag]
@[simp] theorem diag_N {ι : Type*} [Finite ι] (c : ι → ℂˣ) : (diag h c).N = 0 := rfl
variable (w) in

def spEig (n : ℕ) (i : Fin n) : ℂˣ := qPow w (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)
variable (h) in

def sp (n : ℕ) : WDRep h (Fin n → ℂ) where
  ρ := (diag h (spEig w n)).ρ
  N := shiftEnd n
  smooth := (diag h _).smooth
  semisimple := (diag h _).semisimple
  nilpotent := isNilpotent_shiftEnd n
  comm σ := LinearMap.ext fun v => funext fun i => by
    simp only [diag_ρ, End.mul_apply, diagEnd_apply, LinearMap.smul_apply, Pi.smul_apply,
      shiftEnd_apply, smul_eq_mul]
    split_ifs with hi
    · have : (spEig w n i : ℂ) = ((normV w : ℕ) : ℂ) * spEig w n ⟨i - 1, by omega⟩ := by
        rw [← coe_qPow_one, spEig, spEig, ← Units.val_mul, ← qPow_add]
        congr 2
        rw [Nat.cast_sub hi]; push_cast; ring
      rw [this, mul_zpow, mul_assoc]
    · simp
@[simp] theorem sp_ρ (n : ℕ) (σ : Weil h) :
    (sp h n).ρ σ = diagEnd fun i => (spEig w n i : ℂ) ^ deg σ := diag_ρ _ _
@[simp] theorem sp_N (n : ℕ) : (sp h n).N = shiftEnd n := rfl
def ofMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Weil h →* GL ι ℂ) (N : Matrix ι ι ℂ)
    (smooth : IsSmooth ρ)
    (semisimple : ∀ σ, End.IsSemisimple (Matrix.toLin' (ρ σ : Matrix ι ι ℂ)))
    (nilpotent : IsNilpotent N)
    (comm : ∀ σ, (ρ σ : Matrix ι ι ℂ) * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) :
    WDRep h (ι → ℂ) where
  ρ := ((Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] End ℂ (ι → ℂ)) :
    Matrix ι ι ℂ →* End ℂ (ι → ℂ)).comp ((Units.coeHom _).comp ρ)
  N := Matrix.toLin' N
  smooth := smooth.of_le fun σ hσ => by simp [hσ]
  semisimple := semisimple
  nilpotent := nilpotent.map (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] End ℂ (ι → ℂ))
  comm σ := by
    have := congrArg (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] End ℂ (ι → ℂ)) (comm σ)
    rw [map_mul, map_smul, map_mul] at this
    exact this
@[simp] theorem ofMatrix_ρ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Weil h →* GL ι ℂ)
    (N : Matrix ι ι ℂ) (h1 h2 h3 h4) (σ : Weil h) :
    (ofMatrix ρ N h1 h2 h3 h4).ρ σ = Matrix.toLin' (ρ σ : Matrix ι ι ℂ) := rfl
@[simp] theorem ofMatrix_N {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Weil h →* GL ι ℂ)
    (N : Matrix ι ι ℂ) (h1 h2 h3 h4) : (ofMatrix ρ N h1 h2 h3 h4).N = Matrix.toLin' N := rfl
def toGL {ι : Type*} [Fintype ι] [DecidableEq ι] (a : WDRep h (ι → ℂ)) : Weil h →* GL ι ℂ :=
  (((LinearMap.toMatrixAlgEquiv' : End ℂ (ι → ℂ) ≃ₐ[ℂ] Matrix ι ι ℂ) :
    End ℂ (ι → ℂ) →* Matrix ι ι ℂ).comp a.ρ).toHomUnits
@[simp] theorem coe_toGL {ι : Type*} [Fintype ι] [DecidableEq ι] (a : WDRep h (ι → ℂ))
    (σ : Weil h) : (a.toGL σ : Matrix ι ι ℂ) = LinearMap.toMatrix' (a.ρ σ) := rfl
def Mono0 (a : WDRep h V) : Prop := a.N = 0
def Unr (a : WDRep h V) : Prop := a.N = 0 ∧ ∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) = 1
def Tempered (a : WDRep h V) : Prop :=
  ∀ φ : Weil h, deg φ = 1 → IsPurePair ((normV w : ℕ) : ℝ) (a.ρ φ) a.N
theorem Iso.finrank_eq {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) :
    finrank ℂ V = finrank ℂ V' := hab.choose.finrank_eq
theorem Iso.charpoly_eq {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (σ : Weil h) :
    (a.ρ σ).charpoly = (b.ρ σ).charpoly := by
  obtain ⟨e, h1, -⟩ := hab
  rw [← LinearEquiv.charpoly_conj e]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply, h1]
theorem Iso.mono0 {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (ha : a.Mono0) : b.Mono0 := by
  obtain ⟨e, -, h2⟩ := hab
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := e.surjective v
  rw [← h2, show a.N = 0 from ha]; simp
theorem Iso.ρ_eq_one {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) {σ : Weil h} (ha : a.ρ σ = 1) :
    b.ρ σ = 1 := by
  obtain ⟨e, h1, -⟩ := hab
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := e.surjective v
  rw [← h1, ha]; simp
theorem Iso.unr {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (ha : a.Unr) : b.Unr :=
  ⟨hab.mono0 ha.1, fun σ => hab.ρ_eq_one (ha.2 σ)⟩
theorem Iso.tempered {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (ha : a.Tempered) :
    b.Tempered := by
  obtain ⟨e, h1, h2⟩ := hab
  exact fun φ hφ => (ha φ hφ).of_equiv e (h1 φ) h2
theorem tempered_sp (n : ℕ) : (sp h n).Tempered := fun φ hφ => by
  rw [sp_ρ, sp_N, hφ]
  refine isPurePair_diagEnd_shiftEnd (by exact_mod_cast one_lt_normV w) _ fun i => ?_
  rw [zpow_one, spEig, norm_qPow]
end WDRep
def isoSetoid (h : IsPlaceOver A w) : Setoid (Σ n : ℕ, WDRep h (Fin n → ℂ)) where
  r a b := a.2.Iso b.2
  iseqv := ⟨fun a => .refl a.2, WDRep.Iso.symm, WDRep.Iso.trans⟩
def WD (h : IsPlaceOver A w) : Type _ := Quotient (isoSetoid h)
namespace WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
def std (a : WDRep h V) : Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  ⟨finrank ℂ V, a.transport (finBasis ℂ V).equivFun⟩
theorem iso_std (a : WDRep h V) : a.Iso (std a).2 := a.iso_transport _
def mk (a : WDRep h V) : WD h := Quotient.mk (isoSetoid h) (std a)
theorem mk_eq_mk {a : WDRep h V} {b : WDRep h V'} : mk a = mk b ↔ a.Iso b := by
  refine Quotient.eq.trans ⟨fun hab => ?_, fun hab => ?_⟩
  · exact ((iso_std a).trans hab).trans (iso_std b).symm
  · exact ((iso_std a).symm.trans hab).trans (iso_std b)
theorem sound {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : mk a = mk b := mk_eq_mk.mpr hab
def lpDim (x : WD h) : ℕ :=
  Quotient.lift (s := isoSetoid h) (fun a => finrank ℂ (Fin a.1 → ℂ))
    (fun _ _ hab => WDRep.Iso.finrank_eq hab) x
def lpSum (x y : WD h) : WD h :=
  Quotient.lift₂ (s₁ := isoSetoid h) (s₂ := isoSetoid h) (fun a b => mk (a.2.sum b.2))
    (fun _ _ _ _ ha hb => sound (WDRep.Iso.sum ha hb)) x y
def lpTwist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => mk (a.2.twist χ hχ))
    (fun _ _ hab => sound (WDRep.Iso.twist hab χ hχ)) x
@[simp] theorem lpTwist_mk (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    lpTwist (mk a) χ hχ = mk (a.twist χ hχ) :=
  sound ((iso_std a).twist χ hχ).symm
def lpTw (x : WD h) (s : ℝ) : WD h := lpTwist x (unrChar h (qPow w s)) (isSmooth_unrChar h _)
@[simp] theorem lpTw_mk (a : WDRep h V) (s : ℝ) : lpTw (mk a) s = mk (a.tw s) := lpTwist_mk _ _ _
def lpChar (x y : WD h) : WD h :=
  Quotient.lift₂ (s₁ := isoSetoid h) (s₂ := isoSetoid h) (fun a b => mk (a.2.tensor b.2))
    (fun _ _ _ _ ha hb => sound (WDRep.Iso.tensor ha hb)) x y
def lpDual (x : WD h) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => mk a.2.dual)
    (fun _ _ hab => sound (WDRep.Iso.dual hab)) x
variable (h) in

def lpZero : WD h := mk (WDRep.diag h (ι := Fin 0) fun i => i.elim0)
variable (h) in

def lpOfChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WD h :=
  mk (WDRep.ofChars h (ι := Fin 1) (fun _ => χ) fun _ => hχ)
open Classical in

def unitOf (z : ℂ) : ℂˣ := if hz : z = 0 then 1 else Units.mk0 z hz
open Classical in
variable (h) in

def lpUnr (m : Multiset ℂ) : WD h := mk (WDRep.diag h fun i : m.ToType => unitOf (i : ℂ))
variable (h) in

def lpSp (n : ℕ) : WD h := mk (WDRep.sp h n)
def mono0 (x : WD h) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.Mono0)
    (fun _ _ hab => propext ⟨WDRep.Iso.mono0 hab, (WDRep.Iso.symm hab).mono0⟩) x
@[simp] theorem monodromyZero_ofWeilDeligneRepClass_iff (a : WDRep h V) : mono0 (mk a) ↔ a.N = 0 :=
  ⟨(iso_std a).symm.mono0, (iso_std a).mono0⟩
def unr (x : WD h) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.Unr)
    (fun _ _ hab => propext ⟨WDRep.Iso.unr hab, (WDRep.Iso.symm hab).unr⟩) x
def tempered (x : WD h) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.Tempered)
    (fun _ _ hab => propext ⟨WDRep.Iso.tempered hab, (WDRep.Iso.symm hab).tempered⟩) x
@[simp] theorem tempered_mk (a : WDRep h V) : tempered (mk a) ↔ a.Tempered :=
  ⟨(iso_std a).symm.tempered, (iso_std a).tempered⟩
def charPol (x : WD h) (σ : Weil h) : ℂ[X] :=
  Quotient.lift (s := isoSetoid h) (fun a => (a.2.ρ σ).charpoly)
    (fun _ _ hab => WDRep.Iso.charpoly_eq hab σ) x
@[simp] theorem charPol_mk (a : WDRep h V) (σ : Weil h) : charPol (mk a) σ = (a.ρ σ).charpoly :=
  ((iso_std a).charpoly_eq σ).symm
def eig (x : WD h) (σ : Weil h) : Multiset ℂ := (charPol x σ).roots
@[simp] theorem eig_mk (a : WDRep h V) (σ : Weil h) : eig (mk a) σ = (a.ρ σ).charpoly.roots := by
  rw [eig, charPol_mk]
def frobEig (x : WD h) : Multiset ℂ := eig x (frob h)
@[simp] theorem frobEig_mk (a : WDRep h V) : frobEig (mk a) = (a.ρ (frob h)).charpoly.roots :=
  eig_mk _ _
open Classical in

def inePol (x : WD h) (σ : G E Ω) : ℂ[X] := if hσ : σ ∈ Weil h then charPol x ⟨σ, hσ⟩ else 1
theorem tempered_lpSp (n : ℕ) : tempered (lpSp h n) := (tempered_mk _).mpr (WDRep.tempered_sp n)
theorem not_mono0_lpSp {n : ℕ} (hn : 2 ≤ n) : ¬ mono0 (lpSp h n) :=
  fun h0 => shiftEnd_ne_zero hn ((monodromyZero_ofWeilDeligneRepClass_iff _).mp h0)
end WD
section Examples
variable (h : IsPlaceOver A w)
example : ((WD.mk (WDRep.diag h fun _ : Fin 1 => 1)).lpTw 1).frobEig = {((normV w : ℕ) : ℂ)} := by
  have : ((WDRep.diag h fun _ : Fin 1 => 1).tw 1).ρ (frob h) =
      diagEnd fun _ => ((normV w : ℕ) : ℂ) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp
  rw [WD.lpTw_mk, WD.frobEig_mk, this, charpoly_diagEnd, Fin.prod_univ_one, roots_X_sub_C]
example : (WD.lpZero h).lpDim = 0 := by simp [WD.lpZero, WD.lpDim, WD.mk, WD.std]
omit [IsAlgClosure E Ω] in

example (v : HeightOneSpectrum (𝓞 E)) : ∃ (B : ValuationSubring (AlgebraicClosure E))
    (hB : IsPlaceOver B v) (x : WD hB), ¬ x.mono0 ∧ x.tempered :=
  ⟨_, isPlaceOver_placeOf _ v, WD.lpSp _ 2, WD.not_mono0_lpSp le_rfl, WD.tempered_lpSp 2⟩
end Examples
end GlobalTheory.WeilDeligne


