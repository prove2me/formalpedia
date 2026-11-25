-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:18.51183+00:00
-- url     : https://prove2.me/theorems/a0d8684c-c407-57f7-b69c-45e24048a444
-- title:
--   Is Primitive Root Arc Root
-- statement:
--   Definitions and structural lemmas for Is Primitive Root Arc Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/IsPrimitiveRootArcRoot.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Theorems.Thm_GlobalTheory_HostModel_exists_roots
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_HostModel_trForm_adj
import Theorems.Thm_GlobalTheory_HostModel_trForm_pos
import Theorems.Thm_GlobalTheory_HostModel_trForm_symm
import Theorems.Thm_GlobalTheory_ToricData_gtAct_pt
import Theorems.Thm_GlobalTheory_ToricData_hom_eq_iff
import Theorems.Thm_GlobalTheory_ToricData_isAdd_pt
import Theorems.Thm_GlobalTheory_ToricData_isIota_pt
import Theorems.Thm_GlobalTheory_ToricData_isNsmul_pt
import Theorems.Thm_GlobalTheory_ToricData_lieMult_zero
import Theorems.Thm_GlobalTheory_ToricData_psiUnitOn
import Theorems.Thm_GlobalTheory_ToricData_psi_weight_zero_linear_combination
import Theorems.Thm_GlobalTheory_ToricData_qkExt_pt
import Theorems.Thm_GlobalTheory_ToricData_weilQkIs_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q


set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData
section RootChar
variable {X G : Type} [AddCommGroup X] [CommGroup G]
def rootChar (ζ : G) (f : X →ₗ[ℤ] ℤ) : Multiplicative X →* G :=
  (zpowersHom G ζ).comp (AddMonoidHom.toMultiplicative f.toAddMonoidHom)
@[simp] theorem rootChar_apply (ζ : G) (f : X →ₗ[ℤ] ℤ) (χ : X) :
    rootChar ζ f (Multiplicative.ofAdd χ) = ζ ^ f χ := rfl
theorem rootChar_add (ζ : G) (f g : X →ₗ[ℤ] ℤ) : rootChar ζ (f + g) = rootChar ζ f * rootChar ζ g :=
  MonoidHom.ext fun χ => zpow_add ζ (f χ.toAdd) (g χ.toAdd)
theorem rootChar_pow (ζ : G) (f : X →ₗ[ℤ] ℤ) (m : ℕ) : rootChar (ζ ^ m) f = rootChar ζ f ^ m :=
  MonoidHom.ext fun χ => by
    change (ζ ^ m) ^ f χ.toAdd = (ζ ^ f χ.toAdd) ^ m
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
theorem rootChar_pow_eq_one {ζ : G} {n : ℕ} (h : ζ ^ n = 1) (f : X →ₗ[ℤ] ℤ) : rootChar ζ f ^ n = 1 := by
  rw [← rootChar_pow, h]
  exact MonoidHom.ext fun _ => one_zpow _
theorem rootChar_eq_iff {ζ : G} {n : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) (f g : X →ₗ[ℤ] ℤ) :
    rootChar ζ f = rootChar ζ g ↔ ∃ e, f = g + n • e := by
  constructor
  · intro H
    have hd : ∀ χ, (n : ℤ) ∣ f χ - g χ := fun χ => by
      rw [← h.zpow_eq_one_iff_dvd, zpow_sub, mul_inv_eq_one]
      exact DFunLike.congr_fun H (Multiplicative.ofAdd χ)
    choose e he using hd
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨(AddMonoidHom.mk' e fun a b => mul_left_cancel₀ hn' ?_).toIntLinearMap, LinearMap.ext fun χ => ?_⟩
    · rw [mul_add, ← he, ← he, ← he, map_add, map_add]
      ring
    · change f χ = g χ + n • e χ
      rw [nsmul_eq_mul, ← he]
      ring
  · rintro ⟨e, rfl⟩
    refine MonoidHom.ext fun χ => ?_
    change ζ ^ (g χ.toAdd + n • e χ.toAdd) = ζ ^ g χ.toAdd
    rw [zpow_add, nsmul_eq_mul, zpow_mul, zpow_natCast, h.pow_eq_one, one_zpow, mul_one]
theorem exists_rootChar_eq [Module.Free ℤ X] {F : Type} [CommRing F] [IsDomain F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (h : IsPrimitiveRoot ζ n) (t : Multiplicative X →* Fˣ) (ht : t ^ n = 1) : ∃ f, rootChar ζ f = t := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let b := Module.Free.chooseBasis ℤ X
  have hi : ∀ i, ∃ m : ℕ, ζ ^ m = t (Multiplicative.ofAdd (b i)) := fun i => by
    obtain ⟨m, -, hm⟩ := h.eq_pow_of_mem_rootsOfUnity (ξ := t (Multiplicative.ofAdd (b i)))
      ((mem_rootsOfUnity _ _).2 (DFunLike.congr_fun ht _))
    exact ⟨m, hm⟩
  choose m hm using hi
  refine ⟨b.constr ℤ fun i => (m i : ℤ), ?_⟩
  apply MonoidHom.toAdditiveRight.injective
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun i => ?_
  change Additive.ofMul (ζ ^ b.constr ℤ (fun i => (m i : ℤ)) (b i)) = Additive.ofMul (t (Multiplicative.ofAdd (b i)))
  rw [b.constr_basis, zpow_natCast, hm]
end RootChar
section Split
variable (K : Type) [CommRing K] [IsDomain K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
abbrev splitPre : DegPre K := toricPre K X fun _ => 1
variable {X}
omit [IsDomain K] [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem polar_one (a b : X) : polar (K := K) (fun _ : X => 1) a b = 1 := by simp [polar]
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem polar_one_smul {O : Type} [Ring O] [StarRing O] [Module O X] (a : O) (y z : X) :
    polar (K := K) (fun _ : X => 1) (a • y) z = polar (K := K) (fun _ : X => 1) y (star a • z) :=
  (polar_one K _ _).trans (polar_one K _ _).symm
variable (X) in

def splitOAct (O : Type) [Ring O] [StarRing O] [Module O X] : (splitPre K X).OAct O :=
  toricOAct _ O (polar_one_smul K)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]
theorem isIota_split (y : X) (t : Multiplicative X →* Fˣ) :
    GtPtF.IsIota (D := splitPre K X) y (pt _ F t) ↔ t = 1 := by
  rw [isIota_pt, ← hom_eq_iff]
  simp [polar_one]
def splitPt {n : ℕ} (y : X) (t : Multiplicative X →* Fˣ) (ht : t ^ n = 1) : QkPt (splitPre K X) F n :=
  ⟨y, pt _ F t, pt _ F 1, (isNsmul_pt _ F n t 1).2 ht.symm, (isIota_split K F y 1).2 rfl⟩
@[simp] theorem splitPt_y {n : ℕ} (y : X) (t : Multiplicative X →* Fˣ) (ht : t ^ n = 1) :
    (splitPt K F y t ht).y = y := rfl
@[simp] theorem splitPt_g {n : ℕ} (y : X) (t : Multiplicative X →* Fˣ) (ht : t ^ n = 1) :
    (splitPt K F y t ht).g = pt _ F t := rfl
theorem exists_eq_splitPt {n : ℕ} (p : QkPt (splitPre K X) F n) : ∃ y t ht, p = splitPt K F y t ht := by
  obtain ⟨y, g, h, hn, hi⟩ := p
  obtain ⟨t, rfl⟩ := (pt_bijective _ F).2 g
  obtain ⟨u, rfl⟩ := (pt_bijective _ F).2 h
  exact ⟨y, t, ((isNsmul_pt _ F n t u).1 hn).symm.trans ((isIota_split K F y u).1 hi), rfl⟩
theorem equiv_splitPt {n : ℕ} (y y' : X) (t t' : Multiplicative X →* Fˣ) (ht : t ^ n = 1) (ht' : t' ^ n = 1) :
    QkPt.Equiv _ F (splitPt K F y t ht) (splitPt K F y' t' ht') ↔ (∃ z, y' = y + n • z) ∧ t' = t := by
  constructor
  · rintro ⟨z, hz, h, hi, ha⟩
    obtain ⟨u, rfl⟩ := (pt_bijective _ F).2 h
    obtain rfl := (isIota_split K F z u).1 hi
    exact ⟨⟨z, hz⟩, ((isAdd_pt _ F t 1 t').1 ha).trans (mul_one t)⟩
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact ⟨z, hz, pt _ F 1, (isIota_split K F z 1).2 rfl, (isAdd_pt _ F _ 1 _).2 (mul_one _).symm⟩
theorem equiv_refl_split {n : ℕ} (p : QkPt (splitPre K X) F n) : QkPt.Equiv _ F p p := by
  obtain ⟨y, t, ht, rfl⟩ := exists_eq_splitPt K F p
  exact (equiv_splitPt K F y y t t ht ht).2 ⟨⟨0, by simp⟩, rfl⟩
end Split
end GlobalTheory.ToricData
namespace GlobalTheory.HostModel
open ToricData ConjDual
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
section Tate
variable (H : Host E) (K : Type) [CommRing K] [IsDomain K] (F : Type) [Field F] [Algebra (FractionRing K) F]
def arcAct : letI := H.starRing; (splitPre K (𝓞 E)).OAct (𝓞 E) :=
  letI := H.starRing; splitOAct K (𝓞 E) (𝓞 E)
variable {H F}
def qkPt {n : ℕ} (ζ : Fˣ) (hζ : ζ ^ n = 1) (a : HypLattice H) : QkPt (splitPre K (𝓞 E)) F n :=
  splitPt K F a.1 (rootChar ζ (toDual H a.2)) (rootChar_pow_eq_one hζ _)
variable {n : ℕ} (ζ : Fˣ) (hζ : ζ ^ n = 1)
@[simp] theorem qkPt_y (a : HypLattice H) : (qkPt K ζ hζ a).y = a.1 := rfl
@[simp] theorem qkPt_g (a : HypLattice H) : (qkPt K ζ hζ a).g = pt _ F (rootChar ζ (toDual H a.2)) := rfl
theorem qkAdd_qkPt (a b : HypLattice H) : QkAdd (qkPt K ζ hζ a) (qkPt K ζ hζ b) (qkPt K ζ hζ (a + b)) :=
  ⟨qkPt K ζ hζ (a + b), rfl, (isAdd_pt _ F _ _ _).2 (rootChar_add ζ (toDual H a.2) (toDual H b.2)),
    equiv_refl_split K F _⟩
theorem qkAct_qkPt (x : 𝓞 E) (a : HypLattice H) :
    letI := H.starRing; QkAct (arcAct H K) x (qkPt K ζ hζ a) (qkPt K ζ hζ (x • a)) :=
  letI := H.starRing
  ⟨qkPt K ζ hζ (x • a), rfl, (gtAct_pt _ F (𝓞 E) (polar_one_smul K) x _ _).2 fun _ => rfl, equiv_refl_split K F _⟩
theorem weilQkIs_qkPt (a b : HypLattice H) :
    WeilQkIs _ F n (qkPt K ζ hζ a) (qkPt K ζ hζ b) ((ζ ^ hypForm H a b : Fˣ) : F) := by
  rw [hypForm_apply, zpow_sub]
  exact weilQkIs_pt _ F (qkPt K ζ hζ a) (qkPt K ζ hζ b) _ _ rfl rfl
theorem isNsmul_qkPt {n' m : ℕ} {ζ' : Fˣ} (hζ' : ζ' ^ n' = 1) (h : ζ ^ m = ζ') (a : HypLattice H) :
    GtPtF.IsNsmul m (qkPt K ζ hζ a).g (qkPt K ζ' hζ' a).g :=
  (isNsmul_pt _ F m _ _).2 (h ▸ rootChar_pow ζ _ m)
variable {ζ}
theorem equiv_qkPt (hn : 0 < n) (h : IsPrimitiveRoot ζ n) (a b : HypLattice H) :
    QkPt.Equiv _ F (qkPt K ζ hζ a) (qkPt K ζ hζ b) ↔ ∃ e, a = b + n • e := by
  rw [qkPt, qkPt, equiv_splitPt, eq_comm (b := rootChar ζ (toDual H a.2)), rootChar_eq_iff hn h]
  constructor
  · rintro ⟨⟨z, hz⟩, e, he⟩
    refine ⟨(-z, (toDual H).symm e), Prod.ext ?_ ((toDual H).injective ?_)⟩
    · simp [hz]
    · simpa using he
  · rintro ⟨e, rfl⟩
    exact ⟨⟨-e.1, by simp⟩, toDual H e.2, by simp⟩
theorem exists_qkPt_eq (hn : 0 < n) (h : IsPrimitiveRoot ζ n) (p : QkPt (splitPre K (𝓞 E)) F n) :
    ∃ a : HypLattice H, qkPt K ζ hζ a = p := by
  obtain ⟨y, t, ht, rfl⟩ := exists_eq_splitPt K F p
  obtain ⟨f, rfl⟩ := exists_rootChar_eq hn h t ht
  exact ⟨(y, (toDual H).symm f), rfl⟩
theorem qkExt_qkPt {F' : Type} [Field F'] [Algebra (FractionRing K) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing K) F) = algebraMap (FractionRing K) F') {ζ' : F'ˣ} (hζ' : ζ' ^ n = 1)
    (h : (ζ' : F') = f ζ) (a : HypLattice H) (q : QkPt (splitPre K (𝓞 E)) F' n) :
    QkExt f (qkPt K ζ hζ a) q ↔ q = qkPt K ζ' hζ' a := by
  obtain ⟨y, t, ht, rfl⟩ := exists_eq_splitPt K F' q
  have key : (∀ χ, (t χ : F') = f (rootChar ζ (toDual H a.2) χ)) ↔ t = rootChar ζ' (toDual H a.2) := by
    rw [MonoidHom.ext_iff]
    refine forall_congr' fun χ => ?_
    change (t χ : F') = f (ζ ^ toDual H a.2 χ.toAdd : Fˣ) ↔ t χ = ζ' ^ toDual H a.2 χ.toAdd
    rw [Units.ext_iff, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, h]
  rw [qkExt_pt _ F f hf (qkPt K ζ hζ a) (splitPt K F' y t ht) _ _ rfl rfl, key]
  constructor
  · rintro ⟨hy, rfl⟩
    obtain rfl : y = a.1 := hy
    rfl
  · exact fun e => ⟨congrArg QkPt.y e, (pt_bijective _ F').1 (congrArg QkPt.g e)⟩
omit [Algebra (FractionRing K) F] in

theorem pow_eq_one_of_prim {ζ : ℕ → Fˣ} (h : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (n : ℕ) : ζ n ^ n = 1 :=
  n.eq_zero_or_pos.elim (fun e => by rw [e, pow_zero]) fun hn => (h n hn).pow_eq_one
variable (H) in

def tateIsoQ (ζ : ℕ → Fˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n)
    (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) :
    TateIsoQ (hypDatum H) (splitPre K (𝓞 E)) (arcAct H K) F where
  ζ := ζ
  ζ_prim := hp
  ζ_pow := hc
  ev n := qkPt K (ζ n) (pow_eq_one_of_prim hp n)
  add _ _ := qkAdd_qkPt K _ _
  lin _ _ := qkAct_qkPt K _ _
  ker n hn := equiv_qkPt K _ hn (hp n hn)
  onto n hn p := by
    obtain ⟨a, rfl⟩ := exists_qkPt_eq (H := H) K (pow_eq_one_of_prim hp n) hn (hp n hn) p
    exact ⟨a, equiv_refl_split K F _⟩
  tower n m hn hm a :=
    ⟨qkPt K (ζ n) (pow_eq_one_of_prim hp n) a, rfl, isNsmul_qkPt K _ _ _ (hc n m hn hm) a, equiv_refl_split K F _⟩
  isom _ _ := weilQkIs_qkPt K _ _
@[simp] theorem tateIsoQ_ζ (ζ : ℕ → Fˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n)
    (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) : (tateIsoQ H K ζ hp hc).ζ = ζ := rfl
@[simp] theorem tateIsoQ_ev (ζ : ℕ → Fˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n)
    (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) (n : ℕ) (a : HypLattice H) :
    (tateIsoQ H K ζ hp hc).ev n a = qkPt K (ζ n) (pow_eq_one_of_prim hp n) a := rfl
end Tate
variable {H : Host E} {l : Level H} (c : Coeff l) (k : Type) [CommRing k] [IsDomain k] (bF : c.F →+* k)
def arcRoot {a : ℕ} (h : a ∣ l.M') : (FractionRing k)ˣ :=
  Units.map ((algebraMap k (FractionRing k)).comp bF).toMonoidHom
    (Units.mk0 ⟨zeta a, zeta_mem_coeff_of_dvd c h⟩ fun e => Complex.exp_ne_zero _ (congrArg Subtype.val e))
theorem isPrimitiveRoot_arcRoot {a : ℕ} (h : a ∣ l.M') : IsPrimitiveRoot (arcRoot c k bF h) a := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have h1 : IsPrimitiveRoot (⟨zeta a, zeta_mem_coeff_of_dvd c h⟩ : c.F) a :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val)
      (isPrimitiveRoot_zeta (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l))) Subtype.val_injective
  exact h1.map_of_injective ((algebraMap k (FractionRing k)).comp bF).injective
variable (l) in

def arcForm : LinearMap.BilinForm ℤ (𝓞 E) := (2 * l.M' : ℤ) • trForm H
def arcIn : ArcIn (hypDatum H) l (RingHom.id c.F) k bF where
  D₀ := toricPre k (𝓞 E) fun _ => 1
  oa := arcAct H k
  nontriv := inferInstanceAs (Nontrivial (𝓞 E))
  even := psiEven _ fun _ => rfl
  bimult := tauBimult _ fun _ _ _ => by simp [polar_one]
  gen y := psiUnitOn _ y 1 (by simp)
  w0 := letI := H.starRing; psi_weight_zero_linear_combination _ (𝓞 E) (polar_one_smul k) H.w0 fun _ => polar_one k _ _
  be := arcForm l
  be_symm (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
  be_pos (y : 𝓞 E) hy := mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
  be_adj a (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)
  be_dvd (y z : 𝓞 E) := ⟨trForm H y z, rfl⟩
  eta := qkPt k (arcRoot c k bF (Nat.dvd_lcm_left l.M l.A)) (isPrimitiveRoot_arcRoot c k bF _).pow_eq_one
  etaA := qkPt k (arcRoot c k bF (Nat.dvd_lcm_right l.M l.A)) (isPrimitiveRoot_arcRoot c k bF _).pow_eq_one
  geom := by
    letI := H.starRing
    intro F _ _ _ r z _ hz f hf
    refine ⟨fun τ => ⟨0, lieMult_zero _ (𝓞 E) (polar_one_smul k) f τ, ?_⟩, ?_⟩
    · rw [hypDatum_p, hypDatum_q, ite_self, zero_add]
      exact Module.finrank_self (𝓞 E)
    haveI := c.fin
    obtain ⟨ζ, hp, hc, hζ⟩ := exists_roots c.F F (f.comp bF)
    have key : ∀ {n : ℕ} (h : n ∣ l.M') (a : HypLattice H) q,
        QkExt (algebraMap _ F) (qkPt k (arcRoot c k bF h) (isPrimitiveRoot_arcRoot c k bF h).pow_eq_one a) q →
          QkPt.Equiv _ F q ((tateIsoQ H k ζ hp hc).ev n a) := fun {n} h a q hq => by
      rw [qkExt_qkPt k _ (algebraMap (FractionRing k) F) (RingHom.ext fun _ => rfl) (pow_eq_one_of_prim hp n)
        ((hζ n (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l)) ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ rfl).trans
          (by rw [hf]; rfl))] at hq
      subst hq
      exact equiv_refl_split k F _
    exact ⟨tateIsoQ H k ζ hp hc, hζ l.A l.A_pos z hz, key _, fun a _ => key _ a⟩
theorem arcIn_be_apply (y z : 𝓞 E) : (arcIn c k bF).be y z = 2 * l.M' * trForm H y z := rfl
theorem arcIn_eta_equiv_iff (a b : HypLattice H) :
    QkPt.Equiv _ _ ((arcIn c k bF).eta a) ((arcIn c k bF).eta b) ↔ ∃ e, a = b + l.M • e :=
  equiv_qkPt k (isPrimitiveRoot_arcRoot c k bF _).pow_eq_one (lt_of_lt_of_le three_pos l.three_le)
    (isPrimitiveRoot_arcRoot c k bF _) a b
instance instNonemptyArcIn : Nonempty (ArcIn (hypDatum H) l (RingHom.id c.F) k bF) := ⟨arcIn c k bF⟩
example : (arcIn c k bF).be (1 : 𝓞 E) (1 : 𝓞 E) = 2 * l.M' * Module.finrank ℚ E := by
  rw [arcIn_be_apply, trForm_one_one]
example : letI := H.starRing
    Nonempty (TateIsoQ (hypDatum H) (arcIn c k bF).D₀ (arcIn c k bF).oa (AlgebraicClosure (FractionRing k))) := by
  obtain ⟨-, I, -⟩ := (arcIn c k bF).geom (AlgebraicClosure (FractionRing k)) ⟨_, sqrtNegDisc_mem_coeffField c⟩
    ⟨_, zeta_A_mem_coeff c⟩ rfl rfl _ rfl
  exact ⟨I⟩
example : ¬ QkPt.Equiv _ _ ((arcIn c k bF).eta ((1, 0) : HypLattice H)) ((arcIn c k bF).eta (0 : HypLattice H)) := by
  rw [arcIn_eta_equiv_iff]
  rintro ⟨e, he⟩
  have h1 : (1 : 𝓞 E) = l.M • e.1 := by simpa using congrArg Prod.fst he
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℤ (𝓞 E), ∃ x, g x = 1 := by
    let v := RingOfIntegers.basis E
    obtain ⟨i⟩ := v.index_nonempty
    exact ⟨v.coord i, v i, by simp⟩
  obtain ⟨x, hx⟩ := hg
  have h2 : (l.M : ℤ) * g (e.1 * x) = 1 := by
    rw [← nsmul_eq_mul, ← map_nsmul, ← smul_mul_assoc, ← h1, one_mul, hx]
  have h3 := Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg _) h2
  have := l.three_le
  omega
example (f : ConjDual H) (y : 𝓞 E) :
    WeilQkIs _ _ l.M ((arcIn c k bF).eta ((0, f) : HypLattice H)) ((arcIn c k bF).eta ((y, 0) : HypLattice H))
      ((arcRoot c k bF (Nat.dvd_lcm_left l.M l.A) ^ toDual H f y : (FractionRing k)ˣ) : FractionRing k) := by
  have h := weilQkIs_qkPt k (arcRoot c k bF (Nat.dvd_lcm_left l.M l.A))
    (isPrimitiveRoot_arcRoot c k bF _).pow_eq_one ((0, f) : HypLattice H) (y, 0)
  rwa [hypForm_apply, map_zero, sub_zero] at h
example :
    Nonempty (ArcIn (hypDatum host) (level host 5 (by norm_num)) (RingHom.id (coeff _).F) (coeff _).F (RingHom.id _)) ∧
      Nonempty (ArcIn (hypDatum host) (level host 5 (by norm_num)) (RingHom.id (coeff _).F)
        (PowerSeries (coeff _).F) PowerSeries.C) :=
  ⟨inferInstance, inferInstance⟩
end GlobalTheory.HostModel


