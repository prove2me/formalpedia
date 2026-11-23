-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- name    : Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:21.925168+00:00
-- url     : https://prove2.me/theorems/50b9392c-36bc-4a7e-81c8-d3004abb9f5c
-- title:
--   Is Subquotient Det Rep Par Ind
-- statement:
--   Definitions and structural lemmas for Is Subquotient Det Rep Par Ind, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_isUnitarisable_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_normalizer
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_normalizer_lower
import Theorems.Thm_GlobalTheory_SmGL_mem_borel
import Theorems.Thm_GlobalTheory_SmGL_val_diagT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
namespace GlobalTheory.SmGL
section Local
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact_mod_cast MeasureTheory.distribHaarChar_pos
theorem nabs_mul' (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by simp [nabs]
def absPow (s : ℂ) : kˣ →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => ((nabs k x : ℝ) : ℂ) ^ s
      map_one' := by simp [nabs]
      map_mul' := fun x y => by
        rw [nabs_mul', Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (nabs_pos' k x).le (nabs_pos' k y).le] }
theorem val_absPow (s : ℂ) (x : kˣ) : (absPow k s x : ℂ) = ((nabs k x : ℝ) : ℂ) ^ s := rfl
@[simp] theorem absPow_zero : absPow k 0 = 1 := by
  ext x; simp [val_absPow]
def ord (x : kˣ) : ℤ :=
  -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (x : k)))
theorem ord_mul (x y : kˣ) : ord k (x * y) = ord k x + ord k y := by
  simp only [ord, Units.val_mul, map_mul]
  rw [WithZero.log_mul (by simp) (by simp)]
  ring
variable {k} in

theorem ord_eq_zero {x : kˣ} (hx : valuation k (x : k) = 1) : ord k x = 0 := by simp [ord, hx]
def unrChar (α : ℂˣ) : kˣ →* ℂˣ where
  toFun x := α ^ ord k x
  map_one' := by rw [ord_eq_zero (by simp), zpow_zero]
  map_mul' x y := by rw [ord_mul, _root_.zpow_add]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
section Det
variable {R : Type} [CommRing R]
def detChar (n : Type) [Fintype n] [DecidableEq n] (χ : Rˣ →* ℂˣ) : GL n R →* ℂˣ :=
  χ.comp GeneralLinearGroup.det
@[simp] theorem detChar_apply (χ : Rˣ →* ℂˣ) (g : GL n R) :
    detChar n χ g = χ (GeneralLinearGroup.det g) := rfl
def detRep (n : Type) [Fintype n] [DecidableEq n] (χ : Rˣ →* ℂˣ) : Representation ℂ (GL n R) ℂ :=
  ofChar (detChar n χ)
theorem continuous_glDet [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (GeneralLinearGroup.det : GL n R → Rˣ) := by
  refine Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, ?_⟩
  simp only [← map_inv]
  exact Units.continuous_coe_inv.matrix_det
theorem IsSmoothChar.detChar [TopologicalSpace R] [IsTopologicalRing R] {χ : Rˣ →* ℂˣ}
    (h : IsSmoothChar χ) : IsSmoothChar (detChar n χ) :=
  h.comp _ continuous_glDet
def HasCentralChar (π : Representation ℂ (GL n R) V) (ω : Rˣ →* ℂˣ) : Prop :=
  ∀ z v, π (GeneralLinearGroup.scalar n z) v = (ω z : ℂ) • v
def torusChar {n : Type} [Fintype n] (χ : n → Rˣ →* ℂˣ) : (n → Rˣ) →* ℂˣ :=
  ∏ i, (χ i).comp (Pi.evalMonoidHom (fun _ => Rˣ) i)
@[simp] theorem torusChar_apply {n : Type} [Fintype n] (χ : n → Rˣ →* ℂˣ) (t : n → Rˣ) :
    torusChar χ t = ∏ i, χ i (t i) := by
  simp [torusChar, MonoidHom.finsetProd_apply]
end Det
def modExp (m : α → Type) [∀ a, Fintype (m a)] (a : α) : ℤ :=
  (∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)
def modulus (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (g : Levi k m) : ℝ :=
  ∏ a, nabs k (GeneralLinearGroup.det (g a)) ^ modExp m a
def deltaHalf (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] : Levi k m →* ℂˣ :=
  ∏ a, (detChar (m a) (absPow k ((modExp m a : ℂ) / 2))).comp (Pi.evalMonoidHom (fun a => GL (m a) k) a)
variable {k}
abbrev IndSp (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) : Type :=
  smoothPart (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)))
def parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (GL n k) (IndSp e ρ) :=
  smInd (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))
@[simp] theorem parInd_apply (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (g x : GL n k)
    (f : IndSp e ρ) :
    (parInd e ρ g f).1.1 x = f.1.1 (x * g) := rfl
def parIndMap (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V}
    {σ : Representation ℂ (Levi k m) W} (f : ρ.IntertwiningMap σ) :
    (parInd e ρ).IntertwiningMap (parInd e σ) :=
  smIndMap (compMap (twistMap f _) _)
def jacU {R : Type} [CommRing R] (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n R) V) :
    Representation ℂ (Levi R m) (Jacquet π (unipRad R e)) :=
  jacquet π (unipRad R e) (leviEmb R e) (leviEmb_mem_normalizer R e)
def jac (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (Levi k m) (Jacquet π (unipRad k e)) :=
  twist (jacU e π) (deltaHalf k m)⁻¹
def jacMap (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W}
    (f : π.IntertwiningMap τ) : (jac e π).IntertwiningMap (jac e τ) :=
  twistMap (jacquetMap f _ _ _) _
abbrev IndSpLower (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) : Type :=
  smoothPart (ind (parabLower k e) ((twist ρ (deltaHalf k m)⁻¹).comp (leviProjLower k e)))
def parIndLower (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (GL n k) (IndSpLower e ρ) :=
  smInd (parabLower k e) ((twist ρ (deltaHalf k m)⁻¹).comp (leviProjLower k e))
@[simp] theorem parIndLower_apply (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (g x : GL n k) (f : IndSpLower e ρ) : (parIndLower e ρ g f).1.1 x = f.1.1 (x * g) := rfl
def jacLower (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (Levi k m) (Jacquet π (unipRadLower k e)) :=
  twist (jacquet π (unipRadLower k e) (leviEmb k e) (leviEmb_mem_normalizer_lower k e)) (deltaHalf k m)
def multiProd (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :=
  parInd e (piTensor π)
section Two
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
def ind₂ (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :=
  parInd (two e) (ρ.comp (leviTwo k a b).symm.toMonoidHom)
def ind₂Lower (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :=
  parIndLower (two e) (ρ.comp (leviTwo k a b).symm.toMonoidHom)
def jacU₂ (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (GL a k × GL b k) (Jacquet π (unipRad k (two e))) :=
  (jacU (two e) π).comp (leviTwo k a b).toMonoidHom
def jac₂ (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (GL a k × GL b k) (Jacquet π (unipRad k (two e))) :=
  (jac (two e) π).comp (leviTwo k a b).toMonoidHom
def jac₂Lower (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (GL a k × GL b k) (Jacquet π (unipRadLower k (two e))) :=
  (jacLower (two e) π).comp (leviTwo k a b).toMonoidHom
def prod₂ {r t : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :=
  ind₂ (stdSum (rfl : r + t = r + t)) (extTensor π₁ π₂)
end Two
def IsCuspidal (π : Representation ℂ (GL n k) V) : Prop :=
  IsSmooth π ∧ ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n), unipRad k e ≠ ⊥ →
    Subsingleton (Jacquet π (unipRad k e))
def IsCuspSupport (π : Representation ℂ (GL n k) V) {s : ℕ} (d : Fin s → ℕ) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) : Prop :=
  π.IsIrreducible ∧ (∀ a, 0 < d a ∧ (σ a).IsIrreducible ∧ IsCuspidal (σ a)) ∧
    ∃ e : (Σ a, Fin (d a)) ≃ n, IsSubquotient π (multiProd e σ)
def InSupport (π : Representation ℂ (GL n k) V) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n) (a : Fin s), d a = 1 ∧
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (σ : Representation ℂ (Levi k fun a => Fin (d a)) Y),
      σ.IsIrreducible ∧ IsSubquotient σ (jac e π) ∧
        ∀ (g : GL (Fin (d a)) k) (y : Y),
          σ (Pi.mulSingle a g) y = (χ (GeneralLinearGroup.det g) : ℂ) • y
section Borel
variable [LinearOrder n]
def indB (ρ : Representation ℂ (n → kˣ) W) :=
  parInd (points n) (ρ.comp (leviTorus k n).symm.toMonoidHom)
def jacBU (π : Representation ℂ (GL n k) V) : Representation ℂ (n → kˣ) (Jacquet π (unipB k n)) :=
  (jacU (points n) π).comp (leviTorus k n).toMonoidHom
def jacB (π : Representation ℂ (GL n k) V) : Representation ℂ (n → kˣ) (Jacquet π (unipB k n)) :=
  (jac (points n) π).comp (leviTorus k n).toMonoidHom
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem jacBU_mk (π : Representation ℂ (GL n k) V) (t : n → kˣ) (v : V) :
    jacBU π t (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (diagT k n t) v) := rfl
def prinSeries (χ : n → kˣ →* ℂˣ) := indB (ofChar (torusChar χ))
variable (k n)
def iwahori : Subgroup (GL n k) :=
  ((borel 𝓀[k] n).comap (GeneralLinearGroup.map (n := n) (IsLocalRing.residue 𝒪[k]))).map
    (GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k))
def torusO (n : Type) : Subgroup (n → kˣ) where
  carrier := {t | ∀ i, valuation k (t i : k) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro s t hs ht i
    simp [hs i, ht i]
  inv_mem' := by
    intro t ht i
    simp [ht i]
variable {k n}
theorem mem_iwahori {g : GL n k} :
    g ∈ iwahori k n ↔ g ∈ KO k n ∧ ∀ i j, j < i → valuation k ((g : Matrix n n k) i j) < 1 := by
  have key : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, rfl⟩, fun i j hij => (key _).1 ((mem_borel _).1 hh i j hij)⟩
  · rintro ⟨⟨h, rfl⟩, hh⟩
    exact ⟨h, (mem_borel _).2 fun i j hij => (key _).2 (hh i j hij), rfl⟩
theorem diagT_mem_iwahori {t : n → kˣ} (ht : t ∈ torusO k n) : diagT k n t ∈ iwahori k n := by
  let u : n → 𝒪[k]ˣ := fun i => ⟨⟨t i, (ht i).le⟩, ⟨((t i)⁻¹ : kˣ), (inv_mem ht i).le⟩,
    Subtype.ext (t i).mul_inv, Subtype.ext (t i).inv_mul⟩
  refine mem_iwahori.2 ⟨⟨diagT _ n u, ?_⟩, fun i j hij => ?_⟩
  · ext i j
    show algebraMap 𝒪[k] k ((diagT _ n u : Matrix n n 𝒪[k]) i j) = _
    rw [val_diagT, val_diagT, diagonal_apply, diagonal_apply]
    split_ifs
    · rfl
    · simp
  · rw [val_diagT, diagonal_apply_ne _ hij.ne']
    simp
def iwahoriProj (π : Representation ℂ (GL n k) V) :
    fixed π (iwahori k n) →ₗ[ℂ] fixed (jacBU π) (torusO k n) :=
  (twKer π (unipB k n) 1).mkQ.restrict fun v hv t => by
    have h : π (diagT k n t) v = v := by simpa using hv ⟨_, diagT_mem_iwahori t.2⟩
    show jacBU π t (Submodule.Quotient.mk v) = _
    rw [jacBU_mk, h]
    simp
def jacBUFixed (π : Representation ℂ (GL n k) V) :
    Representation ℂ (n → kˣ) (fixed (jacBU π) (torusO k n)) :=
  onFixed (jacBU π) (torusO k n) (MonoidHom.id _) fun _ => by
    rw [Subgroup.normalizer_eq_top]; trivial
def expMult (π : Representation ℂ (GL n k) V) (χ : (n → kˣ) →* ℂˣ) : ℕ∞ :=
  jhMult (ofChar χ) (jacBUFixed π)
omit [LinearOrder n] in

def IsSpherical (π : Representation ℂ (GL n k) V) : Prop := IsSphericalFor π (KO k n)
def HasSatake (π : Representation ℂ (GL n k) V) (α : n → ℂˣ) : Prop :=
  π.IsIrreducible ∧ IsSpherical π ∧ IsSubquotient π (prinSeries fun i => unrChar k (α i))
end Borel
end Local
section Examples
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
def detLevi (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) : Levi k m →* ℂˣ :=
  (detChar n χ).comp (leviEmb k e) * (deltaHalf k m)⁻¹
example (χ : kˣ →* ℂˣ) : HasCentralChar (detRep n χ) (χ ^ Fintype.card n) := fun z v => by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar n z) = z ^ Fintype.card n := by
    ext; simp [GeneralLinearGroup.scalar]
  simp [detRep, this]
example {χ : kˣ →* ℂˣ} (h : IsUnitaryChar χ) : IsUnitarisable (detRep n χ) :=
  (isUnitarisable_ofChar_iff _).2 fun _ => h _
example {G : Type} [Group G] (χ : G →* ℂˣ) : 1 ≤ jhMult (ofChar χ) (ofChar χ) := by
  refine le_iSup₂_of_le 1 ⟨fun _ => ⊤, fun _ => ⊥, fun _ => bot_le,
    fun i j h => absurd (Subsingleton.elim i j) h.ne, fun _ => ⟨.mk ((Submodule.quotEquivOfEqBot _
      (by ext; simp [show (⊥ : Subrepresentation (ofChar χ)).toSubmodule = ⊥ from rfl])).trans
        Submodule.topEquiv) fun g => ?_⟩⟩ le_rfl
  exact Submodule.linearMap_qext _ rfl
end Examples
end GlobalTheory.SmGL


