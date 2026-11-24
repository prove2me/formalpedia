-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:23:38.148171+00:00
-- url     : https://prove2.me/theorems/66eb81f2-4925-4725-8f99-a8a7d320e20c
-- title:
--   Exists Reduction
-- statement:
--   Definitions and structural lemmas for Exists Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
structure Red (I : AutInst) (g : ℕ) (Q : Type) [Group Q] where
  toFun : I.Gf → Q
  map_mul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, toFun (x * y) = toFun x * toFun y
  ker : ∀ x ∈ I.Kset, toFun x = 1 ↔ x ∈ I.Kg g
  surj : ∀ q : Q, ∃ x ∈ I.Kset, toFun x = q
def Red.lift {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf)
    (a : MonoidAlgebra ℂ Q) : I.Gf → ℂ := by
  classical
  exact fun x => if x ∈ I.Kset then a.coeff (ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ) else 0
def IsSA {Q : Type} [Group Q] (a : MonoidAlgebra ℂ Q) : Prop := ∀ q : Q, a.coeff q⁻¹ = star (a.coeff q)
def tensAlg {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (a : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun h : ∀ i, G i => ∏ i, (a i).coeff (h i))
def zSet {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] {Lab : ι → Type}
    (z : ∀ i, Lab i → MonoidAlgebra ℂ (G i)) (S : Set (∀ i, Lab i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  ∑ᶠ t ∈ S, tensAlg fun i => z i (t i)
def IsSeries {Q Lab : Type} [Group Q] (z : Lab → MonoidAlgebra ℂ Q) : Prop :=
  (∀ f, z f * z f = z f) ∧ (∀ f a, z f * a = a * z f) ∧ (∀ f f', f ≠ f' → z f * z f' = 0) ∧
    ∃ T : Finset Lab, (∀ f, f ∉ T → z f = 0) ∧ ∑ f ∈ T, z f = 1
def extId (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : Ideal (IntAf I.F I.E) :=
  Ideal.span {z : IntAf I.F I.E | ∃ a ∈ 𝔞, (z : TensorProduct I.F I.E (Af I.F)) = Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E)}
def hAf (I : AutInst) (x y : Fin I.n → TensorProduct I.F I.E (Af I.F)) : TensorProduct I.F I.E (Af I.F) :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) x y
structure PlFrame (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) where
  r : IntAf I.F I.E →+* ZMod p
  r_ker : ∀ (a : 𝓞 I.E) (h : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E),
    r ⟨_, h⟩ = 0 ↔ a ∈ w.asIdeal
  c : I.Lf →ₛₗ[r] (Fin N → ZMod p)
  c_surj : Function.Surjective c
  c_ker : ∀ y : I.Lf, c y = 0 ↔
    (y : Fin I.n → TensorProduct I.F I.E (Af I.F)) ∈ extId I w.asIdeal • I.Lf
abbrev GProd (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type) : Type :=
  ∀ kv : (Σ k : Fin 2, Pl k), GL (Fin N) (ZMod (g kv.1))
def ActsBy {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (fr : ∀ k v, PlFrame I N (g k) (w k v))
    (ρ : I.Gf → GProd N g Pl) : Prop :=
  ∀ x ∈ I.Kset, ∀ (k : Fin 2) (v : Pl k) (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf),
    (fr k v).c ⟨_, h⟩ = ((ρ x ⟨k, v⟩ : GL (Fin N) (ZMod (g k))) : Matrix (Fin N) (Fin N) (ZMod (g k))) *ᵥ (fr k v).c y
def IsConj (I : AutInst) (w w' : HeightOneSpectrum (𝓞 I.E)) : Prop :=
  ∀ a b : 𝓞 I.E, (b : I.E) = star (a : I.E) → (a ∈ w.asIdeal ↔ b ∈ w'.asIdeal)
def IsChoice (I : AutInst) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) : Prop :=
  (∀ k, (g k).Prime) ∧ g 0 ≠ g 1 ∧ (∀ k, (Ideal.span {((g k : ℕ) : 𝓞 I.E)}).IsRadical) ∧
    (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal ∧ Ideal.absNorm (w k v).asIdeal = g k) ∧
    (∀ k, Function.Injective (w k)) ∧ (∀ k v v', ¬ IsConj I (w k v) (w k v')) ∧
    ∀ k (u : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal → ∃ v, u = w k v ∨ IsConj I (w k v) u
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
namespace Inhab
def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype
theorem mulVec_mem {I : AutInst} {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf := (hx y).1 hy
theorem fmat_mul (I : AutInst) (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
theorem fmat_one (I : AutInst) : I.fmat 1 = 1 := rfl
def KgSub (I : AutInst) (g : ℕ) : Subgroup (Ksub I) where
  carrier := {x | (x : I.Gf) ∈ I.Kg g}
  one_mem' := ⟨(Ksub I).one_mem, fun y _ => ⟨0, zero_mem _, by
    rw [OneMemClass.coe_one, fmat_one]; simp⟩⟩
  mul_mem' := by
    rintro x w ⟨hx, hx'⟩ ⟨hw, hw'⟩
    refine ⟨(x * w).2, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := hx' _ (mulVec_mem hw hy)
    obtain ⟨z', hz', e'⟩ := hw' y hy
    refine ⟨z + z', add_mem hz hz', ?_⟩
    rw [smul_add, ← e, ← e', Subgroup.coe_mul, fmat_mul]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, sub_mul, one_mul]
    abel
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨x⁻¹.2, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := hx' _ (mulVec_mem (x⁻¹).2 hy)
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [smul_neg, ← e]
    have h1 : I.fmat x * I.fmat (x⁻¹ : Ksub I) = 1 := by
      rw [← fmat_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, sub_mul, one_mul, h1]
    abel
instance (I : AutInst) (g : ℕ) : (KgSub I g).Normal := ⟨fun x hx k => by
  refine ⟨(k * x * k⁻¹).2, fun y hy => ?_⟩
  obtain ⟨z, hz, e⟩ := hx.2 _ (mulVec_mem (k⁻¹).2 hy)
  refine ⟨I.fmat k *ᵥ z, mulVec_mem k.2 hz, ?_⟩
  have h1 : I.fmat k * I.fmat (k⁻¹ : Ksub I) = 1 := by
    rw [← fmat_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  rw [← Matrix.mulVec_smul, ← e, Subgroup.coe_mul, Subgroup.coe_mul, fmat_mul, fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    h1, mul_assoc, sub_mul, one_mul, mul_sub]⟩
open Classical in

def quotRed (I : AutInst) (g : ℕ) : Red I g (Ksub I ⧸ KgSub I g) where
  toFun x := if h : x ∈ Ksub I then QuotientGroup.mk ⟨x, h⟩ else 1
  map_mul x hx y hy := by
    have hx' : x ∈ Ksub I := hx
    have hy' : y ∈ Ksub I := hy
    rw [dif_pos hx', dif_pos hy', dif_pos (mul_mem hx' hy')]
    rfl
  ker x hx := by
    have hx' : x ∈ Ksub I := hx
    rw [dif_pos hx', QuotientGroup.eq_one_iff]
    rfl
  surj q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, x.2, dif_pos x.2⟩
end Inhab
open Inhab
namespace Red
variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)
def toHom : Ksub I →* Q := MonoidHom.mk' (fun x => ρ.toFun x) fun x y => ρ.map_mul x x.2 y y.2
def quotEquiv : (Ksub I ⧸ KgSub I g) ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq (M := KgSub I g) (N := ρ.toHom.ker)
    (Subgroup.ext fun x : Ksub I => (ρ.ker x x.2).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ.toHom fun q => by
      obtain ⟨x, hx, e⟩ := ρ.surj q
      exact ⟨⟨x, hx⟩, e⟩)
end Red
theorem tensAlg_coeff {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (a : ∀ i, MonoidAlgebra ℂ (G i)) (h : ∀ i, G i) : (tensAlg a).coeff h = ∏ i, (a i).coeff (h i) := rfl
namespace Inhab
section Reduction
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def psi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : 𝓞 E →+* IntAf F E :=
  ((inclE (F := F) (Af F)).comp (algebraMap (𝓞 E) E)).codRestrict _ fun y => adelstab_incl_int y
end Reduction
def latEnd {I : AutInst} {x : I.Gf} (hx : x ∈ I.Kset) : I.Lf →ₗ[IntAf I.F I.E] I.Lf where
  toFun y := ⟨_, mulVec_mem hx y.2⟩
  map_add' y z := Subtype.ext (Matrix.mulVec_add (I.fmat x) y.1 z.1)
  map_smul' a y := Subtype.ext (Matrix.mulVec_smul (I.fmat x) (a : I.E ⊗[I.F] Af I.F) y.1)
end Inhab
namespace PlFrame
variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
theorem r_psi (a : 𝓞 I.E) : fr.r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal := fr.r_ker a _
def residueEquiv : (𝓞 I.E ⧸ w.asIdeal) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (Ideal.ext fun a => (fr.r_psi a).symm)).trans
    (RingHom.quotientKerEquivOfSurjective (f := fr.r.comp (psi I.F I.E)) (ZMod.ringHom_surjective _))
def ActsAs (x : I.Gf) (M : Matrix (Fin N) (Fin N) (ZMod p)) : Prop :=
  ∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = M *ᵥ fr.c y
theorem ActsAs.unique {x : I.Gf} (hx : x ∈ I.Kset) {M M' : Matrix (Fin N) (Fin N) (ZMod p)}
    (h : fr.ActsAs x M) (h' : fr.ActsAs x M') : M = M' := by
  classical
  refine Matrix.toLin'.injective (LinearMap.ext fun t => ?_)
  obtain ⟨y, rfl⟩ := fr.c_surj t
  exact (h y (mulVec_mem hx y.2)).symm.trans (h' y _)
end PlFrame
section Acts
variable {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
  {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (fr : ∀ k v, PlFrame I N (g k) (w k v))
theorem ActsBy.unique {ρ ρ' : I.Gf → GProd N g Pl} (h : ActsBy fr ρ) (h' : ActsBy fr ρ') {x : I.Gf}
    (hx : x ∈ I.Kset) : ρ x = ρ' x :=
  funext fun kv => Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (h x hx kv.1 kv.2) (h' x hx kv.1 kv.2))
end Acts
namespace Inhab
def negOne (I : AutInst) : I.Gf := ⟨-1, by
  show cT (sigR I.cm.sig (Af I.F)) (Units.val (-1 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) * _ *
    Units.val (-1 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = _
  have : cT (sigR I.cm.sig (Af I.F)) (-1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) = -1 := by
    rw [cT, Matrix.map_neg _ (map_neg _), Matrix.transpose_neg]
    exact congrArg Neg.neg (cT_one _)
  rw [Units.val_neg, Units.val_one, this]
  simp⟩
theorem fmat_negOne (I : AutInst) : I.fmat (negOne I) = -1 := rfl
theorem negOne_mem (I : AutInst) : negOne I ∈ I.Kset := fun y => by
  show _ ↔ I.fmat (negOne I) *ᵥ y ∈ I.Lf
  rw [fmat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec, neg_mem_iff]
theorem actsAs_negOne {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) :
    fr.ActsAs (negOne I) (-1) := by
  intro y hy
  rw [Matrix.neg_mulVec, Matrix.one_mulVec, ← map_neg]
  exact congrArg fr.c (Subtype.ext (by
    show I.fmat (negOne I) *ᵥ (y : Fin I.n → _) = -(y : Fin I.n → _)
    rw [fmat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec]))
end Inhab
example {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] :
    tensAlg (fun i => (1 : MonoidAlgebra ℂ (G i))) = 1 := by
  classical
  ext h
  simp only [tensAlg_coeff, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]
example (Q : Type) [Group Q] : IsSeries (fun _ : Unit => (1 : MonoidAlgebra ℂ Q)) :=
  ⟨fun _ => mul_one _, fun _ a => by simp, fun _ _ h => absurd rfl h, {()}, fun _ h => absurd (by simp) h, by simp⟩
example {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type} {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)}
    (fr : ∀ k v, PlFrame I N (g k) (w k v)) (ρ : I.Gf → GProd N g Pl) (h : ActsBy fr ρ) (kv : Σ k, Pl k) :
    ρ (negOne I) kv = -1 :=
  Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) (negOne_mem I) (h _ (negOne_mem I) kv.1 kv.2) (actsAs_negOne _))
end GlobalTheory.RowLev


