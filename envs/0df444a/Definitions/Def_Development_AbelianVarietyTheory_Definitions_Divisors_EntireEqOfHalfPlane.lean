-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:19.74067+00:00
-- url     : https://prove2.me/theorems/d55724d0-ed10-4854-8d20-f4f379e7c85a
-- title:
--   Entire Eq Of Half Plane
-- statement:
--   Definitions and structural lemmas for Entire Eq Of Half Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Theorems.Thm_Formalism_L2_Host_unif_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace GlobalTheory.CMVal
export Neutral.B1 (Ideles)
export Formalism.L2.Host (hcharSub HChar infDiag)
export Formalism.L2.Host.HChar (LevelLe UnrAt val IsUnitary)
open Neutral.B1 (finiteSingle)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)
open Formalism.L2.Host (atFin atInf unif unif_spec IsUnitAt IsUnifAt upF aboveInf)
variable (E : Type) [Field E] [NumberField E]
abbrev Af : Type := FiniteAdeleRing (𝓞 E) E
def finIdele : (Af E)ˣ →* Ideles E :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing E) (Af E))
variable {E}
def finPart (χ : HChar E) : (Af E)ˣ →* ℂˣ := χ.1.comp (finIdele E)
abbrev infPart (χ : HChar E) : Eˣ →* ℂˣ := χ.inf
def single (v : HeightOneSpectrum (𝓞 E)) : (v.adicCompletion E)ˣ →* (Af E)ˣ := Units.map (Neutral.B1.finiteSingle E v)
def SuppAt (v : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : Prop := ∀ w, w ≠ v → (y : Af E) w = 1
def unifAt (v : HeightOneSpectrum (𝓞 E)) : (Af E)ˣ := single v (atFin v (unif v))
def ExpAt (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Prop := ∀ m, χ.LevelLe v m ↔ n ≤ m
def HasInfRatio {I : Type} [Fintype I] (χ : HChar E) (φ : I → E →+* ℂ) (m : I → ℤ) : Prop :=
  χ.HasInf φ (fun i => 2 * m i)
abbrev HasInf {I : Type} [Fintype I] (χ : HChar E) (φ : I → E →+* ℂ) (m : I → ℤ) : Prop := HasInfRatio χ φ m
abbrev TrivOnF (χ : HChar E) : Prop := χ.TrivOn (maximalRealSubfield E)
def hatF : Subring (Af E) := (((maximalRealSubfield E).toSubring).map (algebraMap E (Af E))).topologicalClosure
open Classical in

def eulerFactor (χ : HChar E) (s : ℂ) (v : HeightOneSpectrum (𝓞 E)) : ℂ :=
  if χ.UnrAt v then (1 - (χ.val v : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ else 1
def IsHeckeL (χ : HChar E) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re → HasProd (eulerFactor χ s) (Λ s)
variable (E)
abbrev OF : Type := 𝓞 (maximalRealSubfield E)
variable {E}
def orderC (c : Ideal (OF E)) : Subring E :=
  Subring.closure (Set.range (algebraMap (OF E) E) ∪
    {x | ∃ b ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c, x = algebraMap (𝓞 E) E b})
def hatO (c : Ideal (OF E)) : Subring (Af E) :=
  ((orderC c).map (algebraMap E (Af E))).topologicalClosure
def hatOUnits (c : Ideal (OF E)) : Subgroup (Af E)ˣ := (hatO c).toSubmonoid.units
def lattice (c : Ideal (OF E)) (y : (Af E)ˣ) : Set E :=
  {x | algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO c}
def princ : Subgroup (Af E)ˣ := (Units.map (algebraMap E (Af E)).toMonoidHom).range
abbrev PicO (c : Ideal (OF E)) : Type := (Af E)ˣ ⧸ (princ ⊔ hatOUnits c)
def unitRel : Setoid E where
  r x x' := ∃ u : (OF E)ˣ, x' = algebraMap (OF E) E u * x
  iseqv := ⟨fun x => ⟨1, by simp⟩, fun {x x'} ⟨u, h⟩ => ⟨u⁻¹, by
      rw [h, ← mul_assoc, ← map_mul]; simp⟩,
    fun {x y z} ⟨u, h⟩ ⟨u', h'⟩ => ⟨u' * u, by rw [h', h, ← mul_assoc, ← map_mul]; simp⟩⟩
def modUnits (L : Set E) : Set (Quotient (unitRel (E := E))) := {q | ∃ x ∈ L, x ≠ 0 ∧ Quotient.mk _ x = q}
variable {I : Type} [Fintype I]
def term (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (σ : ℂ) (x : E) : ℂ :=
  ∏ i, ((φ i x)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i * ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * σ))
def IsLatSum (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (L : Set E) (S : ℂ → ℂ) : Prop :=
  Differentiable ℂ S ∧ ∀ σ : ℂ, 1 < (k : ℝ) / 2 + σ.re →
    HasSum (fun q : modUnits L => term φ k κ σ q.1.out) (S σ)
def modF (y : (Af E)ˣ) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))
def IsToricSum (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (T : ℂ) : Prop :=
  Finite (PicO c) ∧ ∃ S : PicO c → ℂ → ℂ, (∀ q, IsLatSum φ (2 * s) κ (lattice c q.out) (S q)) ∧
    T = ∑ᶠ q : PicO c, ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0
def C0 (E : Type) [Field E] [NumberField E] (d k : ℕ) (κ : I → ℕ) : ℝ :=
  Formalism.PairingDivisionLocalBalance.cmConst |(discr (maximalRealSubfield E) : ℝ)| d k κ
def latDisc (Λ : PeriodPair) : ℂ := Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2
def beta (E : Type) [Field E] [NumberField E] (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) (T : ℂ) : ℂ :=
  ((C0 E d (2 * s) κ : ℂ) * T) ^ 12 / latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ
open Classical in

theorem single_apply (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    (single v x : Af E) w = Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) v x w := rfl
@[simp] theorem single_self (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) : (single v x : Af E) v = x := by
  classical
  rw [single_apply]; convert Function.update_self _ _ _
def coord (v : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : (v.adicCompletion E)ˣ where
  val := (y : Af E) v
  inv := (↑y⁻¹ : Af E) v
  val_inv := by
    show ((y : Af E) * (↑y⁻¹ : Af E)) v = 1
    rw [Units.mul_inv]; rfl
  inv_val := by
    show ((↑y⁻¹ : Af E) * (y : Af E)) v = 1
    rw [Units.inv_mul]; rfl
@[simp] theorem coe_coord (v : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) :
    (coord v y : v.adicCompletion E) = (y : Af E) v := rfl
@[simp] theorem finPart_mul (χ χ' : HChar E) (y : (Af E)ˣ) : finPart (χ * χ') y = finPart χ y * finPart χ' y := rfl
@[simp] theorem finPart_inv (χ : HChar E) (y : (Af E)ˣ) : finPart χ⁻¹ y = (finPart χ y)⁻¹ := rfl
theorem mem_orderC {c : Ideal (OF E)} {x : E} : x ∈ orderC c ↔
    ∃ (a : OF E) (b : 𝓞 E), b ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c ∧
      x = algebraMap (OF E) E a + algebraMap (𝓞 E) E b := by
  have hc : ∀ a : OF E, algebraMap (OF E) E a = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a) := fun a => rfl
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
      · exact ⟨a, 0, zero_mem _, by simp⟩
      · exact ⟨0, b, hb, by simp⟩
    | zero => exact ⟨0, 0, zero_mem _, by simp⟩
    | one => exact ⟨1, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      exact ⟨a + a', b + b', add_mem hb hb', by simp only [map_add]; ring⟩
    | neg x _ hx =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      exact ⟨-a, -b, neg_mem hb, by simp only [map_neg]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      refine ⟨a * a', algebraMap (OF E) (𝓞 E) a * b' + (algebraMap (OF E) (𝓞 E) a' + b') * b,
        add_mem (Ideal.mul_mem_left _ _ hb') (Ideal.mul_mem_left _ _ hb), ?_⟩
      simp only [map_add, map_mul, hc]; ring
  · rintro ⟨a, b, hb, rfl⟩
    exact add_mem (Subring.subset_closure (Or.inl ⟨a, rfl⟩)) (Subring.subset_closure (Or.inr ⟨b, hb, rfl⟩))
theorem orderC_mono {c c' : Ideal (OF E)} (h : c' ≤ c) : orderC c' ≤ orderC c := fun _ hx => by
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
  exact mem_orderC.2 ⟨a, b, Ideal.map_mono h hb, rfl⟩
theorem hatO_mono {c c' : Ideal (OF E)} (h : c' ≤ c) : hatO c' ≤ hatO c :=
  closure_mono (Set.image_mono (orderC_mono h))
theorem hatOUnits_mono {c c' : Ideal (OF E)} (h : c' ≤ c) : hatOUnits c' ≤ hatOUnits c :=
  Submonoid.units_mono (fun _ hx => hatO_mono h hx)
def picMap {c c' : Ideal (OF E)} (h : c' ≤ c) : PicO c' →* PicO c :=
  QuotientGroup.map _ _ (MonoidHom.id _) (sup_le_sup_left (hatOUnits_mono h) _)
@[simp] theorem picMap_mk {c c' : Ideal (OF E)} (h : c' ≤ c) (y : (Af E)ˣ) :
    picMap h (QuotientGroup.mk y) = QuotientGroup.mk y := rfl
theorem mem_lattice {c : Ideal (OF E)} {y : (Af E)ˣ} {x : E} :
    x ∈ lattice c y ↔ algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO c := Iff.rfl
def latticeSub (c : Ideal (OF E)) (y : (Af E)ˣ) : AddSubgroup E where
  carrier := lattice c y
  zero_mem' := by simp [lattice]
  add_mem' := fun {a b} ha hb => by
    rw [mem_lattice, map_add, add_mul]; exact add_mem ha hb
  neg_mem' := fun {a} ha => by
    rw [mem_lattice, map_neg, neg_mul]; exact neg_mem ha
example (s : ℂ) (v : HeightOneSpectrum (𝓞 E)) :
    eulerFactor (1 : HChar E) s v = (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  have h : (1 : HChar E).UnrAt v := fun _ _ => rfl
  have h' : (1 : HChar E).val v = 1 := rfl
  simp [eulerFactor, h, h']
example (x : E) : x ∈ orderC (⊤ : Ideal (OF E)) ↔ ∃ b : 𝓞 E, x = algebraMap (𝓞 E) E b := by
  rw [mem_orderC]
  constructor
  · rintro ⟨a, b, -, rfl⟩
    exact ⟨algebraMap (OF E) (𝓞 E) a + b, by rw [map_add]; rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨0, b, by simp [Ideal.map_top], by simp⟩
example (φ : E →+* ℂ) (x : E) (h : φ x = Complex.I) :
    term (fun _ : Unit => φ) 2 (fun _ => 1) 0 x = 1 ∧ term (fun _ : Unit => φ) 2 (fun _ => 0) 0 x = -1 := by
  simp [term, h, pow_succ]
example : Formalism.PairingDivisionLocalBalance.wtM (2 * 1) (fun _ : Unit => 3) = 8 := by decide
end GlobalTheory.CMVal


