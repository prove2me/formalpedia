-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:30.130206+00:00
-- url     : https://prove2.me/theorems/65d7e9bc-fc7c-44cd-aefe-c41bc5ff7f04
-- title:
--   Plane Form Nondegenerate
-- statement:
--   Definitions and structural lemmas for Plane Form Nondegenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace GlobalTheory.Published
@[ext] structure Heisenberg {F W : Type} [Field F] [AddCommGroup W] [Module F W] (B : LinearMap.BilinForm F W) : Type where

  vec : W

  cen : F
namespace Heisenberg
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}
instance : Mul (Heisenberg B) := ⟨fun g h => ⟨g.vec + h.vec, g.cen + h.cen + B g.vec h.vec / 2⟩⟩
instance : One (Heisenberg B) := ⟨⟨0, 0⟩⟩
instance : Inv (Heisenberg B) := ⟨fun g => ⟨-g.vec, -g.cen + B g.vec g.vec / 2⟩⟩
@[simp] theorem mul_vec (g h : Heisenberg B) : (g * h).vec = g.vec + h.vec := rfl
@[simp] theorem mul_cen (g h : Heisenberg B) : (g * h).cen = g.cen + h.cen + B g.vec h.vec / 2 := rfl
@[simp] theorem one_vec : (1 : Heisenberg B).vec = 0 := rfl
@[simp] theorem one_cen : (1 : Heisenberg B).cen = 0 := rfl
@[simp] theorem inv_vec (g : Heisenberg B) : g⁻¹.vec = -g.vec := rfl
@[simp] theorem inv_cen (g : Heisenberg B) : g⁻¹.cen = -g.cen + B g.vec g.vec / 2 := rfl
instance : Group (Heisenberg B) :=
  Group.ofLeftAxioms
    (fun a b c => by ext <;> simp [add_assoc]; ring)
    (fun a => by ext <;> simp)
    (fun a => by ext <;> simp; ring)
instance [TopologicalSpace F] [TopologicalSpace W] : TopologicalSpace (Heisenberg B) :=
  TopologicalSpace.induced (fun g => (g.vec, g.cen)) inferInstance
def IsIrrSmoothOf [TopologicalSpace F] [TopologicalSpace W] (ψ : AddChar F ℂ) {S : Type} [AddCommGroup S] [Module ℂ S]
    (ρ : Representation ℂ (Heisenberg B) S) : Prop :=
  PRep.IsSmooth ρ ∧ ρ.IsIrreducible ∧ ∀ (t : F) (v : S), ρ ⟨0, t⟩ v = ψ t • v
end Heisenberg
def StoneVonNeumann : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
  ∀ (W : Type) [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    (B : LinearMap.BilinForm F W), B.IsAlt → B.Nondegenerate →
  ∀ ψ : AddChar F ℂ, Continuous ψ → ψ ≠ 1 →
    (∃ (S : Type) (_ : AddCommGroup S) (_ : Module ℂ S) (ρ : Representation ℂ (Heisenberg B) S),
      Heisenberg.IsIrrSmoothOf ψ ρ) ∧
    ∀ (S S' : Type) [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S']
      (ρ : Representation ℂ (Heisenberg B) S) (ρ' : Representation ℂ (Heisenberg B) S'),
      Heisenberg.IsIrrSmoothOf ψ ρ → Heisenberg.IsIrrSmoothOf ψ ρ' → Nonempty (ρ.Equiv ρ')
namespace SvN
section Abstract
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
structure Alt (c : W → W → ℂ) : Prop where
  left : ∀ x y z, c (x + y) z = c x z * c y z
  right : ∀ x y z, c x (y + z) = c x y * c x z
  self : ∀ x, c x x = 1
variable {c : W → W → ℂ}
theorem Alt.anti (h : Alt c) (x y : W) : c x y * c y x = 1 := by
  have := h.self (x + y)
  rw [h.left, h.right, h.right, h.self, h.self] at this
  simpa using this
theorem Alt.ne (h : Alt c) (x y : W) : c x y ≠ 0 := left_ne_zero_of_mul_eq_one (h.anti x y)
theorem Alt.zero_left (h : Alt c) (y : W) : c 0 y = 1 := by
  have := h.left 0 0 y
  rw [add_zero] at this
  exact (mul_eq_left₀ (h.ne 0 y)).1 this.symm
theorem Alt.zero_right (h : Alt c) (y : W) : c y 0 = 1 := by
  have := h.anti y 0
  rwa [h.zero_left, mul_one] at this
def Alt.perp (h : Alt c) (T : Set W) : AddSubgroup W where
  carrier := {x | ∀ t ∈ T, c x t ^ 2 = 1}
  add_mem' := fun {a b} ha hb t ht => by rw [h.left, mul_pow, ha t ht, hb t ht, mul_one]
  zero_mem' := fun t _ => by rw [h.zero_left, one_pow]
  neg_mem' := fun {a} ha t ht => by
    have := congrArg (· ^ 2) (h.left a (-a) t)
    simpa [mul_pow, ha t ht, h.zero_left] using this.symm
structure Ops (c : W → W → ℂ) (ρ : W → Module.End ℂ M) : Prop where
  zero : ∀ v, ρ 0 v = v
  mul : ∀ x y v, ρ x (ρ y v) = c x y • ρ (x + y) v
variable {ρ : W → Module.End ℂ M}
structure Splits (c : W → W → ℂ) (A : AddSubgroup W) (α : W → ℂ) : Prop where
  ne : ∀ a ∈ A, α a ≠ 0
  mul : ∀ a ∈ A, ∀ b ∈ A, α a * α b = c a b * α (a + b)
variable {A : AddSubgroup W} {α : W → ℂ}
@[ext] structure Tw {A : Type} [AddCommGroup A] (b : A →+ A →+ Additive ℂˣ) (hb : ∀ x y, b x y = b y x) where

  pt : A

  sc : Additive ℂˣ
instance {A : Type} [AddCommGroup A] (b : A →+ A →+ Additive ℂˣ) (hb : ∀ x y, b x y = b y x) : AddCommGroup (Tw b hb) :=
  letI : Add (Tw b hb) := ⟨fun g k => ⟨g.pt + k.pt, g.sc + k.sc + b g.pt k.pt⟩⟩
  letI : Zero (Tw b hb) := ⟨⟨0, 0⟩⟩
  letI : Neg (Tw b hb) := ⟨fun g => ⟨-g.pt, -g.sc + b g.pt g.pt⟩⟩
  { AddGroup.ofLeftAxioms (G := Tw b hb)
      (fun x y z => Tw.ext (add_assoc _ _ _) (by
        show x.sc + y.sc + b x.pt y.pt + z.sc + b (x.pt + y.pt) z.pt = x.sc + (y.sc + z.sc + b y.pt z.pt) + b x.pt (y.pt + z.pt)
        simp only [map_add, AddMonoidHom.add_apply]; abel))
      (fun x => Tw.ext (zero_add _) (by
        show 0 + x.sc + b 0 x.pt = x.sc
        simp))
      (fun x => Tw.ext (neg_add_cancel _) (by
        show -x.sc + b x.pt x.pt + x.sc + b (-x.pt) x.pt = 0
        simp only [map_neg, AddMonoidHom.neg_apply]; abel)) with
    add_comm := fun x y => Tw.ext (add_comm _ _) (by
      show x.sc + y.sc + b x.pt y.pt = y.sc + x.sc + b y.pt x.pt
      rw [hb, add_comm x.sc]) }
def transl (c : W → W → ℂ) (x : W) : Module.End ℂ (W → ℂ) where
  toFun f z := c z x * f (z + x)
  map_add' f g := by funext z; simp [mul_add]
  map_smul' r f := by funext z; simp; ring
theorem ops_transl (h : Alt c) : Ops c (transl c) where
  zero v := by funext z; simp [transl, h.zero_right]
  mul x y v := by funext z; simp [transl, h.left, h.right, add_assoc]; ring
end Abstract
section Local
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {W : Type} [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem alt_psi (hB : B.IsAlt) (ψ : AddChar F ℂ) : Alt fun x y => ψ (B x y / 2) where
  left x y z := by rw [← AddChar.map_add_eq_mul, ← add_div]; simp
  right x y z := by rw [← AddChar.map_add_eq_mul, ← add_div]; simp
  self x := by rw [hB.self_eq_zero]; simp
variable [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
end Local
section Group
open Heisenberg
variable {F W M : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (Heisenberg B) M}
def funRep (hB : B.IsAlt) (ψ : AddChar F ℂ) : Representation ℂ (Heisenberg B) (W → ℂ) where
  toFun g := ψ g.cen • transl (fun x y => ψ (B x y / 2)) g.vec
  map_one' := LinearMap.ext fun v => by simp [(ops_transl (alt_psi hB ψ)).zero]
  map_mul' g k := LinearMap.ext fun v => by
    simp only [mul_cen, mul_vec, AddChar.map_add_eq_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
      (ops_transl (alt_psi hB ψ)).mul, smul_smul]
    congr 1; ring
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [TopologicalSpace W]
  [IsModuleTopology F W]
variable (hB : B.IsAlt) {A : AddSubgroup W} {α : W → ℂ} (hα : Splits (fun x y => ψ (B x y / 2)) A α)
  (hA : (alt_psi hB ψ).perp A ≤ A) (h1 : ∀ᶠ u in 𝓝 (0 : W), u ∈ A ∧ α u = 1)
  (h2 : ∀ N ∈ 𝓝 (0 : W), ∃ T, ((alt_psi hB ψ).perp T : Set W) ⊆ N ∧ Finite (A ⧸ ((alt_psi hB ψ).perp T).addSubgroupOf A))
  (h3 : ∀ w, ∀ᶠ u in 𝓝 (0 : W), ψ (B u w / 2) ^ 2 = 1)
end Group
end SvN
namespace SvN
open ValuativeRel
def planeForm (F : Type) [Field F] : LinearMap.BilinForm F (F × F) :=
  LinearMap.mk₂ F (fun x y => x.1 * y.2 - x.2 * y.1) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
end SvN
end GlobalTheory.Published
end


