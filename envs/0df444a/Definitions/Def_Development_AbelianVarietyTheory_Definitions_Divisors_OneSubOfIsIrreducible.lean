-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneSubOfIsIrreducible
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_OneSubOfIsIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:52.324899+00:00
-- url     : https://prove2.me/theorems/bb07731b-bc4e-4eb7-a23b-696b8248f402
-- title:
--   One Sub Of Is Irreducible
-- statement:
--   Definitions and structural lemmas for One Sub Of Is Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneSubOfIsIrreducible.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
namespace GlobalTheory.TypeTwo
section General
variable {G Γ U W : Type} [Group G] [Group Γ] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
def OneSub (X : Representation ℂ G U) : Prop :=
  ∀ S T : Subrepresentation X, IsAtom S → IsAtom T → S = T
def eqMaps (ρ : Representation ℂ (G × Γ) U) (π : Representation ℂ Γ W) : Submodule ℂ (U →ₗ[ℂ] W) where
  carrier := {f | ∀ (h : Γ) (u : U), f (ρ (1, h) u) = π h (f u)}
  add_mem' := by
    intro f f' hf hf' h u
    simp only [LinearMap.add_apply, map_add, hf h u, hf' h u]
  zero_mem' := by intro h u; simp
  smul_mem' := by
    intro c f hf h u
    simp only [LinearMap.smul_apply, map_smul, hf h u]
def homAct (ρ : Representation ℂ (G × Γ) U) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ G (U →ₗ[ℂ] W) where
  toFun g := LinearMap.lcomp ℂ W (ρ (g⁻¹, 1))
  map_one' := by
    ext f u
    show f (ρ ((1 : G)⁻¹, 1) u) = f u
    rw [inv_one, ← Prod.one_eq_mk, map_one]; rfl
  map_mul' a b := by
    ext f u
    show f (ρ ((a * b)⁻¹, 1) u) = f (ρ (b⁻¹, 1) (ρ (a⁻¹, 1) u))
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_rev]
def eqRep (ρ : Representation ℂ (G × Γ) U) (π : Representation ℂ Γ W) : Representation ℂ G (eqMaps ρ π) :=
  sub (homAct ρ W) (eqMaps ρ π) (by
    intro g f hf h u
    show f (ρ (g⁻¹, 1) (ρ (1, h) u)) = π h (f (ρ (g⁻¹, 1) u))
    rw [← hf h, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp)
variable [TopologicalSpace G] [IsTopologicalGroup G]
def homRep (ρ : Representation ℂ (G × Γ) U) (π : Representation ℂ Γ W) :
    Representation ℂ G (smoothPart (eqRep ρ π)) := smoothRep (eqRep ρ π)
end General
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def rkSB (n m j : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) where
  carrier := {Φ | Φ ∈ SB (Matrix (Fin n) (Fin m) k) ∧ ∀ x : Matrix (Fin n) (Fin m) k, x.rank < j → Φ x = 0}
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun x hx => by simp [ha.2 x hx, hb.2 x hx]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun x hx => by simp [hf.2 x hx]⟩
def omAll (n m : ℕ) : Representation ℂ (GL (Fin m) k × GL (Fin n) k) (Matrix (Fin n) (Fin m) k → ℂ) where
  toFun p :=
    { toFun := fun Φ => om 1 p.1 p.2 Φ
      map_add' := fun Φ Ψ => by funext x; simp only [om, Pi.add_apply]; ring
      map_smul' := fun c Φ => by funext x; simp only [om, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := by
    ext Φ x
    simp [om, nabs]
  map_mul' a b := by
    ext Φ x
    have h1 := fun (s : ℝ) (u v : kˣ) => Real.mul_rpow (z := s) (nabs_pos' k u).le (nabs_pos' k v).le
    simp only [om, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, Prod.fst_mul, Prod.snd_mul, map_mul,
      nabs_mul', h1, MonoidHom.one_apply, inv_one, Units.val_one, mul_one, one_mul, mul_inv_rev, Units.val_mul,
      Matrix.mul_assoc, Complex.ofReal_mul]
    ring
def omRk (n m j : ℕ) : Representation ℂ (GL (Fin m) k × GL (Fin n) k) (rkSB k n m j) :=
  sub (omAll k n m) (rkSB k n m j) (by
    intro p Φ hΦ
    refine ⟨Model.om_mem_SB 1 p.1 p.2 hΦ.1, fun x hx => ?_⟩
    have hr : ((p.2⁻¹ : GL (Fin n) k).val * x * p.1.val).rank < j :=
      lt_of_le_of_lt ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)) hx
    show om 1 p.1 p.2 Φ x = 0
    simp only [om, hΦ.2 _ hr, mul_zero])
variable {k}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
abbrev thetaHom {n : ℕ} (m j : ℕ) (π : Representation ℂ (GL (Fin n) k) W) := homRep (omRk k n m j) π
def rkStep {n : ℕ} (m : ℕ) (π : Representation ℂ (GL (Fin n) k) W) (j : ℕ) :
    Subrepresentation (thetaHom m 0 π) where
  toSubmodule :=
    { carrier := {f | ∀ Φ : rkSB k n m 0, Φ.1 ∈ rkSB k n m j → f.1.1 Φ = 0}
      add_mem' := fun {a b} ha hb Φ hΦ => by
        show a.1.1 Φ + b.1.1 Φ = 0
        rw [ha Φ hΦ, hb Φ hΦ, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c f hf Φ hΦ => by
        show c • f.1.1 Φ = 0
        rw [hf Φ hΦ, smul_zero] }
  apply_mem_toSubmodule g f hf Φ hΦ := hf _ (omRk k n m j (g⁻¹, 1) ⟨Φ.1, hΦ⟩).2
def RChar {N : ℕ} (X : Representation ℂ (GL (Fin N) k) W) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (b : ℕ) (h : b + 1 = N) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
    (σ : Representation ℂ (GL (Fin b) k × GL (Fin 1) k) Y),
    σ.IsIrreducible ∧ IsSubquotient σ (jac₂ (stdSum h) X) ∧
      ∀ (g : GL (Fin 1) k) (y : Y), σ (1, g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y
def LChar {N : ℕ} (X : Representation ℂ (GL (Fin N) k) W) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (b : ℕ) (h : 1 + b = N) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
    (σ : Representation ℂ (GL (Fin 1) k × GL (Fin b) k) Y),
    σ.IsIrreducible ∧ IsSubquotient σ (jac₂ (stdSum h) X) ∧
      ∀ (g : GL (Fin 1) k) (y : Y), σ (g, 1) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y
abbrev powChar (a : ℕ) (χ : kˣ →* ℂˣ) := prinSeries (fun _ : Fin a => χ)
abbrev prodAt {r t N : ℕ} (h : r + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W) :=
  ind₂ (stdSum h) (extTensor A B)
def Embeds {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (A : Representation ℂ G V)
    (B : Representation ℂ G W) : Prop := ∃ f : A.IntertwiningMap B, Function.Injective f
variable (k) in

def PowIrr : Prop := ∀ (a : ℕ) (χ : kˣ →* ℂˣ), IsSmoothChar χ → (powChar a χ).IsIrreducible
end GlobalTheory.TypeTwo


