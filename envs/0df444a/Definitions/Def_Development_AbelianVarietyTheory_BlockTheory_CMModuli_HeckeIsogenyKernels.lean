-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HeckeIsogenyKernels
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_HeckeIsogenyKernels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:07.982782+00:00
-- url     : https://prove2.me/theorems/458e6430-b3e4-421b-972f-a0c4f788276d
-- title:
--   Hecke Isogeny Kernels
-- statement:
--   Definitions and structural lemmas for Hecke Isogeny Kernels, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HeckeIsogenyKernels.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def conjIdeal (H : Host E) (P : Ideal (𝓞 E)) : Ideal (𝓞 E) := P.map (H.bar : 𝓞 E →+* 𝓞 E)
def IsSplitPrimeOff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  p.Prime ∧ P.IsMaximal ∧ (p : 𝓞 E) ∈ P ∧ conjIdeal H P ≠ P ∧ ¬ p ∣ l.M'
section Fibre
variable {k : Type} [Field k]
abbrev Pts (t : SAB H (Sp k)) : Type := 𝟙_ (Over (Sp k)) ⟶ t.G
def KilledBy (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∀ a ∈ I, x ≫ t.act.act a = 1
def KilledByPow (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∃ n : ℕ, KilledBy t (I ^ n) x
def IsHeckeDatum (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) (i : ℕ) (C₀ : Subgroup (Pts t)) : Prop :=
  (∀ a, ∀ x ∈ C₀, x ≫ t.act.act a ∈ C₀) ∧ (∀ x ∈ C₀, KilledBy t (conjIdeal H P) x) ∧
    Finite C₀ ∧ Nat.card C₀ = Ideal.absNorm P ^ i
def heckeKernel (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) : Set (Pts t) :=
  {x | ∃ x₁ x₂ x₃ : Pts t, x = x₁ * x₂ * x₃ ∧
    (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ conjIdeal H P ∧ x₁ ≫ t.act.act a = 1) ∧
    (KilledByPow t (conjIdeal H P) x₂ ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ KilledByPow t P x₃ ∧ ∀ c ∈ C₀, Out.WeilIs t.G t.PP.L (p : ℤ) x₃ c 1)}
def IsHeckeIsogeny {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : Sp k ⟶ Sp B}
    (o o'' : Obj D l b s) (p : ℕ) (C : Set (Pts o.t)) (ψ : o.t.G ⟶ o''.t.G) : Prop :=
  IsMonHom ψ ∧ IsFinite ψ.left ∧ Surjective ψ.left ∧
    (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o''.t.act.act a) ∧
    (∀ x : Pts o.t, x ≫ ψ = 1 ↔ x ∈ C) ∧
    LBIso (cubeLB o''.t.G ![fst o.t.G o.t.G ≫ ψ, snd o.t.G o.t.G ≫ ψ] o''.t.PP.L)
      (LB.LinComb (abelian₂ o.t.G o.t.PP.L) (K := PUnit) (fun _ => 𝟙 _) (fun _ => (p : ℤ) ^ 2)) ∧
    (∀ a, o.eta a ≫ ψ = o''.eta a ^ p) ∧
    (∀ a, o.etaA a ≫ ψ = o''.etaA a ^ p)
end Fibre
def HeckeCorrespondence {D : Datum H} {l : Level H} (Xo : Moduli D l) : Prop :=
  ∀ (p : ℕ) (P : Ideal (𝓞 E)), IsSplitPrimeOff l p P → ∀ i : ℕ, i ≤ D.p + D.q →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (o : Obj D l (baseKA l) (y ≫ Xo.s)),
      Nonempty (ObjMap o Xo.univ y) →
      ∀ C₀ : Subgroup (Pts o.t), IsHeckeDatum o.t P i C₀ →
        ∃! y'' : Sp k ⟶ Xo.X, y'' ≫ Xo.s = y ≫ Xo.s ∧
          ∃ (o'' : Obj D l (baseKA l) (y ≫ Xo.s)) (ψ : o.t.G ⟶ o''.t.G),
            Nonempty (ObjMap o'' Xo.univ y'') ∧ IsHeckeIsogeny o o'' p (heckeKernel o.t p P C₀) ψ
def HeckeCorrespondenceStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l),
    HeckeCorrespondence Xo
example {k : Type} [Field k] (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) : IsHeckeDatum t P 0 ⊥ := by
  refine ⟨fun a x hx => ?_, fun x hx a _ => ?_, inferInstance, by simp⟩
  · have := t.act.hom a
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, MonObj.one_comp]
  · have := t.act.hom a
    rw [Subgroup.mem_bot] at hx
    rw [hx, MonObj.one_comp]
example {k : Type} [Field k] (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (x : Pts t)
    (hx : x ∈ heckeKernel t p P ⊥) : x ^ p = 1 := by
  obtain ⟨x₁, x₂, x₃, rfl, ⟨h₁, -⟩, ⟨-, h₂⟩, ⟨h₃, -⟩⟩ := hx
  rw [Subgroup.mem_bot] at h₂
  have hc : ∀ u v : Pts t, Commute u v := fun u v => mul_comm u v
  rw [(hc _ _).mul_pow, (hc _ _).mul_pow, h₁, h₂, h₃, _root_.mul_one, _root_.mul_one]
end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels


