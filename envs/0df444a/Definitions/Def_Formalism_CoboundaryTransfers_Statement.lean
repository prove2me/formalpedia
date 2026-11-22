-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_Statement
-- name    : Formalism_CoboundaryTransfers_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:12.160809+00:00
-- url     : https://prove2.me/theorems/b86b6cad-e106-4d14-90e2-237b49567c1a
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
structure Base (O A : Type) [CommRing O] [CommRing A] [Algebra O A] where
  p : ℕ
  hp : p.Prime
  φ : A →ₐ[O] A
  γ : A →ₐ[O] A
  X : A
  Q : A
  comm : ∀ a, φ (γ a) = γ (φ a)
  φX : ∃ v : A, φ X = X * v
namespace Base
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A)
def QLin : Prop := B.Q = B.X + (B.p : A)
def PhiX (k : ℕ) : Prop := ∃ v : A, B.φ B.X = B.X * B.Q ^ k * v
def GammaQ : Prop := ∃ v : A, IsUnit v ∧ (∃ t : A, v = 1 + B.X * t) ∧ B.γ B.Q = v * B.Q
def GammaX (u : O) : Prop := ∃ t : A, B.γ B.X = B.X * (algebraMap O A u + B.X * t)
def GammaModX : Prop := ∀ a : A, ∃ t : A, B.γ a - a = B.X * t
end Base
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
structure WachMod (B : Base O A) (M : ℕ) (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] where
  N : Submodule A D
  φ : D →ₗ[O] D
  γ : D →ₗ[O] D
  φ_smul : ∀ (a : A) (x : D), φ (a • x) = B.φ a • φ x
  γ_smul : ∀ (a : A) (x : D), γ (a • x) = B.γ a • γ x
  comm : ∀ x, φ (γ x) = γ (φ x)
  X_inj : ∀ x : D, B.X • x = 0 → x = 0
  Q_bij : Function.Bijective (fun x : D => B.Q • x)
  φ_N : ∀ x ∈ N, B.Q ^ M • φ x ∈ N
  γ_N : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = B.X • x'
  γ_QN : ∀ y : D, B.Q ^ M • y ∈ N → ∃ y' : D, B.Q ^ M • y' ∈ N ∧ γ y - y = B.X • y'
namespace WachMod
variable {B : Base O A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D] (W : WachMod B M D)
def HeightLower (k : ℕ) : Prop :=
  ∀ y ∈ W.N, B.Q ^ k • y ∈ Submodule.span A (W.φ '' (W.N : Set D))
def QInv (y : D) : Prop := B.Q ^ M • y ∈ W.N
def XN (z : D) : Prop := ∃ n ∈ W.N, z = B.X • n
def C1 (y z : D) : Prop := W.QInv y ∧ W.XN z
def C2 (ω : D) : Prop := ∃ y, W.QInv y ∧ ω = B.X • y
def d0 (x : D) : D × D := (W.φ x - x, W.γ x - x)
def d1 (y z : D) : D := (W.γ y - y) - (W.φ z - z)
def Cocycle (y z : D) : Prop := W.C1 y z ∧ W.d1 y z = 0
def IsCob1 (y z : D) : Prop := ∃ x ∈ W.N, y = W.φ x - x ∧ z = W.γ x - x
def IsCob2 (ω : D) : Prop := ∃ y z, W.C1 y z ∧ ω = W.d1 y z
def TorsKilled (c : O) : Prop :=
  ∀ ω, W.C2 ω → (∃ k : ℕ, W.IsCob2 (((B.p : O) ^ k) • ω)) → W.IsCob2 (c • ω)
def Z1 : Submodule O (D × D) :=
  LinearMap.ker ((W.γ - LinearMap.id).coprod (-(W.φ - LinearMap.id)))
def B1 : Submodule O (D × D) :=
  LinearMap.range ((W.φ - LinearMap.id).prod (W.γ - LinearMap.id))
def IntRep (pr : D × D) : Prop := (∃ k : ℕ, B.Q ^ k • pr.1 ∈ W.N) ∧ W.XN pr.2
def Zf : Submodule O (D × D) :=
  Submodule.span O {pr | pr ∈ W.Z1 ∧ ∃ a : ℕ, ∃ b ∈ W.B1, W.IntRep ((B.p ^ a : ℕ) • pr + b)} ⊔ W.B1
def FIN (g : ℕ) : Prop :=
  ∃ s : Finset (D × D), s.card ≤ g ∧ Submodule.span O (s : Set (D × D)) ⊔ W.B1 = W.Zf
end WachMod
variable {B : Base O A} {M : ℕ}
section Hom
variable {D D' D'' : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
  [AddCommGroup D''] [Module A D''] [Module O D''] [IsScalarTower O A D'']
structure Hom (W : WachMod B M D) (W' : WachMod B M D') where
  f : D →ₗ[A] D'
  φ_comm : ∀ x, f (W.φ x) = W'.φ (f x)
  γ_comm : ∀ x, f (W.γ x) = W'.γ (f x)
  N_le : ∀ x ∈ W.N, f x ∈ W'.N
namespace Hom
def id (W : WachMod B M D) : Hom W W where
  f := LinearMap.id
  φ_comm := fun _ => rfl
  γ_comm := fun _ => rfl
  N_le := fun _ hx => hx
def comp {W : WachMod B M D} {W' : WachMod B M D'} {W'' : WachMod B M D''}
    (g : Hom W' W'') (f : Hom W W') : Hom W W'' where
  f := g.f.comp f.f
  φ_comm := fun x => by simp [f.φ_comm, g.φ_comm]
  γ_comm := fun x => by simp [f.γ_comm, g.γ_comm]
  N_le := fun x hx => g.N_le _ (f.N_le x hx)
variable {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
def f2 : D × D →ₗ[O] D' × D' := (F.f.restrictScalars O).prodMap (F.f.restrictScalars O)
def ImF : Submodule O (D' × D') := W.Zf.map F.f2 ⊔ W'.B1
def col : ℕ∞ := Module.length O (↥W'.Zf ⧸ F.ImF.comap W'.Zf.subtype)
def LiftF (e : ℕ) : Prop := ∀ pr ∈ W'.Zf, (B.p ^ e : ℕ) • pr ∈ F.ImF
end Hom
end Hom
structure SES {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) where
  ι : Hom W₀ W₁
  π : Hom W₁ W₂
  ι_inj : Function.Injective ι.f
  exact : ∀ x, π.f x = 0 ↔ ∃ x₀, ι.f x₀ = x
  sat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N
section Hyp
variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₀ : WachMod B M D₀} {W₁ : WachMod B M D₁} {W₂ : WachMod B M D₂}
def SES.Surj (S : SES W₀ W₁ W₂) : Prop := Function.Surjective S.π.f
def CokerKilled (S : SES W₀ W₁ W₂) (e : ℕ) : Prop :=
  ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N, S.π.f n₁ = ((B.p : O) ^ e) • n
def RatSurj (S : SES W₀ W₁ W₂) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ k : ℕ, ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ ∃ x ∈ W₂.N,
    S.π.f y₁ = ((B.p : O) ^ k) • y + (W₂.φ x - x) ∧
    S.π.f z₁ = ((B.p : O) ^ k) • z + (W₂.γ x - x)
def Lifts (S : SES W₀ W₁ W₂) (c : O) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ S.π.f y₁ = c • y ∧ S.π.f z₁ = c • z
end Hyp
namespace WachMod
variable {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)
def QInvSub : Submodule A D := W.N.comap (B.Q ^ M • LinearMap.id)
def XNSub : Submodule A D := W.N.map (B.X • LinearMap.id)
def ZInt : Submodule O (D × D) :=
  ((W.QInvSub.restrictScalars O).prod (W.XNSub.restrictScalars O)) ⊓ W.Z1
def BInt : Submodule O (D × D) :=
  (W.N.restrictScalars O).map ((W.φ - LinearMap.id).prod (W.γ - LinearMap.id))
abbrev integralCohomology : Type := ↥W.ZInt ⧸ W.BInt.comap W.ZInt.subtype
abbrev H1 : Type := ↥W.Z1 ⧸ W.B1.comap W.Z1.subtype
abbrev finiteCohomology : Type := ↥W.Zf ⧸ W.B1.comap W.Zf.subtype
end WachMod
section Gal
variable {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {H : Type} [AddCommGroup H] [Module O H]
def HerrIso (W : WachMod B M D) (cl : W.Z1 →ₗ[O] H) : Prop :=
  Function.Surjective cl ∧ ∀ pr : W.Z1, (cl pr = 0 ↔ (pr : D × D) ∈ W.B1)
def HerrInj (W : WachMod B M D) (cl : W.Z1 →ₗ[O] H) : Prop :=
  ∀ pr : W.Z1, W.Cocycle (pr : D × D).1 (pr : D × D).2 → cl pr = 0 →
    W.IsCob1 (pr : D × D).1 (pr : D × D).2
def HfIsZf (W : WachMod B M D) (cl : W.Z1 →ₗ[O] H) (Hf : Submodule O H) : Prop :=
  (W.Zf.comap W.Z1.subtype).map cl = Hf
def HfInt (W : WachMod B M D) (cl : W.Z1 →ₗ[O] H) (Hf : Submodule O H) (eW : ℕ) : Prop :=
  (∀ pr : W.Z1, W.Cocycle (pr : D × D).1 (pr : D × D).2 → cl pr ∈ Hf) ∧
    ∀ κ ∈ Hf, ∃ pr : W.Z1, W.Cocycle (pr : D × D).1 (pr : D × D).2 ∧
      cl pr = ((B.p : O) ^ eW) • κ
def ClNat {D' H' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
    [AddCommGroup H'] [Module O H'] {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
    (cl : W.Z1 →ₗ[O] H) (cl' : W'.Z1 →ₗ[O] H') (g : H →ₗ[O] H') : Prop :=
  ∀ (pr : W.Z1) (pr' : W'.Z1), (pr' : D' × D') = F.f2 pr → g (cl pr) = cl' pr'
end Gal
end Formalism.CoboundaryTransfers


