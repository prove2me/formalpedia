-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- name    : Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:30.508813+00:00
-- url     : https://prove2.me/theorems/8f390a05-711d-49ed-9916-d955693d7483
-- title:
--   Defs Aut
-- statement:
--   Definitions and structural lemmas for Defs Aut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsAut.lean

import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
namespace Formalism.L2.NG
section aut
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
def Cong (N : ℕ) (κ : GAf L n) : Prop :=
  κ ∈ Umax L n ∧ ∀ i j, ∃ y ∈ ALint L,
    (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y
theorem Cong.of_mul_left {N N' : ℕ} {κ : GAf L n} (h : Cong L n (N * N') κ) : Cong L n N κ :=
  ⟨h.1, fun i j => by
    obtain ⟨y, hy, e⟩ := h.2 i j
    exact ⟨(N' : AL L) * y, Subring.mul_mem _ (natCast_mem _ _) hy, by rw [e]; push_cast; ring⟩⟩
theorem Cong.of_mul_right {N N' : ℕ} {κ : GAf L n} (h : Cong L n (N * N') κ) : Cong L n N' κ :=
  Cong.of_mul_left L n (N := N') (N' := N) (by rwa [Nat.mul_comm])
variable {W : Type} [AddCommGroup W] [Module ℂ W]
def rt (h : GAf L n) : (GAf L n → W) →ₗ[ℂ] (GAf L n → W) where
  toFun f := fun g => f (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def AFall (ρ : Representation ℂ (GQ L n) W) : Submodule ℂ (GAf L n → W) where
  carrier := {f | (∀ (γ : GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
    ∃ N : ℕ, 0 < N ∧ ∀ κ, Cong L n N κ → ∀ g, f (g * κ) = f g}
  zero_mem' := ⟨fun γ g => by simp, 1, one_pos, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h1, N, hN, h2⟩ ⟨h1', N', hN', h2'⟩
    refine ⟨fun γ g => by simp [h1 γ g, h1' γ g], N * N', Nat.mul_pos hN hN', fun κ hκ g => ?_⟩
    simp [h2 κ (Cong.of_mul_left L n hκ) g, h2' κ (Cong.of_mul_right L n hκ) g]
  smul_mem' := by
    rintro c f ⟨h1, N, hN, h2⟩
    exact ⟨fun γ g => by simp [h1 γ g], N, hN, fun κ hκ g => by simp [h2 κ hκ g]⟩
variable {L n}
structure IsSubrep (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) : Prop where
  le : S ≤ AFall L n ρ
  stable : ∀ h, ∀ f ∈ S, rt L n h f ∈ S
def IsIrrRep (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) : Prop :=
  IsSubrep ρ S ∧ S ≠ ⊥ ∧ ∀ S', IsSubrep ρ S' → S' ≤ S → S' = ⊥ ∨ S' = S
def IsoRep {W' : Type} [AddCommGroup W'] [Module ℂ W'] (S : Submodule ℂ (GAf L n → W))
    (S' : Submodule ℂ (GAf L n → W')) : Prop :=
  ∃ T : S ≃ₗ[ℂ] S', ∀ (h : GAf L n) (f f' : S), (f' : GAf L n → W) = rt L n h (f : GAf L n → W) →
    ((T f' : S') : GAf L n → W') = rt L n h ((T f : S') : GAf L n → W')
def isoTyp (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) : Submodule ℂ (GAf L n → W) :=
  sSup {S' | IsIrrRep ρ S' ∧ IsoRep S S'}
def HomG (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) :
    Submodule ℂ (S →ₗ[ℂ] (GAf L n → W)) where
  carrier := {T | (∀ f, T f ∈ AFall L n ρ) ∧ ∀ (h : GAf L n) (f f' : S),
    (f' : GAf L n → W) = rt L n h (f : GAf L n → W) → T f' = rt L n h (T f)}
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun _ _ _ _ => by simp⟩
  add_mem' := by
    rintro T T' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨fun f => Submodule.add_mem _ (h1 f) (h1' f), fun h f f' e => by
      simp [h2 h f f' e, h2' h f f' e]⟩
  smul_mem' := by
    rintro c T ⟨h1, h2⟩
    exact ⟨fun f => Submodule.smul_mem _ c (h1 f), fun h f f' e => by simp [h2 h f f' e]⟩
def multRep (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) : ℕ :=
  Module.finrank ℂ (HomG ρ S)
variable (L n)
structure AlgWt where
  W : Type
  [acg : AddCommGroup W]
  [mod : Module ℂ W]
  ρ : Representation ℂ (GQ L n) W
  alg : IsAlgWeight L n ρ
  irr : ρ.IsIrreducible
attribute [instance] AlgWt.acg AlgWt.mod
structure AutRep extends AlgWt L n where
  S : Submodule ℂ (GAf L n → W)
  irrS : IsIrrRep ρ S
variable {L n}
def AlgWt.Iso (a b : AlgWt L n) : Prop := ∃ T : a.W ≃ₗ[ℂ] b.W, ∀ γ x, T (a.ρ γ x) = b.ρ γ (T x)
def AlgWt.IsDual (a b : AlgWt L n) : Prop :=
  ∃ B : a.W →ₗ[ℂ] b.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (a.ρ γ x) (b.ρ γ y) = B x y
open Classical in

def evPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if p.1 = τ then B.val p.2.1 p.2.2
  else if p.1 = ComplexEmbedding.conjugate τ then (B⁻¹).val p.2.2 p.2.1
  else if p.2.1 = p.2.2 then 1 else 0
def AlgWt.HWAt (a : AlgWt L n) (τ : L →+* ℂ) (lam : Fin n → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      LinearMap.toMatrix b b (a.ρ γ) =
        fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (P i j)) ∧
    ∃ v : ι → ℂ, v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id →
      Matrix.mulVec (Matrix.of fun i j => MvPolynomial.eval (evPt τ B) (P i j)) v =
        (∏ i, (B.val i i) ^ (lam i)) • v
def infOf (lam : Fin n → ℤ) : Multiset ℂ :=
  Finset.univ.val.map fun i : Fin n => (lam i : ℂ) + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)
def AutRep.Iso (π π' : AutRep L n) : Prop := π.toAlgWt.Iso π'.toAlgWt ∧ IsoRep π.S π'.S
def AutRep.mult (π : AutRep L n) : ℕ := multRep π.ρ π.S
def AutRep.SphAt (π : AutRep L n) (v : HeightOneSpectrum (𝓞 L⁺)) : Prop :=
  ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → rt L n κ f = f
def OverPl (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 L⁺)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 L⁺) (𝓞 L)) = v.asIdeal
def TypeSp (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) :
    Submodule ℂ (GAf L n → W) where
  carrier := {f | f ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) f = ((χ κ : ℂˣ) : ℂ) • f}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨Submodule.add_mem _ h1 h1', fun κ => by rw [map_add, h2, h2', smul_add]⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨Submodule.smul_mem _ c h1, fun κ => by rw [map_smul, h2, smul_comm]⟩
def HypOutside (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 L⁺))) : Prop :=
  ∀ κ : GAf L n, TrivOutside Bᶜ κ → (κ ∈ J ↔ κ ∈ Umax L n) ∧ ∀ h : κ ∈ J, χ ⟨κ, h⟩ = 1
open Classical in

def heckeD (J : Subgroup (GAf L n)) (D : Set (GAf L n)) (f : GAf L n → W) : GAf L n → W :=
  fun g => ∑ᶠ c : GAf L n ⧸ J, if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then f (g * hc.choose) else 0
def tN (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (f : GAf L n → W) :
    GAf L n → W :=
  ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • heckeD J (tSet L n s ϖ k) f
end aut
end Formalism.L2.NG


