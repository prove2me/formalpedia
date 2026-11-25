-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:41.956488+00:00
-- url     : https://prove2.me/theorems/a48f7c47-9e5d-5e21-8a14-f61580f17f71
-- title:
--   Same Genus Fix
-- statement:
--   Definitions and structural lemmas for Same Genus Fix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SameGenusFix.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SiegelMassRatioOfLI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.L2.SG.Pf.Cnt
open Formalism.HermitianLattices.Ext.L3
section Defs
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def Nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ x : V, (∀ y : V, h x y = 0) → x = 0
def orthK (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : Submodule K V :=
  ⨅ u ∈ U, LinearMap.ker (h u)
def PosDefOn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : Prop :=
  ∀ x ∈ X, x ≠ 0 → ∀ φ : K →+* ℂ, 0 < (φ (h x x)).re
def IsLatIn (X : Submodule K V) (L : Submodule (𝓞 K) V) : Prop :=
  L.FG ∧ Submodule.span K (L : Set V) = X
def dualIn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V :=
  X.restrictScalars (𝓞 K) ⊓ Formalism.HermitianLatticesTheory.dual h L
def dualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V where
  carrier := {x | ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
  zero_mem' := fun y _ => by simp
  add_mem' := by
    intro x x' hx hx' y hy
    rw [map_add]
    exact Submodule.add_mem _ (hx y hy) (hx' y hy)
  smul_mem' := by
    intro c x hx y hy
    rw [show h y (c • x) = c • h y x by
      rw [← algebraMap_smul K c x, LinearMap.map_smul, algebraMap_smul]]
    exact Submodule.smul_mem _ c (hx y hy)
def IsJordanIn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (b : Fin (finrank K X) → V) (a : Fin (finrank K X) → 𝓞 F) : Prop :=
  (∀ i, b i ∈ X) ∧
  locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L ∧
  (∀ i j, i ≠ j → h (b i) (b j) = 0) ∧
  (∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) ∧
  ∀ i, a i ≠ 0
def cJof {n : ℕ} (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) : ℕ :=
  (Finset.univ.filter fun i => vF 𝔭 (a i) ≠ 0).card
def vJof {n : ℕ} (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) : ℕ :=
  ∑ i, vF 𝔭 (a i)
def cJ (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sInf {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a}
def vJ (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sInf {v | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ v = vJof 𝔭 a}
abbrev DiscMod (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : Type :=
  ↥(locF 𝔭 (dualIn h X L)) ⧸ (locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype
def discAut (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : ℕ :=
  Nat.card {P : Module.End (𝓞 K) (DiscMod h X L 𝔭) //
    ∀ x y x' y' : ↥(locF 𝔭 (dualIn h X L)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
def isomFix (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ Formalism.HermitianLatticesTheory.isom h ∧ ∀ u ∈ U, g u = u}
  one_mem' := ⟨(Formalism.HermitianLatticesTheory.isom h).one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Formalism.HermitianLatticesTheory.isom h).mul_mem ha hb, fun u hu => ?_⟩
    change a (b u) = u
    rw [hb' u hu, ha' u hu]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Formalism.HermitianLatticesTheory.isom h).inv_mem ha, fun u hu => ?_⟩
    change a.symm u = u
    conv_lhs => rw [← ha' u hu]
    simp
def stabFix (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    Set (V ≃ₗ[K] V) :=
  {g | g ∈ isomFix h U ∧ Formalism.HermitianLatticesTheory.gmap g Λ = Λ}
def GlueSet (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    Set (Submodule (𝓞 K) V) :=
  {Λ | Submodule.IsLattice K Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ ∧ Λ ⊓ U.restrictScalars (𝓞 K) = M}
def fibP (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F))
    (M T : Submodule (𝓞 K) V) : ℕ :=
  Nat.card {Λ : Submodule (𝓞 K) V //
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T}
def SameGenusFix (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (T T' : Submodule (𝓞 K) V) : Prop :=
  ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T'
def nM (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (U : Submodule K V) (M : Submodule (𝓞 K) V) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vJ h U M 𝔭.1
end Defs
end Formalism.L2.SG.Pf.Cnt


