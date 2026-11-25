-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:35.578548+00:00
-- url     : https://prove2.me/theorems/be5848fe-51b7-523f-bab4-4f22339eabcb
-- title:
--   Split At Of
-- statement:
--   Definitions and structural lemmas for Split At Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SplitAtOf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
namespace Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
def spanS {K V : Type} [Field K] [AddCommGroup V] [Module K V] (S : Subring K) {ι : Type}
    [Fintype ι] (b : ι → V) : AddSubgroup V where
  carrier := {v | ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i}
  zero_mem' := ⟨0, fun _ => S.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, fun i => S.add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro x ⟨c, hc, rfl⟩
    exact ⟨-c, fun i => S.neg_mem (hc i), by
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩
section Abs
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def SplitAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ h (c i₀) (c i₀) = h ξ ξ ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b
def ExactAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) → ∃ X ∈ spanS S b, h X X = h ξ ξ
def RebaseAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ X ∈ spanS S b, IsUnitIn S (h X X * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = X ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b
end Abs
def ExactVec : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ π : K, IsUnif (locRing P) π → ExactAt (locRing P) π h
def Rebase : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Subring K) (π : K)
    (h : V →ₗ⋆[K] V →ₗ[K] K), IsHermSemilocal S → IsUnif S π → h.IsSymm →
    (∀ x, h x x = 0 → x = 0) → RebaseAt S π h
def LocSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ (n : ℕ) (b : Fin n → V)
    (v : V), v ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b)) ↔
      v ∈ spanS (locRing P) b
def UnifVal : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal →
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : 𝓞 F, a ≠ 0 →
      IsUnitIn (locRing P)
        (algebraMap F K (a : F) * (π ^ vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) a)⁻¹)
def JordSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V), Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ (n : ℕ) (b : Fin n → V), locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
      Submodule.span K (Set.range b) = ⊤
end Formalism.L2.SG.Pf.G3


