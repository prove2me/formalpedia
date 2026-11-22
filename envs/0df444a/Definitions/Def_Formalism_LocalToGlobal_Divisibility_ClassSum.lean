-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
-- name    : Formalism_LocalToGlobal_Divisibility_ClassSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:16.786424+00:00
-- url     : https://prove2.me/theorems/06af8dba-5def-47f9-a911-d5e82559b8f2
-- title:
--   Class Sum
-- statement:
--   Definitions and structural lemmas for Class Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSum.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
structure CSD (K : Type) [Field K] [NumberField K] [StarRing K] where

  Cl : Type
  [finCl : Fintype Cl]

  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]

  ιV : Type
  [finιV : Fintype ιV]
  [decιV : DecidableEq ιV]
  bV : Basis ιV K V

  pair : V →ₗ⋆[K] V →ₗ[K] K

  Gam : Cl → Type
  [grpGam : ∀ c, Group (Gam c)]
  [finGam : ∀ c, Fintype (Gam c)]

  ρ : ∀ c, Gam c →* Module.End K V

  Nab : Cl → Submodule (𝓞 K) V

  Del : Cl → Submodule (𝓞 K) V
attribute [instance] CSD.finCl CSD.addV CSD.modV CSD.modOV CSD.towV CSD.finιV CSD.decιV CSD.grpGam
  CSD.finGam
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
instance : FiniteDimensional K S.V := Module.Finite.of_basis S.bV
def Forms : Submodule K (S.Cl → S.V) where
  carrier := {f | ∀ c (γ : S.Gam c), S.ρ c γ (f c) = f c}
  add_mem' := by
    intro f g hf hg c γ
    simp only [Pi.add_apply, map_add, hf c γ, hg c γ]
  zero_mem' := by
    intro c γ
    simp
  smul_mem' := by
    intro a f hf c γ
    simp only [Pi.smul_apply, map_smul, hf c γ]
def dim : ℕ := finrank K S.Forms
def IsRat (f : S.Cl → S.V) : Prop := ∀ c i, S.bV.repr (f c) i ∈ cmMax K
def HasRatBasis : Prop := ∃ b : Basis (Fin S.dim) K S.Forms, ∀ i, S.IsRat (b i : S.Cl → S.V)
open Classical in

def basis : Basis (Fin S.dim) K S.Forms :=
  if h : S.HasRatBasis then h.choose else finBasis K S.Forms
def I : (Fin S.dim → K) →ₗ[K] (S.Cl → S.V) :=
  S.Forms.subtype ∘ₗ (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms)
def wt (c : S.Cl) : ℕ := Fintype.card (S.Gam c)
def DGam : ℕ := Finset.univ.lcm S.wt
def csum (f g : S.Cl → S.V) : K := ∑ c, ((S.wt c : K))⁻¹ * S.pair (f c) (g c)
def H : Matrix (Fin S.dim) (Fin S.dim) K :=
  Matrix.of fun i j => S.csum (S.basis i : S.Cl → S.V) (S.basis j : S.Cl → S.V)
def nabLat : Submodule (𝓞 K) (Fin S.dim → K) := valLatF S.I S.Nab
def delLat : Submodule (𝓞 K) (Fin S.dim → K) := valLatF S.I S.Del
def gramV : Matrix S.ιV S.ιV K := Matrix.of fun i j => S.pair (S.bV i) (S.bV j)
structure Good (s : ℕ) : Prop where
  symm : S.pair.IsSymm
  nondeg : S.pair.Nondegenerate
  inv : ∀ c (γ : S.Gam c) x y, S.pair (S.ρ c γ x) (S.ρ c γ y) = S.pair x y
  nab_lat : ∀ c, Submodule.IsLattice K (S.Nab c)
  del_le : ∀ c, S.Del c ≤ S.Nab c
  del_stable : ∀ c (γ : S.Gam c), ∀ y ∈ S.Del c, S.ρ c γ y ∈ S.Del c
  s_pos : 0 < s
  dual_le : ∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab c), (s : 𝓞 K) • y ∈ S.Del c
  del_dual : ∀ c, ∀ y ∈ S.Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab c)
structure Rat : Prop where
  pair_rat : ∀ i j, S.gramV i j ∈ cmMax K
  act_rat : ∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef
end CSD
end Formalism.L2.DIV


