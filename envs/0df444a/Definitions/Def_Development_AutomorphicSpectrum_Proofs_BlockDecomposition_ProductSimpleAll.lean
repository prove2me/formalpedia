-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:22.896695+00:00
-- url     : https://prove2.me/theorems/51390a48-0bd3-4383-892f-aa7f7ff1dbc2
-- title:
--   Product Simple All
-- statement:
--   Definitions and structural lemmas for Product Simple All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
namespace GlobalTheory.CompanionTheory.ProdSimple
def cf {Γ : Type} [Group Γ] (g : Γ) : MonoidAlgebra ℂ Γ →ₗ[ℂ] ℂ where
  toFun a := a.coeff g
  map_add' a b := by simp
  map_smul' r a := by simp
def regSub {Γ : Type} [Group Γ] (N : Submodule ℂ (MonoidAlgebra ℂ Γ))
    (h : ∀ g : Γ, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N) : Representation ℂ Γ N where
  toFun g := (LinearMap.mulLeft ℂ (MonoidAlgebra.single g (1 : ℂ))).restrict (h g)
  map_one' := by
    ext a
    simp [← MonoidAlgebra.one_def]
  map_mul' g k := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    change MonoidAlgebra.single (g * k) (1 : ℂ) * (a : MonoidAlgebra ℂ Γ) =
      MonoidAlgebra.single g (1 : ℂ) * (MonoidAlgebra.single k (1 : ℂ) * (a : MonoidAlgebra ℂ Γ))
    rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]
variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]
def psi (ρ : Representation ℂ (∀ c, L c) W) (v : W) :
    MultilinearMap ℂ (fun c => MonoidAlgebra ℂ (L c)) W :=
  ∑ g : ∀ c, L c,
    ((MultilinearMap.mkPiAlgebra ℂ (Fin s) ℂ).compLinearMap (fun c => cf (g c))).smulRight (ρ g v)
end GlobalTheory.CompanionTheory.ProdSimple


