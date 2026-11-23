-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:04.95813+00:00
-- url     : https://prove2.me/theorems/ec6c7410-2da3-41b2-bc12-3e3ca6f4873d
-- title:
--   Linear Independent Prod Rename Of Card
-- statement:
--   Definitions and structural lemmas for Linear Independent Prod Rename Of Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean

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
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
def mvPolynomialCoeffInFirstVariables (m : S₁ →₀ ℕ) : MvPolynomial (S₁ ⊕ S₂) K →ₗ[K] MvPolynomial S₂ K :=
  (lcoeff (MvPolynomial S₂ K) m).restrictScalars K ∘ₗ (sumAlgEquiv K S₁ S₂).toLinearMap
def sumComplementToProduct {ι σ : Type} (i : ι) : σ ⊕ ({j // j ≠ i} × σ) → ι × σ :=
  Sum.elim (fun x => (i, x)) (fun p => (p.1.1, p.2))
section Len
end Len
section Psi
variable {K : Type*} [Field K]
def mvPolynomialProductExtension {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) :
    ((∀ τ : {τ // τ ≠ τ₀}, κ τ.1) → MvPolynomial σ K) →ₗ[K] MvPolynomial (ι × σ) K where
  toFun h := ∑ g, rename (Prod.mk τ₀) (h g) * ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ.1) (b τ.1 (g τ))
  map_add' h h' := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c h := by simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]
end Psi
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases


