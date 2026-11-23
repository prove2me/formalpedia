-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:10.984557+00:00
-- url     : https://prove2.me/theorems/b383bf69-2f0c-447c-8b13-c34556a3afa1
-- title:
--   Xdeg Le Total Degree
-- statement:
--   Definitions and structural lemmas for Xdeg Le Total Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace PI.WickFormula.Asm
def xdeg {r s : ℕ} (m : Fin r ⊕ Fin s →₀ ℕ) : ℕ := ∑ i, m (Sum.inl i)
section
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}
theorem ordEval_add (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (P Q : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' (P + Q) = ordEval a a' P + ordEval a a' Q := by
  obtain ⟨f, hf⟩ := h1 k AA r s a a'
  rw [← hf, ← hf, ← hf, map_add]
noncomputable def phiH (h1 : OrdLin) (a b : Fin r → AA) (a' b' : Fin s → AA) (σ₀ : M) :
    MvPolynomial (Fin r ⊕ Fin s) k →+ M :=
  AddMonoidHom.mk' (fun R => ordEval (a + b) (a' + b') R • σ₀)
    (fun P Q => by rw [ordEval_add h1, add_smul])
noncomputable def tH (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (n : ℕ) : MvPolynomial (Fin r ⊕ Fin s) k →+ M :=
  AddMonoidHom.mk' (fun R => ordEval a a' ((n.factorial : ℚ)⁻¹ • (delta κ ^ n) R) • σ₀)
    (fun P Q => by rw [map_add, smul_add, ordEval_add h1, add_smul])
noncomputable def psi (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (N : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) : M :=
  ∑ n ∈ Finset.range N, tH h1 a a' κ σ₀ n R
variable {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}
end
end PI.WickFormula.Asm
namespace PI.WickFormula
end PI.WickFormula


