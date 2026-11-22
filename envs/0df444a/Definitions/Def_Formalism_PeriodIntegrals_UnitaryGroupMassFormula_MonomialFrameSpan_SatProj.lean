-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:54.592329+00:00
-- url     : https://prove2.me/theorems/b55249b6-858b-41b7-81a3-d9c360f35857
-- title:
--   Sat Proj
-- statement:
--   Definitions and structural lemmas for Sat Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace GenFrameSpan
open CutKW MvPolynomial
namespace SatP
section Proj
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}
def emb (s : Lt) : ℕ × Fin N0 → Lt × ℕ × Fin N0 := fun p => (s, p.1, p.2)
theorem emb_inj (s : Lt) : Function.Injective (emb (N0 := N0) s) := by
  intro a b h
  simp only [emb, Prod.mk.injEq] at h
  exact Prod.ext h.2.1 h.2.2
def res (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) : ℕ × Fin N0 →₀ ℕ :=
  m.comapDomain (emb s) (emb_inj s).injOn
def Tmap (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ)) :
    MvPolynomial (Lt × ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  (basisMonomials (Lt × ℕ × Fin N0) ℤ).constr ℤ fun m =>
    ∏ s, rename (emb s) (π s (monomial (res s m) 1))
end Proj
end SatP
end GenFrameSpan


