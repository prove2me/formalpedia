-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:25.282525+00:00
-- url     : https://prove2.me/theorems/d391d95f-d0c0-4fa2-9cce-4d1aa2caa6f4
-- title:
--   PQdet Facts
-- statement:
--   Definitions and structural lemmas for PQdet Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PQdetFacts.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL
namespace PositivityTheory.Rg.Cz
namespace QF
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
section Alg
variable {A : Type} [Ring A] [Algebra ℂ A]
def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A (k : ℂ)) else 0) + C (E a b)
def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), C ((Equiv.Perm.sign σ : ℤ) : A) *
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod
def evU (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) (fun a => (Algebra.commutes u a).symm)
end Alg
section Op
variable {M : Type} [AddCommGroup M] [Module ℂ M]
end Op
end QF
open QF ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end PositivityTheory.Rg.Cz
end


