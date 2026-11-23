-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:23.784784+00:00
-- url     : https://prove2.me/theorems/4f5faab4-0eff-48d5-b653-502feddd18ed
-- title:
--   Idx Det
-- statement:
--   Definitions and structural lemmas for Idx Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
section Det
variable {K : Type} [Field K] [NumberField K]
def famC {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C : Matrix (Fin d) (Fin d) K) : Fin d → V :=
  fun j => ∑ i, C i j • b i
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def stdE (d : ℕ) : Fin d → (Fin d →₀ K) := fun k => Finsupp.single k 1
def idxStd (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C : Matrix (Fin d) (Fin d) K) : ℤ :=
  idxAt w (Submodule.span (𝓞 K) (Set.range (stdE (K := K) d)))
    (Submodule.span (𝓞 K) (Set.range (famC (stdE d) C)))
def colOp {d : ℕ} (j0 : Fin d) (v : Fin d → K) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j => if j = j0 then v i else (if i = j then 1 else 0)
end Det
end PI.Dv.ProjGramW


