-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:35.707282+00:00
-- url     : https://prove2.me/theorems/469cb677-dd62-4823-b061-ec0c557e8161
-- title:
--   Mem OOf Is Integral
-- statement:
--   Definitions and structural lemmas for Mem OOf Is Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.TIW
open PI.Dv NumberField
section Orth
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G)
end Orth
section Eps
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical in

def chiT (P : Pair K G) (x : G) : K := if h : x ∈ P.H then (((P.chi ⟨x, h⟩)⁻¹ : Kˣ) : K) else 0
def epsS (P : Pair K G) : MonoidAlgebra K G := ∑ x : G, chiT P x • MonoidAlgebra.of K G x
end Eps
section RankOne
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
end RankOne
section Integral
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
def ιO : MonoidAlgebra (𝓞 K) G →ₐ[𝓞 K] MonoidAlgebra K G :=
  MonoidAlgebra.mapAlgHom G (Algebra.ofId (𝓞 K) K)
def IntR (z : MonoidAlgebra K G) : Prop := z ∈ (ιO (K := K) (G := G)).range
end Integral
end PI.Dv.TIW


