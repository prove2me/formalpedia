-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SubquotientOfEigencharacter
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SubquotientOfEigencharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:42.050694+00:00
-- url     : https://prove2.me/theorems/e751678f-478a-4f42-b79e-7a8c6ee2830b
-- title:
--   Subquotient Of Eigencharacter
-- statement:
--   Definitions and structural lemmas for Subquotient Of Eigencharacter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SubquotientOfEigencharacter.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothQuot
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
namespace GlobalTheory.CompanionTheory.SubEig
section Generic
variable {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
def cyc (ρ : Representation ℂ G U) (u : U) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G => ρ g u)
  apply_mem_toSubmodule g v hv := by
    have hle : Submodule.span ℂ (Set.range fun g : G => ρ g u) ≤
        (Submodule.span ℂ (Set.range fun g : G => ρ g u)).comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact hle hv
theorem mem_cyc (ρ : Representation ℂ G U) (u : U) : u ∈ (cyc ρ u).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩
def mkI (ρ : Representation ℂ G U) (T : Submodule ℂ U) (hst : ∀ g, T ≤ T.comap (ρ g)) :
    Representation.IntertwiningMap ρ (ρ.quotient T hst) where
  toLinearMap := T.mkQ
  isIntertwining' g := by
    ext v
    rfl
def inclI {ρ : Representation ℂ G U} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl
variable [TopologicalSpace G] [IsTopologicalGroup G]
noncomputable def stab (ρ : Representation ℂ G U) (v : U) : Subgroup G :=
  _root_.UpperTheory.Reformulated.B.RepresentationStabilizer.stab ρ v
end Generic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.CompanionTheory.SubEig


