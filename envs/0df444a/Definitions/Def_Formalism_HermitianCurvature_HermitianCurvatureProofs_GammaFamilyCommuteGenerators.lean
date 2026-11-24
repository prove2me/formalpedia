-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:41.178831+00:00
-- url     : https://prove2.me/theorems/4826792e-12fb-4ae2-93f7-7fcc80fec41e
-- title:
--   Gamma Family Commute Generators
-- statement:
--   Definitions and structural lemmas for Gamma Family Commute Generators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GammaFamilyCommuteGenerators.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
namespace Formalism.FourierDecayAlt.P.Mx8
section Abstract
variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
def sStar (σ : Site A) : Site A := ⟨star σ.p, -star σ.ci, -star σ.c⟩
end Abstract
section Lev
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
def G (l : Fin r) : Set A := {L.p l, L.c l, L.ci l, -L.pb l, L.cb l, L.cbi l}
end Lev
noncomputable def Cen (P : Par) (i : Fin P.r) : Subalgebra ℂ (A P) := Subalgebra.centralizer ℂ (ops (siteA P i))
def Ent {A : Type} [Ring A] [Algebra ℂ A] (C : Subalgebra ℂ A) (M : M2 A) : Prop := ∀ a b, M a b ∈ C
section Ent
variable {A : Type} [Ring A] [Algebra ℂ A] {C : Subalgebra ℂ A}
theorem Ent.Ts {σ : Site A} (hp : σ.p ∈ C) (hc : σ.c ∈ C) (hci : σ.ci ∈ C) (Y : ℂ) : Ent C (Ts σ Y) := by
  intro a b
  fin_cases a <;> fin_cases b
  · show algebraMap ℂ A Y + σ.p ∈ C
    exact add_mem (C.algebraMap_mem Y) hp
  · show -σ.c ∈ C
    exact neg_mem hc
  · show σ.ci ∈ C
    exact hci
  · show (0 : A) ∈ C
    exact zero_mem C
end Ent
end Formalism.FourierDecayAlt.P.Mx8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


