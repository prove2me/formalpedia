-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:14:16.156128+00:00
-- url     : https://prove2.me/theorems/8543d186-8274-4c74-8d06-c122cfd8b326
-- title:
--   Admissible Of Places
-- statement:
--   Definitions and structural lemmas for Admissible Of Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
namespace Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
section pull
end pull
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
section words
def pw (A : Finset (Fin S.f)) (w : S.W) (θ : Fin S.f → List C.Letter → ℝ) (v : Fin S.f) (a : List C.Letter) : ℝ :=
  if v ∈ A then θ v a else if a = w.1 v then 1 else 0
def pθ (A : Finset (Fin S.f)) (w : S.W) (θ : Fin S.f → List C.Letter → ℝ) (w' : S.W) : ℝ :=
  ∏ v, pw S A w θ v (w'.1 v)
def supp (A : Finset (Fin S.f)) (w : S.W) (U : Fin S.f → Finset (List C.Letter)) (v : Fin S.f) :
    Finset (List C.Letter) :=
  if v ∈ A then U v else {w.1 v}
variable {S}
section hyps
variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}
end hyps
end words
end
end Formalism.FourierDecayAlt.P.PBA


