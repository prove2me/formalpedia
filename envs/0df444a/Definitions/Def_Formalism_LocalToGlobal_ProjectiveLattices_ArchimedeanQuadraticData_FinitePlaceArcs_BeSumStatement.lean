-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:09.516097+00:00
-- url     : https://prove2.me/theorems/9aab1629-fc26-4808-b7db-e8283379cc05
-- title:
--   Be Sum Statement
-- statement:
--   Definitions and structural lemmas for Be Sum Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumStatement.lean

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
namespace Formalism.L2.Pj.QAt
open NumberField IsDedekindDomain
def vla {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk la.asIdeal).count (Associates.mk I).factors
def discAt (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] : Ideal (𝓞 K) :=
  Ideal.span {(((discr E).natAbs : ℕ) : 𝓞 K)}
def mOf (E : Type) [Field E] [NumberField E] {K : Type} [Field K] [NumberField K] (n' : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  max (vla la (discAt E K)) (vla la (Ideal.span {(n' : 𝓞 K)}))
def beOf (E : Type) [Field E] [NumberField E] {K : Type} [Field K] [NumberField K] (n' A : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (A : ℝ) * (mOf E n' la : ℝ)
def lrdOf (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log (|((NumberField.discr E : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))
def BeSumStatement : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (n' A : ℕ), 0 < n' →
    (Function.support (beOf E (K := K) n' A)).Finite ∧
    (∑ᶠ la, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ)) / (Module.finrank ℚ K : ℝ) ≤
      (Real.log |((discr E : ℤ) : ℝ)| + Real.log n') * A
end Formalism.L2.Pj.QAt


