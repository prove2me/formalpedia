-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:40.861011+00:00
-- url     : https://prove2.me/theorems/a67f7a83-a29b-4504-b202-d4553ae3c09e
-- title:
--   Jacobian Transformation Law
-- statement:
--   Definitions and structural lemmas for Jacobian Transformation Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section F
end F
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
section Law
variable (P)
def CondQ (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) : Prop :=
  (∀ p p', p < n + c → p' < n' + c' → IntAt P (entB q k₀ c' n' c n 0 0 x p p')) ∧
  (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (entB q k₀ c' n' c n 0 0 x p p' / (q : E)))
def AYm (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun s t : Fin r => entB q k₀ c' n' c n 0 0 x s.1 t.1
variable {P}
def GA (k₀ r c n : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun s p : Fin r => atN (g (eN E (n + c) (fIdx k₀ c n p.1))) (fIdx k₀ c n s.1)
variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5
end Law
end PI.TwistedEisensteinNonvanishing.W


