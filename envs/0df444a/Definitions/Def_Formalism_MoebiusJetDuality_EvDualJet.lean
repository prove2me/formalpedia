-- Prove2me | Definitions.Def_Formalism_MoebiusJetDuality_EvDualJet
-- name    : Formalism_MoebiusJetDuality_EvDualJet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:48.935081+00:00
-- url     : https://prove2.me/theorems/888b5661-1cac-4463-ba84-79fa1504d31a
-- title:
--   Ev Dual Jet
-- statement:
--   Definitions and structural lemmas for Ev Dual Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MoebiusJetDuality/EvDualJet.lean

import Definitions.Def_Formalism_MoebiusJetDuality_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MJ
open MvPolynomial
universe u v
def EvDualJet : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (F : MvPolynomial σ R),
    (∀ P : MvPolynomial σ R, IsIntegralJet A P → evOp P F ∈ A) ↔
      ∀ α, (mfac α : R) * coeff α F ∈ A
def EvDualOp : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (P : MvPolynomial σ R),
    (∀ F : MvPolynomial σ R, IsIntegralJet A F → evOp P F ∈ A) ↔
      ∀ α, (mfac α : R) * coeff α P ∈ A
def EvKernel : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (F : MvPolynomial σ R),
    (∀ P : MvPolynomial σ R, evOp P F = 0) ↔ ∀ α, (mfac α : R) * coeff α F = 0
def EvSymm : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (P F : MvPolynomial σ R), evOp P F = evOp F P
def EvLinear : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (c : R) (P F G : MvPolynomial σ R),
    evOp P (c • F + G) = c * evOp P F + evOp P G
def EvDegree : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (P F : MvPolynomial σ R) (m n : ℕ),
    P.IsHomogeneous m → F.IsHomogeneous n → m ≠ n → evOp P F = 0
end Formalism.MJ


