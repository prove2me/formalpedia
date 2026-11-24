-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:12.218634+00:00
-- url     : https://prove2.me/theorems/56f7d8b4-5444-40de-800b-11a4be2117d9
-- title:
--   Statement P
-- statement:
--   Definitions and structural lemmas for Statement P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/StatementP.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_DetIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
def IsBaseChangeLine {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K)
    (L1 : MLine K1) : Prop :=
  ((L1.I : Submodule (𝓞 K1) K1) = Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ L.I})) ∧
  ∀ σ : K1 →+* ℂ, L1.n σ = L.n (σ.comp (algebraMap K K1))
def NdegBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1),
    L.Good → IsBaseChangeLine L L1 → L1.Good ∧ L1.ndeg = L.ndeg
def BaseChangeExists : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K),
    ∃ L1 : MLine K1, IsBaseChangeLine L L1
def LocGenBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1)
    (p : HeightOneSpectrum (𝓞 K)) (p1 : HeightOneSpectrum (𝓞 K1)) (c : K), L.I ≠ 0 → IsBaseChangeLine L L1 →
    (∀ a : 𝓞 K, a ∈ p.asIdeal ↔ (algebraMap (𝓞 K) (𝓞 K1) a) ∈ p1.asIdeal) → IsLocGen p c L.I →
    IsLocGen p1 (algebraMap K K1 c) L1.I
end Formalism.L2.LamCM


