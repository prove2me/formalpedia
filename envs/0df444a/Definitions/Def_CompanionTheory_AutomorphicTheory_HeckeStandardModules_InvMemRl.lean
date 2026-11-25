-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
-- name    : CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:06.497154+00:00
-- url     : https://prove2.me/theorems/c8b29ded-b63c-5f78-af51-8c5e3cd4124d
-- title:
--   Inv Mem Rl
-- statement:
--   Definitions and structural lemmas for Inv Mem Rl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
namespace CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
section R
variable (l : ℕ) [hl : Fact l.Prime]
instance span_prime : (Ideal.span {(l : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
abbrev Rl : Subalgebra ℤ ℚ :=
  Localization.subalgebra.ofField ℚ (Ideal.span {(l : ℤ)}).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)
variable {l}
end R
section Eig
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}
def M0 (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ) : Submodule (Rl l) ℂ :=
  Submodule.span (Rl l) (Set.range fun p : (L →+* ℂ) × Module.Free.ChooseBasisIndex ℤ (𝓞 L) =>
    p.1 (RingOfIntegers.basis L p.2 : L) / (c : ℂ) ^ 2)
end Eig
end CompanionTheory.L3H
namespace ReciprocityTheory.ChartRestriction.L3H
open CompanionTheory.L3H
end ReciprocityTheory.ChartRestriction.L3H


