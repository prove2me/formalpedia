-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
-- name    : ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:19.451972+00:00
-- url     : https://prove2.me/theorems/ba4d117e-fa46-4fb9-b5d8-eefef77dfe2c
-- title:
--   Is Saturated Chain
-- statement:
--   Definitions and structural lemmas for Is Saturated Chain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/IsSaturatedChain.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
universe u
def IsSaturatedChain {R : Type*} [CommRing R] (s : LTSeries (PrimeSpectrum R)) : Prop :=
  ∀ i : Fin s.length, s (Fin.castSucc i) ⋖ s (Fin.succ i)
def IsCatenary (R : Type*) [CommRing R] : Prop :=
  ∀ s s' : LTSeries (PrimeSpectrum R), s.head = s'.head → s.last = s'.last →
    IsSaturatedChain s → IsSaturatedChain s' → s.length = s'.length
def DimFormula (R : Type*) [CommRing R] : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = ringKrullDim R
def IsCMQuot (R : Type u) [CommRing R] : Prop :=
  ∃ (P : Type u) (_ : CommRing P) (_ : IsLocalRing P) (f : P →+* R),
    IsCM P ∧ Function.Surjective f
end ReciprocityTheory.CA


