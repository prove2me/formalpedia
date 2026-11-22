-- Prove2me | Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- name    : Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:21:44.644165+00:00
-- url     : https://prove2.me/theorems/3cb2cf29-c784-4cf9-ad92-fb4204080c70
-- title:
--   Count O
-- statement:
--   Definitions and structural lemmas for Count O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.SLP.P
namespace CountO
section DedekindLFunctions
variable {R : Type} [CommRing R] [IsDedekindDomain R]
end DedekindLFunctions
section DedekindLFunctions
variable {R : Type} [CommRing R] [IsDedekindDomain R]
def hyp (P : Ideal R) (X : Type) [AddCommGroup X] [Module R X] : Set (Submodule R X) :=
  {L | P • ⊤ ≤ L ∧ L.toAddSubgroup.index = Nat.card (R ⧸ P)}
end DedekindLFunctions
section Mul
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
def idxSet (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (m : ℕ) :
    Set (Submodule R X) :=
  {N | N.toAddSubgroup.index = m}
def mulSub (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (c : ℕ) : Submodule R X :=
  LinearMap.range (c • (LinearMap.id : X →ₗ[R] X))
end Mul
section NF
open NumberField
variable (E : Type) [Field E] [NumberField E]
def TF (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Prop :=
  ∀ a : 𝓞 E, a ≠ 0 → ∀ x : X, a • x = 0 → x = 0
def LIB (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (k : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (v : ι → X), LinearIndependent (𝓞 E) v → Fintype.card ι ≤ k
variable {E}
end NF
end CountO
end Formalism.SLP.P


