-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_Statement
-- name    : Formalism_WachLatticeTwists_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:21.352391+00:00
-- url     : https://prove2.me/theorems/213ac166-38d6-46ec-a664-3579025c95da
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/Statement.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.RepresentationBoundsCohomology
def negCount (s : Multiset ℤ) : ℕ := Multiset.card (s.filter (fun u => u < 0))
def StatRowColength : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    (I : Submodule O M) (ℓ e : ℕ),
    (∀ m : M, ((ℓ : O) ^ e) • m ∈ I) →
    Module.length O (M ⧸ I) ≤
      (Module.finrank O M : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) +
        Module.length O (Submodule.torsion O M)
def SubmoduleLengthBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] (N : Submodule O (d → Formalism.NG.KO O)) (ℓ c : ℕ),
    (∀ x ∈ N, ((ℓ : O) ^ c) • x = 0) →
    Module.length O N ≤
      (Fintype.card d : ℕ∞) * ((c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}))
def StatJumpsColumn : Prop :=
  ∀ (ι : Type*) [Fintype ι] (cloud lows : ι → Multiset ℤ) (m j h0 : ℕ),
    (∀ τ, ∀ u ∈ cloud τ, 0 < u) → (∀ τ, Multiset.card (lows τ) ≤ m) →
    j = h0 + ∑ τ, negCount (cloud τ + lows τ) → h0 = 0 →
    j ≤ Fintype.card ι * m
def StatJumpsRow : Prop :=
  ∀ (ι : Type*) [Fintype ι] (cloud lows : ι → Multiset ℤ) (m j h0 : ℕ),
    (∀ τ, ∀ u ∈ cloud τ, u < 0) → (∀ τ, Multiset.card (lows τ) ≤ m) →
    j = h0 + ∑ τ, negCount ((cloud τ + lows τ).map (fun u => -u - 1)) → h0 = 0 →
    j ≤ Fintype.card ι * m
end Formalism.RepresentationBoundsCohomology


