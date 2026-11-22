-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementMult
-- name    : Formalism_CharacterColumnKernels_StatementMult
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:53.305225+00:00
-- url     : https://prove2.me/theorems/82e8e039-3032-4f99-b5d0-6891df41f475
-- title:
--   Statement Mult
-- statement:
--   Definitions and structural lemmas for Statement Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementMult.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
namespace Formalism.NG
universe u v
section Mult
variable (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]
abbrev csFactor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) : Type u :=
  s i.succ ⧸ (s (Fin.castSucc i)).comap (s i.succ).subtype
def csMult (s : CompositionSeries (Submodule R M)) (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  (Finset.univ.filter fun i : Fin s.length => Nonempty (csFactor R M s i ≃ₗ[R] S)).card
def IsFullSeries (s : CompositionSeries (Submodule R M)) : Prop := s.head = ⊥ ∧ s.last = ⊤
def compMult (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  if h : ∃ s : CompositionSeries (Submodule R M), IsFullSeries R M s then
    csMult R M (Classical.choose h) S
  else 0
end Mult
def StatCsMultIndep : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S] (s₁ s₂ : CompositionSeries (Submodule R M)),
    IsFullSeries R M s₁ → IsFullSeries R M s₂ → csMult R M s₁ S = csMult R M s₂ S
def StatCompMultEq : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S] (s : CompositionSeries (Submodule R M)),
    IsFullSeries R M s → compMult R M S = csMult R M s S
def StatEpsMult : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [Ring Λ] [Algebra O Λ] [AddCommGroup M]
    [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S] [Module Λ S] (ε : Λ),
    IsIdempotentElem ε →
    (∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0) →
    IsFiniteLength Λ M →
    Module.length O (epsImg O (M := M) ε) = compMult Λ M S
def StatEpsMultHom : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Ring Λ] [Algebra O Λ] [AddCommGroup M]
    [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S] [Module Λ S] (ε : Λ),
    IsIdempotentElem ε → [SMulCommClass Λ O (EpsDual O Λ (KO O) ε)] →
    (∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0) →
    IsFiniteLength Λ M →
    Module.length O (M →ₗ[Λ] EpsDual O Λ (KO O) ε) = compMult Λ M S
end Formalism.NG


