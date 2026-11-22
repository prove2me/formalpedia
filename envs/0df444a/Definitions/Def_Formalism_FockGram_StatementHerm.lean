-- Prove2me | Definitions.Def_Formalism_FockGram_StatementHerm
-- name    : Formalism_FockGram_StatementHerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:16.138712+00:00
-- url     : https://prove2.me/theorems/9e6b61a7-afeb-48a5-826e-5b95672a5689
-- title:
--   Statement Herm
-- statement:
--   Definitions and structural lemmas for Statement Herm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/StatementHerm.lean

import Definitions.Def_Formalism_FockGram_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix LinearMap Module
noncomputable section
namespace Formalism.E
def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)
def HermDual : Prop :=
  ∀ (S K V ι : Type) [CommRing S] [Field K] [StarRing K] [Algebra S K]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower S K V] [Fintype ι] [DecidableEq ι]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V),
    Function.Injective (algebraMap S K) →
    (∀ s : S, star (algebraMap S K s) ∈ Set.range (algebraMap S K)) →
    (Submodule.span S (Set.range b) ≤ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i j, B (b i) (b j) ∈ Set.range (algebraMap S K)) ∧
    ∀ [Module.Free ℤ S] [Module.Finite ℤ S] (GS : Matrix ι ι S),
      (∀ i j, B (b i) (b j) = algebraMap S K (GS i j)) → GS.det ≠ 0 →
      (Submodule.span S (Set.range b)).toAddSubgroup.relIndex
          (hdual B (Submodule.span S (Set.range b))).toAddSubgroup =
        (Algebra.norm ℤ GS.det).natAbs ∧
      (hdual B (Submodule.span S (Set.range b)) = Submodule.span S (Set.range b) ↔
        IsUnit GS.det)
def HermTraceGram : Prop :=
  ∀ (S M ι κ : Type) [CommRing S] [StarRing S] [AddCommGroup M] [Module S M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : M →ₗ⋆[S] M →ₗ[S] S) (b : Basis ι S M) (ω : Basis κ ℤ S),
    (Matrix.of fun p q : ι × κ => Algebra.trace ℤ S (B (ω p.2 • b p.1) (ω q.2 • b q.1))).det =
      (Matrix.of fun k l : κ => Algebra.trace ℤ S (star (ω k) * ω l)).det ^ Fintype.card ι *
        Algebra.norm ℤ (sgram B b).det
end Formalism.E


