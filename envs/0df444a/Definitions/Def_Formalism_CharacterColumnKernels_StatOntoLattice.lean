-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
-- name    : Formalism_CharacterColumnKernels_StatOntoLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:45.700203+00:00
-- url     : https://prove2.me/theorems/df8c8d5f-9487-4747-b2bd-2e90371f0f16
-- title:
--   Stat Onto Lattice
-- statement:
--   Definitions and structural lemmas for Stat Onto Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatOntoLattice.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.NG
universe u
def StatBurnside : Prop :=
  ∀ (k A V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V], IsSimpleModule A V →
    (∀ φ : V →ₗ[A] V, ∃ c : k, ∀ v, φ v = c • v) →
    Function.Surjective (fun a : A => DistribSMul.toLinearMap k V a)
def StatOntoLattice : Prop :=
  ∀ (O A L : Type*) [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A] [AddCommGroup L] [Module O L]
    [Module.Free O L] [Module.Finite O L] (φ : A →ₐ[O] Module.End O L),
    (∀ f : Module.End O L, ∃ a : A,
      f - φ a ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O (Module.End O L))) →
    Function.Surjective φ
def IdempotentLift : Prop :=
  ∀ (O A B : Type*) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Ring A] [Algebra O A] [Module.Finite O A]
    [Ring B] (f : A →+* B), Function.Surjective f →
    (∀ x : A, f x = 0 → ∃ n : ℕ, x ^ n ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O A)) →
    ∀ e₁ e₂ : B, IsIdempotentElem e₁ → IsIdempotentElem e₂ → e₁ * e₂ = 0 → e₂ * e₁ = 0 →
      ∃ E₁ E₂ : A, IsIdempotentElem E₁ ∧ IsIdempotentElem E₂ ∧ E₁ * E₂ = 0 ∧ E₂ * E₁ = 0 ∧
        f E₁ = e₁ ∧ f E₂ = e₂
def StatRankMod : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsLocalRing O] (r : Type) [Fintype r] [DecidableEq r]
    (e : Matrix r r O), IsIdempotentElem e →
    (e.map (IsLocalRing.residue O)).rank = (e.map (algebraMap O (FractionRing O))).rank
def StatSplitAlg : Prop :=
  ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin P.natDegree → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = P.natDegree.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin P.natDegree → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃! φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i
def StatSplitFibre : Prop :=
  ∀ (T T' K : Type*) [CommRing T] [CommRing T'] [Algebra T T'] [Field K] (P : T[X]), P.Monic →
    ∀ (rr : Fin P.natDegree → T'), P.map (algebraMap T T') = ∏ i, (X - C (rr i)) →
      Algebra.adjoin T (Set.range rr) = ⊤ →
    ∀ (b : Module.Basis (Fin P.natDegree.factorial) T T') (x : T →+* K) (a : Fin P.natDegree → K),
      Function.Injective a → P.map x = ∏ i, (X - C (a i)) →
      ∀ c : Fin P.natDegree.factorial → K,
        (∀ φ : T' →+* K, φ.comp (algebraMap T T') = x → ∑ k, c k * φ (b k) = 0) → c = 0
end Formalism.NG


