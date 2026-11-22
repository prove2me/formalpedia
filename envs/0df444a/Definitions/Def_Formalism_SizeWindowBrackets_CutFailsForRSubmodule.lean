-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_CutFailsForRSubmodule
-- name    : Formalism_SizeWindowBrackets_CutFailsForRSubmodule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:37.886802+00:00
-- url     : https://prove2.me/theorems/986111a3-bf8b-4c42-98f4-9765e8619fda
-- title:
--   Cut Fails For RSubmodule
-- statement:
--   Definitions and structural lemmas for Cut Fails For RSubmodule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/CutFailsForRSubmodule.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.DiagonalSublatticeLength
open scoped Pointwise
section defs
variable {R K W : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup W] [Module K W] [Module R W]
  [IsScalarTower R K W]
def latV (M : Submodule R W) (V : Submodule K W) : Submodule R W :=
  M ⊓ V.restrictScalars R
def cutN (ϖ : R) (τ : ℕ) (M N : Submodule R W) (V : Submodule K W) : Submodule R W :=
  N ⊓ ϖ ^ τ • M ⊓ V.restrictScalars R
end defs
def LemmaC : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Type) [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W] [FiniteDimensional K W]
    (d : ℕ) (M : Submodule R W) (b : Module.Basis (Fin d) R M), Submodule.span K (M : Set W) = ⊤ →
  ∀ (e : Fin d → ℕ) (N : Submodule R W), N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W)) →
  ∀ (τ : ℕ) (V : Submodule K W),
    cutN ϖ τ M N V ≤ ϖ ^ τ • latV M V ∧
    (ϖ ^ τ • M) ⊓ V.restrictScalars R = ϖ ^ τ • latV M V ∧
    Module.length R (latV M V ⧸ (cutN ϖ τ M N V).comap (latV M V).subtype) ≤
      ((Module.finrank R (latV M V) * τ + ∑ i, (e i - τ) : ℕ) : ℕ∞)
def ClaimC : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Type) [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W] [FiniteDimensional K W]
    (d : ℕ) (M : Submodule R W) (b : Module.Basis (Fin d) R M), Submodule.span K (M : Set W) = ⊤ →
  ∀ (e : Fin d → ℕ) (N : Submodule R W), N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W)) →
  ∀ (τ : ℕ) (V : Submodule K W),
    Module.length R ((ϖ ^ τ • latV M V : Submodule R W) ⧸
        (cutN ϖ τ M N V).comap (ϖ ^ τ • latV M V : Submodule R W).subtype) ≤ ((∑ i, (e i - τ) : ℕ) : ℕ∞) ∧
    Module.length R (latV M V ⧸ (ϖ ^ τ • latV M V).comap (latV M V).subtype) =
      ((Module.finrank R (latV M V) * τ : ℕ) : ℕ∞)
def CutFailsForRSubmodule : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K],
    let M : Submodule R K := Submodule.span R {1}
    let V : Submodule R K := Submodule.span R {algebraMap R K ϖ}
    ϖ • M ⊓ V ≠ ϖ • (M ⊓ V)
end Formalism.LFunctionChainParameters.DiagonalSublatticeLength


