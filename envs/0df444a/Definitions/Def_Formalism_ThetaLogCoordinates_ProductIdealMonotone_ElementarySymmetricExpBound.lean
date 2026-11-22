-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
-- name    : Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:32.262248+00:00
-- url     : https://prove2.me/theorems/0c6f61d4-ed6d-4c77-bcca-79f03ccc6e7d
-- title:
--   Elementary Symmetric Exp Bound
-- statement:
--   Definitions and structural lemmas for Elementary Symmetric Exp Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ElementarySymmetricExpBound.lean

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ParamDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
namespace Formalism.InvariantFactorPaths.G0
open Formalism.G0
def PositivePartLeCount : Prop :=
  ∀ e τ S : ℝ, 0 < S → {β : ℕ | τ + (β : ℝ) * S < e}.Finite ∧
    pp (e - τ) ≤ S * ({β : ℕ | τ + (β : ℝ) * S < e}.ncard : ℝ)
def ElementarySymmetricExpBound : Prop :=
  ∀ (V : ℕ) (κ : Fin V → ℝ) (m : ℝ), (∀ v, 0 ≤ κ v) → 0 ≤ m → m * ∑ v, κ v ≤ 1 / 2 →
    (∀ j : ℕ, m ^ j * esymmR κ j ≤ (m * ∑ v, κ v) ^ j / (j.factorial : ℝ)) ∧
    Summable (fun j : ℕ => (m * ∑ v, κ v) ^ (j + 1) / ((j + 1).factorial : ℝ)) ∧
    ∑' j : ℕ, (m * ∑ v, κ v) ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ 2 * (m * ∑ v, κ v)
def InvariantFactorsSubmodule : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] [Module R X]
    (π : R) (M M' P : Submodule R X) (g E : ℕ), P ≤ M' → M' ≤ M →
    AllButLE π M P g E → AllButLE π M' P g E
def InvariantFactorsQuotient : Prop :=
  ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (π : R) (M P P' : Submodule R X) (g E : ℕ), P ≤ P' →
    AllButLE π M P g E → AllButLE π M P' g E
def InvShift : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] [Module R X]
    (π : R) (A B NA NB : Submodule R X) (g E e : ℕ), B ≤ A → NA ≤ A → π ^ e • NA ≤ NB → NB ≤ B →
    AllButLE π A NA g E → AllButLE π B NB g (E + e)
def ProdIdealMono : Prop :=
  ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (π : R) (V : ℕ) (A B : Submodule R X)
    (y : Fin V → Module.End R X) (m e : ℕ) (Sv : Fin V → ℕ),
    (π ^ e • A ≤ B → π ^ e • prodIdealMap π y m Sv A ≤ prodIdealMap π y m Sv B) ∧
    ((∀ v, ∀ x ∈ B, y v x ∈ B) → prodIdealMap π y m Sv B ≤ B)
def G1a : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] [Module R X]
    (π : R), Irreducible π → ∀ (V : ℕ) (A B W : Submodule R X) (y : Fin V → Module.End R X)
    (m S d e τ : ℕ) (Sv : Fin V → ℕ) (κ : Fin V → ℝ),
    Module.Free R A → Module.Finite R A → Module.finrank R A = d →
    B ≤ A → π ^ e • A ≤ B →
    (∀ v, ∀ x ∈ A, y v x ∈ A) → (∀ v, ∀ x ∈ B, y v x ∈ B) →
    (∀ x : X, π • x ∈ W → x ∈ W) →
    (∀ v, Sv v ≤ S) → (∀ v, 0 ≤ κ v) → (m : ℝ) * ∑ v, κ v ≤ 1 / 2 →
    (∀ β : ℕ, ∃ g : ℕ, (g : ℝ) ≤ d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) ∧
      AllButLE π A (prodIdealMap π y m Sv A) g (τ + β * S)) →
    prodIdealMap π y m Sv B ⊓ π ^ (e + τ) • B ⊓ W ≤ π ^ (e + τ) • (B ⊓ W) ∧
    ∃ ℓ : ℕ, Module.length R ((B ⊓ W : Submodule R X) ⧸
        (prodIdealMap π y m Sv B ⊓ π ^ (e + τ) • B ⊓ W).comap (B ⊓ W).subtype) = ℓ ∧
      (ℓ : ℝ) ≤ d * (((e + τ : ℕ) : ℝ) + 2 * S * ((m : ℝ) * ∑ v, κ v))
def GenGain : Prop :=
  ∀ (m : ℕ) (g Pr g0 : Fin m → ℝ) (S : ℝ), (∑ j, pp (g j - Pr j - g0 j)) ≤ S →
    (∑ j, max (g j - Pr j) (g0 j)) ≤ S + ∑ j, g0 j
def AlmostEverywhereSpherical : Prop :=
  ∀ {R X Z : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Z] [Module R Z]
    (π : R) (vπ : ℝ) (V m : ℕ) (M : Submodule R X) (y : Fin V → Module.End R X) (Sv : Fin V → ℕ)
    (K : X →ₗ[R] Z) (Fil : ℝ → Submodule R Z) (g Pr g0 : Fin V → Fin m → ℝ) (rest : ℝ),
    Antitone Fil → (∀ t z, z ∈ Fil t → π • z ∈ Fil (t + vπ)) →
    (∀ v, (∑ j, pp (g v j - Pr v j - g0 v j)) ≤ vπ * (Sv v : ℝ)) →
    (∀ E : Fin V → Bool, ∀ F ∈ M, K (monoOp π y m (fun _ => 0) E F) ∈
      Fil ((∑ j, ((∑ v with E v = true, max (g v j - Pr v j) (g0 v j)) + ∑ v with E v = false, g0 v j)) + rest)) →
    ∀ F ∈ prodIdealMap π y m Sv M, K F ∈ Fil ((∑ j, ∑ v, max (g v j - Pr v j) (g0 v j)) + rest)
def SizeOfSingularValues : Prop :=
  ∀ (n m : ℕ) (G : Glob) (O : Orb n m) (Pr : Fin m → ℝ) (th : ℝ),
    5 ≤ G.p → 10 * G.p ≤ 9 * G.a → th ≤ 1 / 125 → 1 ≤ m → 1 ≤ O.T.card →
    (∀ s ∈ O.T, 0 ≤ al G O s ∧ al G O s ≤ G.a * (1 + th)) → (∀ j z, 0 ≤ cap G O j z) → (∀ j, 0 ≤ Pr j) →
    (0 : ℝ) ≤ ((⌈∑ j, pp (gg G O j - Pr j - g0 G O j)⌉ : ℤ) : ℝ) ∧
    ((⌈∑ j, pp (gg G O j - Pr j - g0 G O j)⌉ : ℤ) : ℝ) ≤ (m : ℝ) * gam G.p * (∑ s ∈ O.T, al G O s) + 1 ∧
    (m : ℝ) * gam G.p * (∑ s ∈ O.T, al G O s) + 1 ≤ 2 * (m : ℝ) * (O.T.card : ℝ) * G.a / G.p
end Formalism.InvariantFactorPaths.G0


