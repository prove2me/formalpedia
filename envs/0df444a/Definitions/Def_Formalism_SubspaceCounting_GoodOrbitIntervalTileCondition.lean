-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
-- name    : Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:24.220877+00:00
-- url     : https://prove2.me/theorems/a353dd44-d406-4e47-8f17-09fc0246e297
-- title:
--   Good Orbit Interval Tile Condition
-- statement:
--   Definitions and structural lemmas for Good Orbit Interval Tile Condition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.G0
def cell (r u s c : ℕ) : Finset ℕ :=
  Finset.Ico (s * ((6 * r + 1) * u) + (c - 1) * u) (s * ((6 * r + 1) * u) + c * u)
def Marked (T : Finset ℕ) (r u s : ℕ) : Prop :=
  ∀ c, 1 ≤ c → c ≤ 6 * r + 1 →
    (Odd c → T ∩ cell r u s c = ∅) ∧
    (Even c → ∃ x, T ∩ cell r u s c = {x} ∧ Even x)
def CondTiles (n : ℕ) (T : Finset ℕ) (r u M₀ : ℕ) : Prop :=
  ∀ s₀ < n / ((6 * r + 1) * u), ∃ j ≤ M₀, Marked T r u ((s₀ + j) % (n / ((6 * r + 1) * u)))
def CondIntervals (n : ℕ) (T : Finset ℕ) (G' N₁ : ℕ) : Prop :=
  ∀ i < n, (T ∩ window n i G').card ≤ N₁
def GoodOrbitIntervalTileCondition (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ) : Prop :=
  CondA n T L₂ K ∧ CondTiles n T r u M₀ ∧ CondIntervals n T G' N₁
def binUpper (G : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j)
def markedBound (δ : ℝ) (r u : ℕ) : ℝ :=
  ((1 - δ) ^ u) ^ (3 * r + 1) * (((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) ^ (3 * r)
def condProbAt (n : ℕ) (δ : ℝ) (i₀ : ℕ) (A : Finset ℕ → Prop) : ℝ := by
  classical
  exact ∑ T ∈ (Finset.range n).powerset,
    if i₀ ∈ T ∧ A T then δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) else 0
def TileConditionFailureProbBound : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (L₂ K r u M₀ G' N₁ i₀ : ℕ), 0 ≤ δ → δ ≤ 1 → 1 ≤ r → 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → i₀ < n →
    condProbAt n δ i₀ (fun T => ¬ GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁) ≤
      n * (L₂.choose K : ℝ) * δ ^ K + n * (1 - markedBound δ r u) ^ M₀ +
      n * binUpper G' δ (N₁ - 1)
def MarkedRun : Prop :=
  ∀ (T : Finset ℕ) (r u s : ℕ), 1 ≤ u → Marked T r u s →
    ∃ f : Fin (3 * r) → ℕ, StrictMono f ∧
      T ∩ Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) =
        Finset.univ.image f ∧
      (∀ i, Even (f i)) ∧
      (∀ (i : Fin (3 * r)) (h : i.val + 1 < 3 * r), f i + u < f ⟨i.val + 1, h⟩) ∧
      (∀ i, s * ((6 * r + 1) * u) + u ≤ f i ∧ f i + u < (s + 1) * ((6 * r + 1) * u))
def ManyOrbitsRefined : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (V : ℕ) (π : R), Irreducible π →
    ∀ (L : (Fin V → Slot) → Submodule R X) (y : Fin V → Module.End R X)
    (m c₀ S d : ℕ) (a b c Sv : Fin V → ℕ) (κ : Fin V → ℝ)
    (G : Finset (Fin V) → Finset X),
    [Module.Free R (L fun _ => Slot.base)] → [Module.Finite R (L fun _ => Slot.base)] →
    Module.finrank R (L fun _ => Slot.base) = d →
    1 ≤ m →
    (∀ v w, Commute (y v) (y w)) →
    (∀ σ v, L (Function.update σ v Slot.base) ≤ L (Function.update σ v Slot.ball)) →
    (∀ σ v, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ a v • x ∈ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.base),
      π ^ b v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ c v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      y v x ∈ L (Function.update σ v Slot.dual)) →
    (∀ B : Finset (Fin V), 1 ≤ B.card →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ ((G B).card : ℝ) ≤ (∏ v ∈ B, κ v) * d ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X)) →
    (∀ v, 0 ≤ κ v) → (∀ v, a v + b v ≤ c v) → (∀ v, Sv v ≤ S) →
    (m : ℝ) * ∑ v, κ v ≤ 1 / 2 →
    (∀ β : ℕ, ∃ C : Finset X, (↑C : Set X) ⊆ L (fun _ => Slot.base) ∧
        (C.card : ℝ) ≤ d * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) ∧
        ∀ x ∈ L (fun _ => Slot.base), π ^ (∑ v, m * (c v + c₀) + β * S) • x ∈
          prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X)) ∧
    AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
      (∑ v, Sv v) ∧
    ∃ ℓ : ℕ, Module.length R ((L fun _ => Slot.base) ⧸ Submodule.comap
        (L fun _ => Slot.base).subtype
        (prodIdealMap π y m Sv (L fun _ => Slot.base) ⊓
          (Ideal.span {π ^ (∑ v, m * (c v + c₀))}) • (L fun _ => Slot.base))) = ℓ ∧
      (ℓ : ℝ) ≤ d * ((∑ v, m * (c v + c₀) : ℕ) + 2 * S * (m * ∑ v, κ v))
end Formalism.G0


