-- Prove2me | Definitions.Def_GirvingAKS_Separator_Defs
-- name    : GirvingAKS_Separator_Defs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:19.389116+00:00
-- url     : https://prove2.me/theorems/72e1caab-7029-4ced-a9e8-771aeb7e903a
-- title:
--   AKS sorting networks (Seiferas port) — (γ, ε)-Separator Definitions
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Separator/Defs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Defines ε-approximate γ-separation (Seiferas 2009, Section 6), the separator-based reformulation of the AKS sorting network correctness proof.
--
--   Key definitions:
--
--   - `SepInitial`, `SepFinal`: one-sided separation properties
--   - `IsApproxSep`: both-sided separation
--   - `IsSeparator`: network-level separator property (quantified over permutations)
--
--   For γ = 1/2, this reduces to ε-halving (`IsEpsilonHalver` in `Halver/Defs.lean`).
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Separator/Defs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs
import Definitions.Def_GirvingAKS_Misc_Fin

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Separator/Defs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # (γ, ε)-Separator Definitions

  Defines ε-approximate γ-separation (Seiferas 2009, Section 6), the
  separator-based reformulation of the AKS sorting network correctness proof.

  Key definitions:
  - `SepInitial`, `SepFinal`: one-sided separation properties
  - `IsApproxSep`: both-sided separation
  - `IsSeparator`: network-level separator property (quantified over permutations)

  For γ = 1/2, this reduces to ε-halving (`IsEpsilonHalver` in `Halver/Defs.lean`).
-/


section


open Finset BigOperators

/-! **ε-Approximate γ-Separation (Seiferas 2009, Section 6)** -/

/-- ε-approximate γ-separation, initial direction (Seiferas 2009, Section 6).
    For each γ' ≤ γ, at most ε·γ'·n of the ⌊γ'·n⌋ smallest output values
    are NOT placed among the first ⌊γ·n⌋ positions.

    In the filter, `pos` is an output position and `w pos` is the value there:
    • `rank (w pos) < ⌊γ' * n⌋₊` selects the ⌊γ'n⌋ smallest elements (by value)
    • `⌊γ * n⌋₊ ≤ rank pos` selects positions outside the first ⌊γn⌋ (by index) -/
def SepInitial {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (γ ε : ℝ) : Prop :=
  let n := Fintype.card α
  ∀ γ' : ℝ, 0 ≤ γ' → γ' ≤ γ →
    ((Finset.univ.filter (fun pos : α ↦
        ⌊γ * ↑n⌋₊ ≤ rank pos ∧ rank (w pos) < ⌊γ' * ↑n⌋₊)).card : ℝ) ≤ ε * γ' * ↑n

/-- ε-approximate γ-separation, final direction: dual via order reversal. -/
def SepFinal {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (γ ε : ℝ) : Prop :=
  SepInitial (α := αᵒᵈ) w γ ε

/-- ε-approximate γ-separation (Seiferas 2009, Section 6): both directions. -/
def IsApproxSep {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (γ ε : ℝ) : Prop :=
  SepInitial w γ ε ∧ SepFinal w γ ε

/-- A comparator network is a (γ, ε)-separator if for every permutation input,
    the output satisfies ε-approximate γ-separation. -/
def IsSeparator {n : ℕ} (net : ComparatorNetwork n) (γ ε : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin n)), IsApproxSep (net.exec v) γ ε


/-! **Monotonicity** -/

/-- `SepInitial` is monotone in ε: increasing ε weakens the bound. -/
theorem SepInitial_mono_ε {α : Type*} [Fintype α] [LinearOrder α]
    {w : α → α} {γ ε₁ ε₂ : ℝ}
    (h : SepInitial w γ ε₁) (hle : ε₁ ≤ ε₂) :
    SepInitial w γ ε₂ := by
  intro γ' hγ' hγ'_le
  calc _ ≤ ε₁ * γ' * ↑(Fintype.card α) := h γ' hγ' hγ'_le
    _ ≤ ε₂ * γ' * ↑(Fintype.card α) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hle hγ'

/-- `IsSeparator` is monotone in ε: increasing ε weakens the bound. -/
theorem IsSeparator_mono_ε {n : ℕ} {net : ComparatorNetwork n} {γ ε₁ ε₂ : ℝ}
    (h : IsSeparator net γ ε₁) (hle : ε₁ ≤ ε₂) :
    IsSeparator net γ ε₂ := by
  intro v
  obtain ⟨h_init, h_final⟩ := h v
  exact ⟨SepInitial_mono_ε h_init hle, SepInitial_mono_ε h_final hle⟩

end


