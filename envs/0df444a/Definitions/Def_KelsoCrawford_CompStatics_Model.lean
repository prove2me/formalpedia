-- Prove2me | Definitions.Def_KelsoCrawford_CompStatics_Model
-- name    : KelsoCrawford_CompStatics_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:22.737748+00:00
-- url     : https://prove2.me/theorems/d3bdb77d-fead-4720-b01e-488014a40ae7
-- title:
--   Section 2 and Section 5 — job-matching markets, discrete core, no-ties conditions, and market changes
-- statement:
--   A finite job-matching market has workers, firms, a worker's utility from each firm at each salary, each firm's gross product from any set of workers, and a starting salary for each worker–firm pair. A firm's profit is its product less the salaries of its hires:
--
--   $$\pi^j(C;s)=y^j(C)-\sum_{i\in C}s_i.$$
--
--   The definitions include demanded worker sets, gross substitutes on a specified set of salary vectors, regular utilities, the marginal-product and no-free-lunch conditions, the salary grid, allocations, individual rationality, the discrete core and strict core, and the two no-ties conditions (NTW) and (NTF). A firm-augmented market keeps every original firm's data and adds one firm. A worker-diminished market restricts the workers and each production function to sets excluding the removed worker.
--
--   These definitions fix the objects compared in Theorem 5 and are reusable for the other results of the paper.
--
--   **Formalization Note** Every worker is assigned to a firm in an allocation; the worker-diminished market uses a subtype of the original workers. Permitted salaries are $\sigma_{ij}+k\delta$ for natural $k$. The paper's Section 5 treats starting salaries independently of unemployment utility, so no reservation-salary equality is imposed here.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1486–1488, Section 2 (MP), (NFL), (GS), D1–D3; p. 1494, (NTW), (NTF); pp. 1496–1497, discrete and augmented/diminished markets. https://doi.org/10.2307/1913392

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model

namespace KelsoCrawford.CompStatics

structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

def Market.UtilityRegular {W F : Type} (M : Market W F) : Prop :=
  ∀ i j, StrictMono (M.u i j) ∧ Continuous (M.u i j)

def Market.MP {W F : Type} [DecidableEq W] (M : Market W F) : Prop :=
  ∀ i j (C : Finset W), i ∉ C →
    0 ≤ M.y j (insert i C) - M.y j C - M.σ i j

def Market.NFL {W F : Type} [DecidableEq W] (M : Market W F) : Prop :=
  ∀ j, M.y j ∅ = 0

def Market.grid {W F : Type} (M : Market W F) (δ : ℝ)
    (i : W) (j : F) : Set ℝ :=
  {r | ∃ k : ℕ, r = M.σ i j + k * δ}

def Market.gridVectors {W F : Type} (M : Market W F) (δ : ℝ)
    (j : F) : Set (W → ℝ) :=
  {s | ∀ i, s i ∈ M.grid δ i j}

structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

noncomputable def Allocation.hired {W F : Type} [Fintype W] [DecidableEq W]
    (A : Allocation W F) (j : F) : Finset W := by
  classical
  exact Finset.univ.filter (fun i => A.assign i = j)

def Market.IsIR {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ KelsoCrawford.OneSided.profit (M.y j) (A.hired j) A.sal

def Market.CanImprove {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
    KelsoCrawford.OneSided.profit (M.y j) (A.hired j) A.sal ≤ KelsoCrawford.OneSided.profit (M.y j) C r ∧
    ((∃ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∨
      KelsoCrawford.OneSided.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.OneSided.profit (M.y j) C r)

def Market.CanStrictlyImprove {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    KelsoCrawford.OneSided.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.OneSided.profit (M.y j) C r

def Market.IsStrictCore {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanImprove R A

def Market.IsCore {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanStrictlyImprove R A

def Market.NTW {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (δ : ℝ) : Prop :=
  ∀ A, M.IsCore (M.grid δ) A → ∀ i (k : F), k ≠ A.assign i →
    ∀ r ∈ M.grid δ i k,
      M.u i (A.assign i) (A.sal i) ≠ M.u i k r

def Market.NTF {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (δ : ℝ) : Prop :=
  ∀ A, M.IsCore (M.grid δ) A → ∀ (j : F) (C : Finset W),
    C.Nonempty → C ≠ A.hired j → ∀ r ∈ M.gridVectors δ j,
      KelsoCrawford.OneSided.profit (M.y j) (A.hired j) A.sal ≠ KelsoCrawford.OneSided.profit (M.y j) C r

def Market.Theorem4Conditions {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (δ : ℝ) : Prop :=
  M.UtilityRegular ∧ M.MP ∧ M.NFL ∧
    (∀ j, KelsoCrawford.OneSided.GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) ∧
    M.NTW δ ∧ M.NTF δ

def IsFirmAugmentation {W F : Type} (M : Market W F)
    (Mplus : Market W (Option F)) : Prop :=
  (∀ i j s, Mplus.u i (some j) s = M.u i j s) ∧
    (∀ j, Mplus.y (some j) = M.y j) ∧
    ∀ i j, Mplus.σ i (some j) = M.σ i j

def Market.withoutWorker {W F : Type} [DecidableEq W]
    (M : Market W F) (w₀ : W) : Market {i : W // i ≠ w₀} F :=
  ⟨fun i j s => M.u i j s,
   fun j C => M.y j (C.map (Function.Embedding.subtype _)),
   fun i j => M.σ i j⟩

end KelsoCrawford.CompStatics


