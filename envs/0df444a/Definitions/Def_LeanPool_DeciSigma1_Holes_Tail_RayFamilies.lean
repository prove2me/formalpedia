-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
-- name    : LeanPool_DeciSigma1_Holes_Tail_RayFamilies
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:55:19.136354+00:00
-- url     : https://prove2.me/theorems/b636a64e-3ee6-4675-bd09-d794154e6caf
-- title:
--   Ray Families
-- statement:
--   Definitions and structural lemmas for Ray Families, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayFamilies.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
structure RayFamily [DecidableEq α] [Fintype S] {σ : ℕ}
    (C : LevelBounds σ k (Fintype.card S)) (M : StructuralReader α S k) (W : Fin k → List α) where
  /-- Common hierarchy level of the family. -/
  level : ℕ
  le_top : level ≤ levelCount k
  /-- Coordinates represented by infinite rays. -/
  rays : Finset (Fin k)
  /-- Suffix-window length for each ray coordinate. -/
  windowLength : Fin k → ℕ
  /-- Initial ray cut for each coordinate. -/
  startCut : Fin k → ℕ
  /-- Final ray cut for each coordinate. -/
  endCut : Fin k → ℕ
  /-- Infinite periodic continuation assigned to each ray coordinate. -/
  ray : {i // i ∈ rays} → Ray α
  /-- Finite target words used in the suffix dictionary. -/
  targets : List (List α)
  fixed : ∀ j, j ∉ rays → ¬ M.Immortal (M.endState W j) ∨ LevelCoverProperty C (level - 2) M W j
  mem_targets : ∀ j, j ∉ rays → W j ∈ targets
  closed : ∀ i ∈ rays, NodeClosedAt M.toTable (M.start i)
    (suffixDictionary targets (windowLength i)) (W i) (startCut i) (endCut i)
  ray_eq : ∀ i (hi : i ∈ rays),
    ray ⟨i, hi⟩ = repeatFactorRay (W i) (startCut i) (endCut i) (closed i hi).1 (closed i hi).2.1
  firstRejection_le_startCut : ∀ i ∈ rays, M.firstRejection W i ≤ startCut i
  free : ∀ i ∈ rays, ∀ j, j ∉ rays →
      NoSuffixOccurrenceEndsBetween (W i) (W j) (windowLength i) (startCut i) (endCut i)
  period_le_bound : ∀ i (hi : i ∈ rays), (ray ⟨i, hi⟩).period ≤ C.periodBound level
  cover : ∀ i ∈ rays, (endCut i = (W i).length ∧ CoordinateCover C (level - 1) M W i) ∨
    PeriodicCover ((W i).take (startCut i)) (M.firstRejection W i) (C.pieceCountBase + 2)
        (C.periodBound level) ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound level + 3))
  no_self_admission : ∀ i (hi : i ∈ rays), ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
    M.admitted (rayState M (M.start i) (ray ⟨i, hi⟩) a) (rayState M (M.start i) (ray ⟨i, hi⟩) b) =
        true →
    ¬ ∀ t, (ray ⟨i, hi⟩).stream (a + t) = (ray ⟨i, hi⟩).stream (b + t)
  no_positive_cycle : ¬ (raySystem M (fun i : {i // i ∈ rays} => M.start i.1) ray
    (fun i => M.firstRejection W i.1)).HasPositiveCycle
structure FactorCuts where
  /-- Suffix-window length used by the periodic factor. -/
  windowLength : ℕ
  /-- Cut immediately before the factor. -/
  startCut : ℕ
  /-- Cut immediately after the factor. -/
  endCut : ℕ
def mkRay (dflt : Ray α) (x : List α) (c c' : ℕ) : Ray α :=
  if h : c < c' ∧ c' ≤ x.length then repeatFactorRay x c c' h.1 h.2 else dflt
section Family
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]
end Family
end DeciSigma1.Holes.Tail


