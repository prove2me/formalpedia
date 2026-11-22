-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
-- name    : LeanPool_DeciSigma1_Holes_Periodic_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:43:39.309178+00:00
-- url     : https://prove2.me/theorems/b46c0329-5e02-4c27-a4f6-45d8b94a7a6c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
structure Piece (W : Fin k → List α) (d : ℕ) where
  /-- Coordinate whose word contains the periodic interval. -/
  coordinate : Fin k
  /-- First position of the periodic interval. -/
  start : ℕ
  /-- Position immediately after the periodic interval. -/
  stop : ℕ
  long : start + 2 * d ≤ stop
  stop_le_length : stop ≤ (W coordinate).length
  periodic : ∀ p, start ≤ p → p + d < stop → (W coordinate)[p]? = (W coordinate)[p + d]?
  primitive : IsPrimitive (((W coordinate).drop start).take d)
  left_maximal : start = 0 ∨ (W coordinate)[start - 1]? ≠ (W coordinate)[start - 1 + d]?
  right_maximal : stop = (W coordinate).length ∨ (W coordinate)[stop]? ≠ (W coordinate)[stop - d]?
namespace Piece
variable {W : Fin k → List α} {d : ℕ}
theorem ext_coordinates {P Q : Piece W d} (hl : P.coordinate = Q.coordinate)
    (hs : P.start = Q.start) (he : P.stop = Q.stop) : P = Q := by
  cases P; cases Q; simp only at hl hs he; subst hl hs he; rfl
theorem ext_iff_coordinates {P Q : Piece W d} :
    P = Q ↔ P.coordinate = Q.coordinate ∧ P.start = Q.start ∧ P.stop = Q.stop :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl⟩, fun ⟨a, b, c⟩ => ext_coordinates a b c⟩
instance : DecidableEq (Piece W d) := fun _ _ => decidable_of_iff _ ext_iff_coordinates.symm
def len (P : Piece W d) : ℕ := P.stop - P.start
def root (P : Piece W d) : List α := ((W P.coordinate).drop P.start).take d
def follower (P : Piece W d) : List α := (W P.coordinate).drop P.stop
end Piece
section Fin
variable [DecidableEq α] (W : Fin k → List α) (d : ℕ)
def IsPeriodicPiece (l : Fin k) (s e : ℕ) : Prop :=
  s + 2 * d ≤ e ∧ e ≤ (W l).length ∧ (∀ p < e, s ≤ p → p + d < e → (W l)[p]? = (W l)[p + d]?) ∧
    IsPrimitive (((W l).drop s).take d) ∧ (s = 0 ∨ (W l)[s - 1]? ≠ (W l)[s - 1 + d]?) ∧
    (e = (W l).length ∨ (W l)[e]? ≠ (W l)[e - d]?)
instance (l : Fin k) (s e : ℕ) : Decidable (IsPeriodicPiece W d l s e) := by
  unfold IsPeriodicPiece; infer_instance
def Piece.ofIsPeriodicPiece {U : Fin k → List α} {d : ℕ}
    {l : Fin k} {s e : ℕ}
    (h : IsPeriodicPiece U d l s e) : Piece U d :=
  ⟨l, s, e, h.1, h.2.1, fun p hp hpe => h.2.2.1 p (by omega) hp hpe, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2⟩
omit [DecidableEq α] in
/-- A piece satisfies the piece conditions. -/
theorem Piece.isPeriodicPiece {U : Fin k → List α} {d : ℕ}
    (P : Piece U d) :
    IsPeriodicPiece U d P.coordinate P.start P.stop :=
  ⟨P.long, P.stop_le_length, fun p _ hp hpe => P.periodic p hp hpe, P.primitive, P.left_maximal,
      P.right_maximal⟩
def mkPiece? (t : Fin k × ℕ × ℕ) : Option (Piece W d) :=
  if h : IsPeriodicPiece W d t.1 t.2.1 t.2.2 then some (Piece.ofIsPeriodicPiece h) else none
theorem mkPiece?_spec {t : Fin k × ℕ × ℕ} {P : Piece W d} (h : P ∈ mkPiece? W d t) :
    t = (P.coordinate, P.start, P.stop) := by
  unfold mkPiece? at h
  split_ifs at h with h1
  · simp only [Option.mem_def, Option.some.injEq] at h; subst h; rfl
  · simp at h
theorem mkPiece?_inj (t t' : Fin k × ℕ × ℕ) (P : Piece W d) (h : P ∈ mkPiece? W d t)
    (h' : P ∈ mkPiece? W d t') : t = t' :=
  (mkPiece?_spec W d h).trans (mkPiece?_spec W d h').symm
def allPieces : Finset (Piece W d) :=
  (Finset.univ ×ˢ (Finset.range (totalLength W + 1) ×ˢ Finset.range (totalLength W + 1))).filterMap
    (mkPiece? W d) (mkPiece?_inj W d)
theorem mem_allPieces (P : Piece W d) : P ∈ allPieces W d := by
  unfold allPieces
  rw [Finset.mem_filterMap]
  have hle := (P.stop_le_length).trans (length_le_totalLength W P.coordinate)
  refine ⟨(P.coordinate, P.start, P.stop), by simp; have := P.long; omega, ?_⟩
  unfold mkPiece?
  rw [dif_pos P.isPeriodicPiece]
  rfl
instance : Fintype (Piece W d) := ⟨allPieces W d, mem_allPieces W d⟩
def piecesOf (ρ : List α) : Finset (Piece W ρ.length) :=
  Finset.univ.filter (fun P => IsConjugate P.root ρ)
end Fin
def FollowerEdge {W : Fin k → List α} {d : ℕ} (P Q : Piece W d) : Prop :=
  P.follower <+: Q.follower ∨ Q.follower <+: P.follower
instance [DecidableEq α] {W : Fin k → List α} {d : ℕ} (P Q : Piece W d) :
    Decidable (FollowerEdge P Q) := by
  unfold FollowerEdge; infer_instance
section Overlap
variable {W : Fin k → List α} {d : ℕ}
end Overlap
end DeciSigma1.Holes.Periodic


