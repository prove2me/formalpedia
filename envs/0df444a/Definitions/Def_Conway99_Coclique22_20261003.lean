-- Prove2me | Definitions.Def_Conway99_Coclique22_20261003
-- name    : Conway99_Coclique22_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T01:03:44.621371+00:00
-- url     : https://prove2.me/theorems/08f385ea-def1-43ce-b12b-f0b878287303
-- title:
--   Graph-owned coclique blocks and exact simultaneous completion data
-- statement:
--   For a finite simple graph G and a specified independent set C of 22 vertices, P and D are literal adjacency blocks of G on C and its complement. For G on 99 vertices, H is the literal incidence matrix of its actual outside triangles, while E and R partition outside edges by whether their unique triangle meets C. BlockCompletion and SimultaneousCompletion are finite binary matrix data on fixed 22 and 77 point sets; their equations are requirements, not existence claims. HasCoclique99 expresses existence of a 99-vertex strongly regular graph together with a specified independent 22-set.
-- source:
--   archive/clean-start/proof-library.zip!proofs/COCLIQUE22.md SHA-256 ecdefe7569c56cff259816da8660e5375bdd64bfaeea3771b3b2f4c0712292d3; archive/clean-start/proof-library.zip!proofs/COCLIQUE22_REVIEW.md SHA-256 d51c8b3e09cbd22f63bb29a779b9ac874ebd72725cbccf34630bfdfc1d0eddbf. Formal source: formalization/2026-10-03/coclique22-completion at commit 9f00682e6161089cdce7b915368ea7cbb01a3194. This is a private intermediate packet, not a proof of the public Conway 99 target.

/- Pure definitions for the private coclique completion statements; pinned Mathlib 0df444a, Lean 4.33.1. -/
import Mathlib

set_option autoImplicit false

/-! Pure definitions for the private 22-coclique completion statements. -/

namespace Conway99Formal.Coclique22

open Matrix SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Coclique (G : SimpleGraph V) where
  carrier : Finset V
  card_eq : carrier.card = 22
  independent : ∀ ⦃x⦄, x ∈ carrier → ∀ ⦃y⦄, y ∈ carrier → ¬ G.Adj x y

abbrev Inside {G : SimpleGraph V} (C : Coclique G) := {v : V // v ∈ C.carrier}
abbrev Outside {G : SimpleGraph V} (C : Coclique G) :=
  {v : V // v ∈ C.carrierᶜ}

def J (I K : Type*) : Matrix I K ℤ := Matrix.of fun _ _ => 1

def P (G : SimpleGraph V) [DecidableRel G.Adj] (C : Coclique G) :
    Matrix (Inside C) (Outside C) ℤ :=
  (G.adjMatrix ℤ).submatrix Subtype.val Subtype.val

def D (G : SimpleGraph V) [DecidableRel G.Adj] (C : Coclique G) :
    Matrix (Outside C) (Outside C) ℤ :=
  (G.adjMatrix ℤ).submatrix Subtype.val Subtype.val

/-- Conditions on arbitrary 22-by-77 and 77-by-77 binary blocks. -/
structure BlockCompletion where
  P : Matrix (Fin 22) (Fin 77) ℤ
  D : Matrix (Fin 77) (Fin 77) ℤ
  P_binary : ∀ c u, P c u = 0 ∨ P c u = 1
  D_adjacency : D.IsAdjMatrix
  P_row_sum : ∀ c, (∑ u, P c u) = 14
  P_column_sum : ∀ u, (∑ c, P c u) = 4
  D_row_sum : ∀ u, (∑ v, D u v) = 10
  P_design : P * Pᵀ =
    12 • (1 : Matrix (Fin 22) (Fin 22) ℤ) + 2 • J (Fin 22) (Fin 22)
  mixed : P * D + P = 2 • J (Fin 22) (Fin 77)
  quadratic : D * D + D + Pᵀ * P =
    12 • (1 : Matrix (Fin 77) (Fin 77) ℤ) + 2 • J (Fin 77) (Fin 77)

def blockMatrix (Q : BlockCompletion) :
    Matrix (Fin 22 ⊕ Fin 77) (Fin 22 ⊕ Fin 77) ℤ :=
  Matrix.fromBlocks 0 Q.P Q.Pᵀ Q.D

def blockCocliqueCarrier : Finset (Fin 22 ⊕ Fin 77) :=
  Finset.univ.image (Sum.inl : Fin 22 → Fin 22 ⊕ Fin 77)

/-- The simultaneous P,H,E problem; R and D are derived from one packet. -/
def outsideR (H : Matrix (Fin 77) (Fin 77) ℤ) :
    Matrix (Fin 77) (Fin 77) ℤ :=
  H * Hᵀ - 3 • (1 : Matrix (Fin 77) (Fin 77) ℤ)

structure SimultaneousCompletion where
  P : Matrix (Fin 22) (Fin 77) ℤ
  H : Matrix (Fin 77) (Fin 77) ℤ
  E : Matrix (Fin 77) (Fin 77) ℤ
  P_binary : ∀ c u, P c u = 0 ∨ P c u = 1
  P_row_sum : ∀ c, (∑ u, P c u) = 14
  P_column_sum : ∀ u, (∑ c, P c u) = 4
  P_design : P * Pᵀ =
    12 • (1 : Matrix (Fin 22) (Fin 22) ℤ) + 2 • J (Fin 22) (Fin 22)
  H_binary : ∀ u t, H u t = 0 ∨ H u t = 1
  H_row_sum : ∀ u, (∑ t, H u t) = 3
  H_column_sum : ∀ t, (∑ u, H u t) = 3
  R_binary_offdiag : ∀ u v, u ≠ v →
    outsideR H u v = 0 ∨ outsideR H u v = 1
  R_diag : ∀ u, outsideR H u u = 0
  R_edge_disjoint : ∀ u v,
    outsideR H u v = 1 →
      (Pᵀ * P) u v = 0
  E_adjacency : E.IsAdjMatrix
  E_row_sum : ∀ u, (∑ v, E u v) = 4
  E_edge_meets : ∀ u v, E u v = 1 → (Pᵀ * P) u v = 1
  mixed : P * (outsideR H + E) + P =
    2 • J (Fin 22) (Fin 77)
  quadratic :
    (outsideR H + E) * (outsideR H + E) +
      (outsideR H + E) + Pᵀ * P =
        12 • (1 : Matrix (Fin 77) (Fin 77) ℤ) + 2 • J (Fin 77) (Fin 77)

def simultaneousD (Q : SimultaneousCompletion) :
    Matrix (Fin 77) (Fin 77) ℤ :=
  outsideR Q.H + Q.E

/-- Actual-graph side of the exact completion equivalence; the graph and coclique are both quantified. -/
def HasCoclique99 : Prop := by
  classical
  exact ∃ G : SimpleGraph (Fin 99),
    G.IsSRGWith 99 14 1 2 ∧ Nonempty (Coclique G)

end Conway99Formal.Coclique22

namespace Conway99Formal.TriangleIncidence

abbrev Triangle (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj] :=
  {T : Finset (Fin 99) // T ∈ G.cliqueFinset 3}

end Conway99Formal.TriangleIncidence

namespace Conway99Formal.Coclique22Triangle

open Conway99Formal.Coclique22 Conway99Formal.TriangleIncidence

abbrev OutsideTriangle (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (C : Coclique G) :=
  {T : Triangle G // Disjoint T.1 C.carrier}

def H (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj] (C : Coclique G) :
    Matrix (Outside C) (OutsideTriangle G C) ℤ :=
  fun u T => if u.1 ∈ T.1.1 then 1 else 0

def E (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj] (C : Coclique G) :
    Matrix (Outside C) (Outside C) ℤ :=
  fun u v => if G.Adj u.1 v.1 ∧
      ∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1 then 1 else 0

def R (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj] (C : Coclique G) :
    Matrix (Outside C) (Outside C) ℤ :=
  fun u v => if G.Adj u.1 v.1 ∧
      ¬ ∃ c : Inside C, G.Adj c.1 u.1 ∧ G.Adj c.1 v.1 then 1 else 0

end Conway99Formal.Coclique22Triangle


