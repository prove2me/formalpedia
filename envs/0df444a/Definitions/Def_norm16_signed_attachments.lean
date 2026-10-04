-- Prove2me | Definitions.Def_norm16_signed_attachments
-- name    : norm16_signed_attachments
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T02:28:18.930433+00:00
-- url     : https://prove2.me/theorems/815672be-f4f0-4511-aab8-e490f626e645
-- title:
--   Signed graph attachment data
-- statement:
--   Defines the five signed vertex cells, their explicit edge-exclusion hypotheses, selected signed neighbors with indicator laws, and the exact integer and rational demand and contribution coordinates used by the attachment equations.
-- source:
--   Conway99 signed-attachment family, formalization/2026-10-03/norm16-attachments/BlockEquations.lean, five graph demand equations and graph_weighted_capacity_cut; source pinned at a45708acebe3f397faccb1b646be906f24f23ee5 (BlockEquations blob 2243b9ff3e16838727e0d4e03da4a5d06336d920); originating source family commit f51996b. See ATTACHMENT_AND_FORCING_BOUNDARY.md, Eq. (1), and finite weighted capacity cut Eq. (2).

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.Norm16Attachments

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A five-cell labeling P=0, M=1, Z=2, R=3, T=4 with the exact exclusions used by the signed attachment equations. -/
structure SignedCells (G : SimpleGraph V) [DecidableRel G.Adj] where
  color : V → Fin 5
  positive_independent : ∀ x y, color x = 0 → color y = 0 → ¬ G.Adj x y
  negative_independent : ∀ x y, color x = 1 → color y = 1 → ¬ G.Adj x y
  zero_anticomplete_positive : ∀ x y, color x = 0 → color y = 2 → ¬ G.Adj x y
  zero_anticomplete_negative : ∀ x y, color x = 1 → color y = 2 → ¬ G.Adj x y

namespace SignedCells

variable (G : SimpleGraph V) [DecidableRel G.Adj] (s : SignedCells G)

abbrev Cell (i : Fin 5) := {v : V // s.color v = i}
abbrev P := Cell G s 0
abbrev M := Cell G s 1
abbrev Z := Cell G s 2
abbrev R := Cell G s 3
abbrev T := Cell G s 4

/-- A block is a restriction of the same graph's integer adjacency matrix. -/
def block (i j : Fin 5) : Matrix (Cell G s i) (Cell G s j) ℤ :=
  (G.adjMatrix ℤ).submatrix (fun x => x.1) (fun y => y.1)

abbrev K := block G s 0 1
abbrev X := block G s 0 4
abbrev Y := block G s 1 4
abbrev U := block G s 4 2
abbrev E := block G s 4 4
abbrev D := block G s 4 3
abbrev B := block G s 2 3
abbrev HP := block G s 0 3
abbrev HM := block G s 1 3

/-- Each R vertex has one selected positive and one selected negative neighbor, with exact indicator laws. -/
structure SignedNeighbors where
  pos : R G s → P G s
  neg : R G s → M G s
  pos_indicator : ∀ r : R G s, ∀ p : P G s,
    G.adjMatrix ℤ p.1 r.1 = if p = pos r then 1 else 0
  neg_indicator : ∀ r : R G s, ∀ m : M G s,
    G.adjMatrix ℤ m.1 r.1 = if m = neg r then 1 else 0

/-- Indices for the five signed demand families P–M, P–Z, M–Z, P–T, and M–T. -/
abbrev DemandIndex :=
  (P G s × M G s) ⊕ (P G s × Z G s) ⊕ (M G s × Z G s) ⊕
    (P G s × T G s) ⊕ (M G s × T G s)

/-- Exact graph demand in each of the five signed block equations. -/
def graphDemand : DemandIndex G s → ℤ
  | .inl (p, m) =>
      2 - G.adjMatrix ℤ p.1 m.1 -
        ∑ t : T G s, G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 m.1
  | .inr (.inl (p, z)) =>
      2 - ∑ t : T G s, G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 z.1
  | .inr (.inr (.inl (m, z))) =>
      2 - ∑ t : T G s, G.adjMatrix ℤ m.1 t.1 * G.adjMatrix ℤ t.1 z.1
  | .inr (.inr (.inr (.inl (p, t)))) =>
      2 - G.adjMatrix ℤ p.1 t.1 -
        (∑ m : M G s, G.adjMatrix ℤ p.1 m.1 * G.adjMatrix ℤ m.1 t.1) -
        (∑ u : T G s, G.adjMatrix ℤ p.1 u.1 * G.adjMatrix ℤ u.1 t.1)
  | .inr (.inr (.inr (.inr (m, t)))) =>
      2 - G.adjMatrix ℤ m.1 t.1 -
        (∑ p : P G s, G.adjMatrix ℤ m.1 p.1 * G.adjMatrix ℤ p.1 t.1) -
        (∑ u : T G s, G.adjMatrix ℤ m.1 u.1 * G.adjMatrix ℤ u.1 t.1)

/-- The contribution at one R vertex from one proposed signed-neighbor pair. -/
def graphContribution (r : R G s) (pair : P G s × M G s) :
    DemandIndex G s → ℤ
  | .inl (p, m) =>
      (if p = pair.1 then 1 else 0) * (if m = pair.2 then 1 else 0)
  | .inr (.inl (p, z)) =>
      (if p = pair.1 then 1 else 0) * G.adjMatrix ℤ r.1 z.1
  | .inr (.inr (.inl (m, z))) =>
      (if m = pair.2 then 1 else 0) * G.adjMatrix ℤ r.1 z.1
  | .inr (.inr (.inr (.inl (p, t)))) =>
      (if p = pair.1 then 1 else 0) * G.adjMatrix ℤ r.1 t.1
  | .inr (.inr (.inr (.inr (m, t)))) =>
      (if m = pair.2 then 1 else 0) * G.adjMatrix ℤ r.1 t.1

/-- Rational form of an integer graph demand. -/
def graphDemandQ (i : DemandIndex G s) : ℚ := graphDemand G s i

/-- Rational form of one R-vertex contribution. -/
def graphContributionQ (r : R G s) (pair : P G s × M G s)
    (i : DemandIndex G s) : ℚ := graphContribution G s r pair i

end SignedCells
end Conway99Formal.Norm16Attachments


