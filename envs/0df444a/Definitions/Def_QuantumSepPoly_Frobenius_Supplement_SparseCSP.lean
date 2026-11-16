-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_SparseCSP
-- name    : QuantumSepPoly_Frobenius_Supplement_SparseCSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:46:33.727318+00:00
-- url     : https://prove2.me/theorems/63dc572a-a3a2-454e-975e-c2fff8bd16b7
-- title:
--   Sparse Boolean two-variable constraints
-- statement:
--   A sparse instance specializes the published MaxCSP to arity two and alphabet $\operatorname{Fin}(A)$. Every edge has distinct endpoints and is stored once with its lesser endpoint first. Its predicate takes values zero or one, and each vertex has degree between one and $\delta$. These are separate properties of an instance, not fields asserting construction correctness.
--
--   The endpoint lookup reverses the two labels when reading an edge backwards and returns the neutral factor one when no edge exists. This represents precisely one predicate for each constrained unordered pair.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 25, 28, 32–35 (PDF p. 25, 28, 32–35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_DenseCSP

noncomputable section

namespace QuantumSepPoly.Frobenius.Supplement
/-- Sparse Boolean two-CSPs use the published MaxCSP without assuming correctness.
An unordered edge is stored once, with its lesser endpoint first. -/
def Sparse {N A : ℕ} (I : MaxCSP N 2 (Fin A)) (δ : ℕ) : Prop :=
  (∀ t ∈ I.constraints, t 0 < t 1) ∧
  (∀ t ∈ I.constraints, ∀ a, I.predicate t a = 0 ∨ I.predicate t a = 1) ∧
  ∀ i : Fin N,
    1 ≤ (I.constraints.filter (fun t => t 0 = i ∨ t 1 = i)).card ∧
    (I.constraints.filter (fun t => t 0 = i ∨ t 1 = i)).card ≤ δ

/-- Endpoint-to-constraint lookup, including the reverse orientation. -/
def edgePredicate {N A : ℕ} (I : MaxCSP N 2 (Fin A))
    (i j : Fin N) (a b : Fin A) : ℝ :=
  if h : ∃ t ∈ I.constraints, t 0 = i ∧ t 1 = j then
    I.predicate (Classical.choose h) ![a,b]
  else if h : ∃ t ∈ I.constraints, t 0 = j ∧ t 1 = i then
    I.predicate (Classical.choose h) ![b,a]
  else 1
end QuantumSepPoly.Frobenius.Supplement


