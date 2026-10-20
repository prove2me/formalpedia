-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19
-- name    : QAlgorithms_Papers_Independent_Frontier30_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:11:59.551161+00:00
-- url     : https://prove2.me/theorems/8d7b92e9-3a4e-4abb-9a53-aa337020fdba
-- title:
--   Definitions for A memory and gate efficient algorithm for unitary mixed Schur sampling
-- statement:
--   The objects the formalized statements of *A memory and gate efficient algorithm for unitary mixed Schur sampling* (arXiv:2410.15793) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `skewCells`: Skew diagram cells, with zero-based row and column coordinates. Source: arXiv:2410.15793v2, PDF p.32, proof of Lemma 11.
--   - `lrPrefixCount`: Number of occurrences of a letter through a given cell in the reading order: rows from top to bottom, and each row from right to left, including the endpoint. Source: arXiv:2410.15793v2, PDF p.32, the Littlewood--Richardson rule invoked there.
--   - `IsLRFilling`: The standard LR tableau predicate: semistandard rows and columns, prescribed content, and a lattice reading word. These are tableau conditions, not assumed properties of the coefficient support. Source: arXiv:2410.15793v2, PDF p.32, Definition 3 and the LR rule used in the proof of Lemma 11.
--   - `lrCoefficient`: Canonical homogeneous Littlewood--Richardson coefficient, counted by the LR rule, and zero when the inner diagram is not contained in the outer diagram. Source: arXiv:2410.15793v2, PDF p.32, Definition 3 interpreted by its own proof. This is the polynomial/U(d) lift of the printed SU(d) notation; unrestricted SU(d) determinant-shift multiplicities would not satisfy Lemma 11(2).
--   - `pureTensor`: Computational coordinates of a pure tensor of m vectors of C^d. Source: arXiv:2410.15793v2, PDF p.34, Eq.(C13).
--   - `tensorPowerSubspace`: The tensor power of S, formed by iterating the accepted physical binary `Dependency50.P31.tensorSubspace` at the last-particle cut. The last one-qudit subspace is spanned by coordinate copies of S. The zeroth power is C. Source: arXiv:2410.15793v2, PDF p.34, Eq.(C13).
-- source:
--   A memory and gate efficient algorithm for unitary mixed Schur sampling, arXiv:2410.15793v2, https://arxiv.org/abs/2410.15793v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Skew diagram cells, with zero-based row and column coordinates.
Source: arXiv:2410.15793v2, PDF p.32, proof of Lemma 11. -/
def skewCells (lambda nu : YoungDiagram) : Finset (ℕ × ℕ) :=
  nu.cells \ lambda.cells

/-- Number of occurrences of a letter through a given cell in the reading order:
rows from top to bottom, and each row from right to left, including the endpoint.
Source: arXiv:2410.15793v2, PDF p.32, the Littlewood--Richardson rule invoked there. -/
def lrPrefixCount {d : ℕ} {lambda nu : YoungDiagram}
    (T : (skewCells lambda nu) → Fin d) (a : skewCells lambda nu) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun b : skewCells lambda nu =>
    (b.val.1 < a.val.1 ∨ (b.val.1 = a.val.1 ∧ a.val.2 ≤ b.val.2)) ∧ T b = i).card

/-- The standard LR tableau predicate: semistandard rows and columns, prescribed
content, and a lattice reading word. These are tableau conditions, not assumed
properties of the coefficient support. Source: arXiv:2410.15793v2, PDF p.32,
Definition 3 and the LR rule used in the proof of Lemma 11. -/
def IsLRFilling {d : ℕ} (lambda mu nu : YoungDiagram)
    (T : (skewCells lambda nu) → Fin d) : Prop :=
  (∀ a b : skewCells lambda nu,
    (a.val.1 = b.val.1 → a.val.2 < b.val.2 → T a ≤ T b) ∧
    (a.val.2 = b.val.2 → a.val.1 < b.val.1 → T a < T b)) ∧
  (∀ i : ℕ,
    (Finset.univ.filter fun a : skewCells lambda nu => (T a).val = i).card = mu.rowLen i) ∧
  (∀ a : skewCells lambda nu, ∀ i j : Fin d,
    j.val = i.val + 1 → lrPrefixCount T a j ≤ lrPrefixCount T a i)

/-- Canonical homogeneous Littlewood--Richardson coefficient, counted by the
LR rule, and zero when the inner diagram is not contained in the outer diagram.
Source: arXiv:2410.15793v2, PDF p.32, Definition 3 interpreted by its own proof.
This is the polynomial/U(d) lift of the printed SU(d) notation; unrestricted
SU(d) determinant-shift multiplicities would not satisfy Lemma 11(2). -/
def lrCoefficient (d : ℕ) (lambda mu nu : YoungDiagram) : ℕ :=
  if lambda.cells ⊆ nu.cells then
    (Finset.univ.filter (IsLRFilling (d := d) lambda mu nu)).card
  else 0

example : skewCells ⊥ ⊥ = ∅ := by
  simp [skewCells]

example (d : ℕ) : lrCoefficient d ⊥ ⊥ ⊥ = 1 := by
  letI : IsEmpty (skewCells ⊥ ⊥) := ⟨fun a => by
    simpa [skewCells] using a.property⟩
  have hvalid : ∀ T : (skewCells ⊥ ⊥) → Fin d,
      IsLRFilling ⊥ ⊥ ⊥ T := by
    intro T
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact isEmptyElim a
    · intro i
      simp [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
    · intro a
      exact isEmptyElim a
  simp only [lrCoefficient, if_pos (Finset.Subset.refl _)]
  rw [Finset.filter_true_of_mem (fun T _ => hvalid T)]
  simp

example (d : ℕ) (lambda mu nu : YoungDiagram)
    (h : ¬ lambda.cells ⊆ nu.cells) : lrCoefficient d lambda mu nu = 0 := by
  simp [lrCoefficient, h]

/-- Computational coordinates of a pure tensor of m vectors of C^d.
Source: arXiv:2410.15793v2, PDF p.34, Eq.(C13). -/
def pureTensor {d m : ℕ} (v : Fin m → EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (Fin m → Fin d) :=
  WithLp.toLp 2 (fun x => ∏ i : Fin m, v i (x i))

/-- The tensor power of S, formed by iterating the accepted physical binary
`Dependency50.P31.tensorSubspace` at the last-particle cut. The last one-qudit
subspace is spanned by coordinate copies of S. The zeroth power is C.
Source: arXiv:2410.15793v2, PDF p.34, Eq.(C13). -/
def tensorPowerSubspace {d : ℕ} : (m : ℕ) →
    Submodule ℂ (EuclideanSpace ℂ (Fin d)) →
    Submodule ℂ (EuclideanSpace ℂ (Fin m → Fin d))
  | 0, _ => ⊤
  | m + 1, S =>
    QAlgorithms.Papers.Independent.Dependency50.P31.tensorSubspace
      (n := m + 1) m (Nat.le_succ m) (tensorPowerSubspace m S)
      (Submodule.span ℂ {w | ∃ v ∈ S,
        w = pureTensor (fun _ : Fin (m + 1 - m) => v)})

example {d : ℕ} (v : Fin 1 → EuclideanSpace ℂ (Fin d))
    (x : Fin 1 → Fin d) : pureTensor v x = v 0 (x 0) := by
  simp [pureTensor]

example {d : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    tensorPowerSubspace 0 S = ⊤ := by
  rfl

example {d k : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (v : EuclideanSpace ℂ (Fin d)) (hv : v ∈ S) :
    pureTensor (fun _ : Fin k => v) ∈
      Submodule.span ℂ {w | ∃ u ∈ S, w = pureTensor (fun _ : Fin k => u)} := by
  exact Submodule.subset_span ⟨v, hv, rfl⟩

end QAlgorithms.Papers.Independent.Frontier30.P19


