-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P26
-- name    : QAlgorithms_Papers_Independent_Bridge50_P26
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:14:26.141835+00:00
-- url     : https://prove2.me/theorems/2d4892ae-19ba-47ee-9345-6ef636ae12d7
-- title:
--   Definitions for Fundamental limitation on quantum broadcast networks
-- statement:
--   The objects the formalized statements of *Fundamental limitation on quantum broadcast networks* (arXiv:1609.03994) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PhysicalBasis`: PDF p.12: coordinates of all physical registers, before any partial trace.
--   - `GroupedBasis`: PDF pp.7,12, (13)-(14),(A1): each honest party holds the product of its listed physical registers. An empty register list has its unit empty factor.
--   - `groupedDensity`: PDF pp.7,12: partial trace onto the union of the disjoint honest groups, followed by their tensor-coordinate grouping. Discarded coordinates are equal between row and column; retained coordinates may be off-diagonal. The physical interpretation requires disjoint groups, as in each of the three groupings below.
--   - `groupedSquashed`: PDF pp.4-5,7, (6)-(7),(14), footnote 1: squashed entanglement of the computed honest marginal. The accepted infimum ranges over every positive finite extension dimension and every normalized quantum extension. The zero or one party value is explicitly zero. On the disjoint groupings below a unit input gives a density marginal, so the real infimum is nonempty and bounded below.
--   - `lemma5LeftGroups`: PDF p.12, (A1), left side. Physical positions are S=0, P_i=i for 1<=i<=m, Q_i=m+i for 1<=i<=n, E1=m+n+1, E2=m+n+2. Parties are S, P1 Q1, ..., Pn Qn, P(n+1), ..., Pm; both environments are discarded.
--   - `lemma5FirstGroups`: PDF p.12, (A1), first right term: parties SQ1...QnE2, P1, ..., Pm. Only E1 is discarded. The environment E2 is retained in the first honest party.
--   - `lemma5SecondGroups`: PDF p.12, (A1), second right term: parties SP1...PmE1, Q1, ..., Qn. Only E2 is discarded. The environment E1 is retained in the first honest party.
-- source:
--   Fundamental limitation on quantum broadcast networks, arXiv:1609.03994v3, https://arxiv.org/abs/1609.03994v3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

/-!
Bauml and Azuma, arXiv:1609.03994v3, finite-dimensional source-proof scope.
Entropies are in bits; squashed entanglement is the quantum conditional TOTAL
correlation infimum, with no factor 1/2. Lemma 3 is recorded as exact reuse.
The operational network results and the ambiguous Steiner-hypertree claim are
deferred in this unit's HARD.md and GAPS.json. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P26

open QAlgorithms.Papers.Independent.Claimed50.P33 (multipartiteSquashed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.12: coordinates of all physical registers, before any partial trace. -/
abbrev PhysicalBasis {r : ℕ} (D : Fin r → Type) := (i : Fin r) → D i

/-- PDF pp.7,12, (13)-(14),(A1): each honest party holds the product of its
listed physical registers. An empty register list has its unit empty factor. -/
abbrev GroupedBasis {r k : ℕ} (D : Fin r → Type)
    (groups : Fin k → Finset (Fin r)) :=
  (j : Fin k) → (i : {i : Fin r // i ∈ groups j}) → D i.val

/-- PDF pp.7,12: partial trace onto the union of the disjoint honest groups,
followed by their tensor-coordinate grouping. Discarded coordinates are equal
between row and column; retained coordinates may be off-diagonal. The physical
interpretation requires disjoint groups, as in each of the three groupings below. -/
def groupedDensity {r k : ℕ} {D : Fin r → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (PhysicalBasis D) (PhysicalBasis D) ℂ)
    (groups : Fin k → Finset (Fin r)) :
    Matrix (GroupedBasis D groups) (GroupedBasis D groups) ℂ :=
  fun a b => ∑ x : PhysicalBasis D, ∑ y : PhysicalBasis D,
    if (∀ j i (hi : i ∈ groups j),
        x i = a j ⟨i, hi⟩ ∧ y i = b j ⟨i, hi⟩) ∧
        (∀ i, (∀ j, i ∉ groups j) → x i = y i)
    then rho x y else 0

/-- PDF pp.4-5,7, (6)-(7),(14), footnote 1: squashed entanglement of the
computed honest marginal. The accepted infimum ranges over every positive
finite extension dimension and every normalized quantum extension. The zero
or one party value is explicitly zero. On the disjoint groupings below a unit
input gives a density marginal, so the real infimum is nonempty and bounded below. -/
def groupedSquashed {r k : ℕ} {D : Fin r → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (PhysicalBasis D) (PhysicalBasis D) ℂ)
    (groups : Fin k → Finset (Fin r)) : ℝ :=
  if k < 2 then 0 else multipartiteSquashed false .total (groupedDensity rho groups)

/-- PDF p.12, (A1), left side. Physical positions are S=0, P_i=i for
1<=i<=m, Q_i=m+i for 1<=i<=n, E1=m+n+1, E2=m+n+2.
Parties are S, P1 Q1, ..., Pn Qn, P(n+1), ..., Pm; both environments are discarded. -/
def lemma5LeftGroups (m n : ℕ) : Fin (m + 1) → Finset (Fin (m + n + 3)) :=
  fun j => Finset.univ.filter fun t =>
    if j.val = 0 then t.val = 0
    else t.val = j.val ∨ (j.val ≤ n ∧ t.val = m + j.val)

/-- PDF p.12, (A1), first right term: parties SQ1...QnE2, P1, ..., Pm.
Only E1 is discarded. The environment E2 is retained in the first honest party. -/
def lemma5FirstGroups (m n : ℕ) : Fin (m + 1) → Finset (Fin (m + n + 3)) :=
  fun j => Finset.univ.filter fun t =>
    if j.val = 0 then
      t.val = 0 ∨ (m + 1 ≤ t.val ∧ t.val ≤ m + n) ∨ t.val = m + n + 2
    else t.val = j.val

/-- PDF p.12, (A1), second right term: parties SP1...PmE1, Q1, ..., Qn.
Only E2 is discarded. The environment E1 is retained in the first honest party. -/
def lemma5SecondGroups (m n : ℕ) : Fin (n + 1) → Finset (Fin (m + n + 3)) :=
  fun j => Finset.univ.filter fun t =>
    if j.val = 0 then t.val ≤ m ∨ t.val = m + n + 1
    else t.val = m + j.val

/-- The zero-list boundary leaves exactly S on the left, not either environment. -/
example (j : Fin 1) : lemma5LeftGroups 0 0 j = {0} := by
  have hj : j.val = 0 := by omega
  ext t
  simp only [lemma5LeftGroups, Finset.mem_filter, Finset.mem_univ,
    true_and, hj, if_pos rfl, Finset.mem_singleton]
  constructor
  · intro ht
    exact Fin.ext ht
  · intro ht
    exact congrArg Fin.val ht

/-- A one-party marginal has zero squashed entanglement, including when m=n=0. -/
example {r : ℕ} {D : Fin r → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (PhysicalBasis D) (PhysicalBasis D) ℂ)
    (groups : Fin 1 → Finset (Fin r)) : groupedSquashed rho groups = 0 := by
  simp [groupedSquashed]

/-- A one-dimensional physical product state remains normalized after grouping
and discarding. This also checks the partial-trace sum has no extra multiplicity. -/
example {r k : ℕ} (groups : Fin k → Finset (Fin r))
    (a b : GroupedBasis (fun _ : Fin r => Unit) groups) :
    groupedDensity (D := fun _ : Fin r => Unit) (fun _ _ => 1) groups a b = 1 := by
  simp [groupedDensity]

end QAlgorithms.Papers.Independent.Bridge50.P26


