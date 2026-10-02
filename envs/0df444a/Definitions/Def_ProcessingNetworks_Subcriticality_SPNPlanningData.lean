-- Prove2me | Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
-- name    : ProcessingNetworks_Subcriticality_SPNPlanningData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:23:28.45507+00:00
-- url     : https://prove2.me/theorems/d9067cda-2642-406d-88c4-0e451700b68c
-- title:
--   Static planning problem model data (Section 5.2)
-- statement:
--   This bundles the first-order data of a stochastic processing network (SPN) that the **static
--   planning problem** of Section 5.2 is built from.
--
--   An SPN has $I$ buffers and $J$ activities. `B` is the $I \times J$ **material requirement
--   matrix**: $B_{ij}$ is the number of class-$i$ items consumed by one unit of a type-$j$ service.
--   `Γ` is the $I \times J$ **mean output matrix**: its $j$th column is the expected vector of
--   items produced into the $I$ buffers by one type-$j$ service (Assumption 2.1(b)). `m j > 0` is
--   the mean service time of activity $j$. `A` is the $K \times J$ **capacity consumption matrix**
--   (server pool $k$ against activity $j$), and `b : Fin K → ℝ`, with every entry positive, is the
--   vector of server-pool capacities.
--
--   From this data, Eq. (5.3) forms
--   $$
--   R := (B - \Gamma) M^{-1}, \qquad M := \operatorname{diag}(m_1, \dots, m_J),
--   $$
--   so that $R_{ij}$ is the long-run average rate at which activity $j$ depletes the content of
--   buffer $i$ (a negative entry means activity $j$ increases buffer $i$'s content on average).
--
--   Two specializations are also recorded. `ofOutputMatrix` re-indexes an output matrix given in
--   the row-major convention `Fin J → Fin I → ℝ` (as `BaselineAssumptions`'s mean-output field is
--   indexed) into `SPNPlanningData`'s column-major `Γ`. `ofUnitary` specializes to a **unitary
--   network** (Section 2.6, one activity per class): `B` is the identity (each activity is
--   dedicated to its own class) and `Γ := Pᵀ`, where `P` is the class-to-class routing matrix, so
--   that $R = (I - P^\top)M^{-1}$ matches the book's own specialization of (5.3) for this case.
--
--   **Formalization note.** `R` and the two constructors are `noncomputable` because `Matrix`
--   multiplication and inversion over `ℝ` are not executable in general; this affects nothing at the
--   level of statements, since every downstream use is propositional.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 92-94, Section 5.2 (Eq. 5.3)

import Mathlib

namespace ProcessingNetworks.Subcriticality

/-- The static planning problem's model data (Section 5.2, p. 92, PDF p. 108): the `I × J`
material requirement matrix `B` (the `(i,j)`-entry is the number of class-`i` items consumed by a
type-`j` service), the `I × J` mean output matrix `Γ` (whose `j`th column is the expected output
vector from a class-`j` service, Assumption 2.1(b)), the mean service times `m j > 0`
(Assumption 2.1(b)), the `K × J` capacity consumption matrix `A`, and the `K`-vector of server
capacities `b > 0`. -/
structure SPNPlanningData (I J K : ℕ) where
  B : Matrix (Fin I) (Fin J) ℝ
  Γ : Matrix (Fin I) (Fin J) ℝ
  m : Fin J → ℝ
  hm : ∀ j, 0 < m j
  A : Matrix (Fin K) (Fin J) ℝ
  b : Fin K → ℝ
  hb : ∀ k, 0 < b k

/-- Eq. (5.3), p. 93 (PDF p. 109): `R := (B - Γ)M⁻¹` where `M = diag(m₁,…,m_J)`. `R i j` is the
long-run average rate at which activity `j` depletes the content of buffer `i`. -/
noncomputable def SPNPlanningData.R {I J K : ℕ} (D : SPNPlanningData I J K) :
    Matrix (Fin I) (Fin J) ℝ :=
  (D.B - D.Γ) * Matrix.diagonal (fun j => (D.m j)⁻¹)

/-- Bridge from the raw material-requirement/output/service-time/capacity data to
`SPNPlanningData`, used to instantiate the static planning problem when `Γ` and `m` are already
supplied in `Fin J → Fin I → ℝ`/`Fin J → ℝ` form (`BaselineAssumptions`'s convention). -/
noncomputable def SPNPlanningData.ofOutputMatrix {I J : ℕ} (B : Matrix (Fin I) (Fin J) ℝ)
    (Γrow : Fin J → Fin I → ℝ) (m : Fin J → ℝ) (hm : ∀ j, 0 < m j) {K : ℕ}
    (A : Matrix (Fin K) (Fin J) ℝ) (b : Fin K → ℝ) (hb : ∀ k, 0 < b k) :
    SPNPlanningData I J K :=
  { B := B, Γ := fun i j => Γrow j i, m := m, hm := hm, A := A, b := b, hb := hb }

/-- Specialization of `SPNPlanningData` to a unitary network (Section 2.6): `B := 1` (each
activity is dedicated to depleting exactly one unit of its own class) and `Γ := Pᵀ` (a completed
class-`i` service becomes a class-`j` item with probability `P i j`), so that
`R = (1 - Pᵀ)M⁻¹` matches the book's specialization of (5.3) for a unitary network (p. 94,
PDF p. 110). -/
noncomputable def SPNPlanningData.ofUnitary {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ)
    (m : Fin I → ℝ) (hm : ∀ i, 0 < m i) {K : ℕ} (A : Matrix (Fin K) (Fin I) ℝ) (b : Fin K → ℝ)
    (hb : ∀ k, 0 < b k) : SPNPlanningData I I K :=
  { B := 1, Γ := P.transpose, m := m, hm := hm, A := A, b := b, hb := hb }

end ProcessingNetworks.Subcriticality


