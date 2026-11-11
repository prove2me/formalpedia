-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Reduction
-- name    : SparsestCutOracle_Main_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:23.205357+00:00
-- url     : https://prove2.me/theorems/152ba437-be95-495e-b260-d13f49bf4551
-- title:
--   The constructed graph for the weighted-to-unweighted reduction
-- statement:
--   For fixed $R,\xi>0$, a set $A$, and weights $\pi$, set
--
--   $$\mu=\frac{\xi\pi(A)}{64R^2n},\qquad k_i=\lfloor\pi(i)/\mu\rfloor\ (i\in A),\qquad
--   z=n+\sum_{i\in A}k_i-|\{i\in A:k_i\ge1\}|.$$
--
--   A vertex with $k_i\ge1$ is replaced by $k_i$ copies; other vertices are retained once. Copies form a cycle of capacity $M=c_Mz(\operatorname{cap}(E)+\alpha)$, with no edge for one copy and one edge for two copies. Original edges join chosen representatives and preserve capacities. Copy vectors are $w_i/R$ on replaced vertices and zero elsewhere. The parent map defines a canonical lift of cuts. The graph is computed from these data, rather than quantified as an unrelated graph satisfying desired conclusions.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 31–33, §5.2 and Claim 3

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

noncomputable def reductionMu {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ) : ℝ :=
  ξ * mass π A / (64 * R ^ 2 * n)

noncomputable def units {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ) (i : Fin n) : ℕ :=
  if i ∈ A then ⌊π i / reductionMu π A R ξ⌋₊ else 0

noncomputable def copies {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ) (i : Fin n) : ℕ :=
  max 1 (units π A R ξ i)

abbrev RedVertex {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ) :=
  (i : Fin n) × Fin (copies π A R ξ i)

noncomputable def redZ {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ) : ℕ :=
  Fintype.card (RedVertex π A R ξ)

noncomputable def redIndex {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ) :
    RedVertex π A R ξ ≃ Fin (redZ π A R ξ) := Fintype.equivFin _

noncomputable def representative {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ)
    (i : Fin n) : Fin (redZ π A R ξ) :=
  redIndex π A R ξ ⟨i, ⟨0, by unfold copies; omega⟩⟩

noncomputable def parent {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ)
    (h : Fin (redZ π A R ξ)) : Fin n := ((redIndex π A R ξ).symm h).1

/-- k=1 has no edge; k=2 has one edge; k≥3 has its k cycle edges. -/
noncomputable def cycleEdges (k : ℕ) (M : NNReal) : Graph k :=
  if h : 2 ≤ k then
    if k = 2 then [⟨⟨0, by omega⟩, ⟨1, by omega⟩, M⟩] else
      (List.finRange k).map fun j =>
        ⟨j, ⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩, M⟩
  else []

noncomputable def reductionM {n : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (A : Finset (Fin n)) (R ξ α cM : ℝ) : ℝ :=
  cM * redZ π A R ξ * (G.total + α)

/-- The §5.2 graph is constructed from the input. Its cycles are not free graph parameters. -/
noncomputable def reductionGraph {n : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (A : Finset (Fin n)) (R ξ α cM : ℝ) : Graph (redZ π A R ξ) :=
  (G.map fun e => ⟨representative π A R ξ e.u, representative π A R ξ e.v, e.capacity⟩) ++
  ((List.finRange n).flatMap fun i =>
    (cycleEdges (copies π A R ξ i) (reductionM G π A R ξ α cM).toNNReal).map fun e =>
      ⟨redIndex π A R ξ ⟨i, e.u⟩, redIndex π A R ξ ⟨i, e.v⟩, e.capacity⟩)

noncomputable def redA {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ) :
    Finset (Fin (redZ π A R ξ)) :=
  Finset.univ.filter fun h => 1 ≤ units π A R ξ (parent π A R ξ h)

noncomputable def redGram {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ)
    (X : Mat n) : Mat (redZ π A R ξ) :=
  fun h k => if h ∈ redA π A R ξ ∧ k ∈ redA π A R ξ then
    X (parent π A R ξ h) (parent π A R ξ k) / R ^ 2 else 0

noncomputable def liftCut {n : ℕ} (π : Fin n → ℝ) (A : Finset (Fin n)) (R ξ : ℝ)
    (S : Finset (Fin n)) : Finset (Fin (redZ π A R ξ)) :=
  Finset.univ.filter fun h => parent π A R ξ h ∈ S

end SparsestCutOracle.Main


