-- Prove2me | Definitions.Def_RandGraphStates_nullity
-- name    : RandGraphStates_nullity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:38.312579+00:00
-- url     : https://prove2.me/theorems/d51595b3-8a47-4249-8bef-ea7f6c8d2ec6
-- title:
--   Nullity over $\mathbb F_2$, the adjacency matrix, leading submatrices, and the events $\mathcal E^{\mathrm{sp}}$, $\mathcal E^{\mathrm{mid}}$
-- statement:
--   All matrices are over $\mathbb F_2$. For a square matrix $M$, $\mathrm{Nullity}(M):=\dim_{\mathbb F_2}\ker M$, and $|v|$ is the Hamming weight of $v$. $A_G$ is the adjacency matrix of $G$. For an $m\times m$ matrix $M$ with leading principal $j\times j$ submatrices $M_j$, and $1\le j_0\le m$, $1\le L_0\le L_1$,
--   $$
--   \mathcal E^{\mathrm{sp}}_{j_0,L_0}(M):=\{\exists j\in[j_0,m],\ 0\neq v\in\ker(M_j):|v|\le L_0\},
--   $$
--   $$
--   \mathcal E^{\mathrm{mid}}_{j_0,L_0,L_1}(M):=\{\exists j\in[j_0,m],\ v\in\ker(M_j):L_0<|v|\le L_1\}.
--   $$
--   These events isolate the matrices whose exposure produces kernel vectors of small or intermediate weight.
--
--   **Formalization Note** The paper also calls $M_j$ "leading principal minors"; they are submatrices, not determinants. The adjacency matrix is taken with a classical decidability instance, so it applies to every graph.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §4, p.17, §4.2.2, p.20, and §4.2.4, p.26

import Mathlib

set_option autoImplicit false

namespace RandGraphStates

/-- `Nullity(M) := dim_{F₂} ker M`, for a square matrix over `F₂`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), §4, p.17. -/
noncomputable def nullity {ι : Type*} [Fintype ι] (M : Matrix ι ι (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin)

open scoped Classical in
/-- `A_G`, the adjacency matrix of `G` over `F₂`. Source: ibid., §4, p.17. -/
noncomputable def adjF2 {V : Type*} (G : SimpleGraph V) : Matrix V V (ZMod 2) :=
  G.adjMatrix (ZMod 2)

/-- The leading principal `j × j` submatrix `M_j` of an `m × m` matrix `M`. The paper also calls
these "leading principal minors"; they are submatrices, not determinants.

Source: ibid., §4.2.2, p.20. -/
def leadingSub {m : ℕ} (M : Matrix (Fin m) (Fin m) (ZMod 2)) {j : ℕ} (hj : j ≤ m) :
    Matrix (Fin j) (Fin j) (ZMod 2) :=
  M.submatrix (Fin.castLE hj) (Fin.castLE hj)

/-- `E^sp_{j₀,L₀}(M) := {∃ j ∈ [j₀, m], 0 ≠ v ∈ ker(M_j) : |v| ≤ L₀}`, where `|v|` is Hamming
weight. Source: ibid., §4.2.4, p.26. -/
def Esp {m : ℕ} (j0 L0 : ℕ) (M : Matrix (Fin m) (Fin m) (ZMod 2)) : Prop :=
  ∃ (j : ℕ) (hj : j ≤ m), j0 ≤ j ∧ ∃ v : Fin j → ZMod 2,
    v ≠ 0 ∧ (leadingSub M hj).mulVec v = 0 ∧ hammingNorm v ≤ L0

/-- `E^mid_{j₀,L₀,L₁}(M) := {∃ j ∈ [j₀, m], v ∈ ker(M_j) : L₀ < |v| ≤ L₁}`.
Source: ibid., §4.2.4, p.26. -/
def Emid {m : ℕ} (j0 L0 L1 : ℕ) (M : Matrix (Fin m) (Fin m) (ZMod 2)) : Prop :=
  ∃ (j : ℕ) (hj : j ≤ m), j0 ≤ j ∧ ∃ v : Fin j → ZMod 2,
    (leadingSub M hj).mulVec v = 0 ∧ L0 < hammingNorm v ∧ hammingNorm v ≤ L1

end RandGraphStates


