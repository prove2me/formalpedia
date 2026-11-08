-- Prove2me | Definitions.Def_QuadraticRE_rowSamp
-- name    : QuadraticRE_rowSamp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:11:40.106919+00:00
-- url     : https://prove2.me/theorems/83f75cdf-2efb-425c-8e0b-56019af932b8
-- title:
--   The row sampler $\mathrm{RowSamp}$ and the selected sets $S_C$, $S_A$
-- statement:
--   For fresh uniform bits $U,V,T$,
--   $$\mathrm{RowSamp}(y_i,c_i,a_i)=\begin{cases}(U,V,T),&y_i=1,\\(U,V,0),&y_i=0,\ c_i=0,\\(U,V,U+a_iV),&y_i=0,\ c_i=1,\end{cases}$$
--   run once for every row of every leaf with fresh bits. The selected sets are $S_C(y)=\{i:y_i=0\}$ and $S_A(c,y)=\{i:y_i=0,\ c_i=1\}$, and $P_y=\{\eta\in\mathbb F_2^L:\sum_i\eta_i=y\}$. The set $S_A$ can be computed from $y$ and the selected $c$-shares $c[S_C]$ alone.
--
--   These describe Step 1 of the privacy proof.
--
--   **Formalization Note** The fresh bits form an array indexed by leaf, row and the three coordinates $U,V,T$. The second computation of $S_A$ takes $y$ and a vector on $S_C(y)$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), eq. (6), p.20; p.21

import Mathlib
import Definitions.Def_QuadraticRE_encE

namespace QuadraticRE

/-- The row sampler (6) of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.20, on the fresh bits `U, V, T`:
`(U, V, T)` if `y = 1`; `(U, V, 0)` if `y = 0, c = 0`; `(U, V, U + aV)` if `y = 0, c = 1`. -/
def rowSamp (y c a U V T : F2) : Fin 3 → F2 :=
  if y = 1 then ![U, V, T] else if c = 0 then ![U, V, 0] else ![U, V, U + a * V]

/-- Fresh bits for every call of `RowSamp`: leaf, row, and the coordinates `U, V, T`. -/
abbrev Coins (j h : ℕ) : Type := Fin (4 ^ j) → Fin h → Fin 3 → F2

/-- Runs `RowSamp(y_i, c_i, a_i)` for every row of every leaf, with fresh bits. -/
def sampleFrom {j h : ℕ} (aL cL η : Fin (4 ^ j) → F2) (ω : Coins j h) : Encoded j h :=
  fun i => Matrix.of fun r => rowSamp (η i) (cL i) (aL i) (ω i r 0) (ω i r 1) (ω i r 2)

/-- `P_y = {η ∈ F₂^L : ∑_i η_i = y}`, p.21. -/
abbrev Py (j : ℕ) (y : F2) : Type := {η : Fin (4 ^ j) → F2 // ∑ i, η i = y}

/-- `S_C(y) = {i : y_i = 0}`, p.21. -/
def selC {j : ℕ} (η : Fin (4 ^ j) → F2) : Finset (Fin (4 ^ j)) :=
  Finset.univ.filter (fun i => η i = 0)

/-- `S_A(c, y) = {i : y_i = 0, c_i = 1}`, p.21. -/
def selA {j : ℕ} (cL η : Fin (4 ^ j) → F2) : Finset (Fin (4 ^ j)) :=
  Finset.univ.filter (fun i => η i = 0 ∧ cL i = 1)

open Classical in
/-- The set `S_A` as computed from `y` and the selected `c`-shares alone, the second stage of the
selection, p.21: "those `c`-shares tell us which `a`-shares to read". -/
noncomputable def selAOf {j : ℕ} (η : Fin (4 ^ j) → F2) (cS : selC η → F2) : Finset (Fin (4 ^ j)) :=
  Finset.univ.filter (fun i => ∃ hi : i ∈ selC η, cS ⟨i, hi⟩ = 1)

end QuadraticRE


