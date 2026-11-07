-- Prove2me | Definitions.Def_KMeansTaper_unitCost
-- name    : KMeansTaper_unitCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:17.625574+00:00
-- url     : https://prove2.me/theorems/2f02e752-5122-4a15-9b1e-3cc7ac1cd9ae
-- title:
--   Squared nearest-unit costs of fractional and grid openings on pieces
-- statement:
--   Let $I$ be an instance and $y$ fractional openings, $0\le y_i\le1$, supported on $F$. Client $j$ takes a unit of opening from its nearest facilities, and its **squared nearest-unit cost** is
--
--   $$V_j=\min\Bigl\{\sum_i x_i\,d(j,i)^2:\ 0\le x_i\le y_i,\ x_i=0\ (i\notin F),\ \sum_i x_i=1\Bigr\},$$
--
--   the greedy value $\sum_{i\in F_j}y_id(j,i)^2$ with $y(F_j)=1$. For a grid $g=1/\Delta$, **grid openings** are a list of pieces $(\ell_p,Y_p)$: a co-located piece at facility $\ell_p$ with opening $Y_p/\Delta\in g\mathbb Z\cap[0,1]$; their **mass** is $M=\sum_pY_p/\Delta$, and the squared nearest-unit cost $\tilde V_j$ (Theorem A.1), equal to $V_{j,0}$ of Theorem D.17 (the cost of $j$'s nearest $\Delta$ copies of mass $g$), is the same minimum over the pieces. For a set $O$ of pieces, $d(j,O)=\min_{p\in O}d(j,\ell_p)$.
--
--   These quantities measure fractional solutions in the two rounding stages.
--
--   **Formalization Note** The minima are infima of real sets; they are attained and meaningful when the total opening is at least $1$. A piece is a pair of natural numbers; `GridValid` requires $\ell_p$ to be a candidate facility and $Y_p\le\Delta$. `pieceNearest` is $0$ on the empty set, which the statements exclude.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 2, p.3 (PDF p.6); Theorem A.1, p.20 (PDF p.23); Definition A.2, p.20; Theorem D.17, p.40 (PDF p.43)

import Mathlib
import Definitions.Def_MetricKMedian

namespace KMeansTaper

open OAI.MetricKMedian (Instance)

/-- **Squared nearest-unit cost** `V_j` of client `j` for fractional openings `y`, Section 2,
p.3 (PDF p.6) and Definition A.2, p.20 (PDF p.23): client `j` takes a unit of opening mass from
its nearest facilities, `V_j = ∑_{i ∈ F_j} y_i d(j, i)²` with `y(F_j) = 1`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** Written as the value of the fractional knapsack
`min {∑_i x_i d(j, i)² : 0 ≤ x_i ≤ y_i, x_i = 0 off F, ∑_i x_i = 1}`, whose optimum is the
greedy nearest unit (splitting the last facility as the paper's pieces do); ties do not change
the value. It is an `sInf` of reals: meaningful when `∑_{i ∈ F} y_i ≥ 1` (the set is then
nonempty and bounded below by `0`). -/
noncomputable def unitCost (I : Instance) (y : Fin I.n → ℝ) (j : Fin I.n) : ℝ :=
  sInf {v : ℝ | ∃ x : Fin I.n → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ y i) ∧ (∀ i, i ∉ I.facilities → x i = 0) ∧
    ∑ i, x i = 1 ∧ v = ∑ i, x i * (I.distance j i : ℝ) ^ 2}

/-- **Distance from a point to a piece.** A grid solution is a list of **pieces**
`(loc, Y) : ℕ × ℕ`, a co-located labeled piece at facility `loc` carrying opening `Y/Δ`
(Theorem A.1, p.20, PDF p.23; Definition A.2). This is `d(j, loc)`.

**Formalization Note.** `0` if `loc ≥ n`; `GridValid` excludes that case. -/
noncomputable def pieceDist (I : Instance) (j : Fin I.n) (p : ℕ × ℕ) : ℝ :=
  if h : p.1 < I.n then (I.distance j ⟨p.1, h⟩ : ℝ) else 0

/-- **Validity of grid openings** with grid `g = 1/Δ` (Theorem A.1): every piece sits at a
candidate facility and has opening `Y/Δ ∈ gℤ ∩ [0, 1]`, i.e. `Y ≤ Δ`. -/
def GridValid (I : Instance) (Δ : ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ L, ∃ h : p.1 < I.n, (⟨p.1, h⟩ : Fin I.n) ∈ I.facilities ∧ p.2 ≤ Δ

/-- **Mass** `M = ∑_i ỹ_i = (∑ Y)/Δ` of grid openings. -/
noncomputable def gridMass (Δ : ℕ) (L : List (ℕ × ℕ)) : ℝ := ((L.map Prod.snd).sum : ℝ) / Δ

/-- **Squared nearest-unit cost of client `j` for grid openings** on pieces: `Ṽ_j` of
Theorem A.1 and `V_{j,0}` of Theorem D.17 (the cost of `j`'s nearest `Δ` copies of mass `g`),
as the same fractional knapsack over the pieces.

**Formalization Note.** Meaningful when `gridMass Δ L ≥ 1` and `Δ ≥ 1`. -/
noncomputable def pieceUnitCost (I : Instance) (Δ : ℕ) (L : List (ℕ × ℕ)) (j : Fin I.n) : ℝ :=
  sInf {v : ℝ | ∃ x : Fin L.length → ℝ, (∀ p, 0 ≤ x p ∧ x p ≤ ((L.get p).2 : ℝ) / Δ) ∧
    ∑ p, x p = 1 ∧ v = ∑ p, x p * pieceDist I j (L.get p) ^ 2}

/-- **Distance from a client to a set `O` of pieces**, `d(j, O) = min_{p ∈ O} d(j, loc_p)`
(Theorem D.17, p.40, PDF p.43). `0` if `O = ∅`, which every statement excludes. -/
noncomputable def pieceNearest (I : Instance) (L : List (ℕ × ℕ)) (j : Fin I.n)
    (O : Finset (Fin L.length)) : ℝ :=
  if h : O.Nonempty then (O.image (fun p => pieceDist I j (L.get p))).min' (h.image _) else 0

end KMeansTaper


