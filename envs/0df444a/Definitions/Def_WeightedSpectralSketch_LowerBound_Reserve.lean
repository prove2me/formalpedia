-- Prove2me | Definitions.Def_WeightedSpectralSketch_LowerBound_Reserve
-- name    : WeightedSpectralSketch_LowerBound_Reserve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:06:27.106213+00:00
-- url     : https://prove2.me/theorems/636a17cc-55d5-49d7-8f5d-0e8d321e812c
-- title:
--   Reserves $T_i$, auxiliary sets $S_i$, reserve-goodness, root-star terms, transitions and routing paths (§5)
-- statement:
--   Let $b=t+s+1$. In every block the slots $0,\dots,t-1$ are **reserve** slots, $t,\dots,t+s-1$ **auxiliary** slots and $t+s$ the **spare** slot. Under a ring labeling $\sigma$, $T_i$ and $S_i$ are the vertices in the reserve and auxiliary slots of block $i$, and the query endpoints $x,y$ are the vertices in the spare slots of blocks $0$ and $\ell/2$; $q=xy$. Let $B=[b_e:e\in\binom R2]$ be a real matrix.
--
--   1. For a reserve $T$ and $v\notin T\cup\{y\}$, $[B_{v,T}\,B_{y,T}\,B_T]$ consists of the columns of edges from $v$ to $T$, from $y$ to $T$ and within $T$. The vertex $v$ is **reserve-good for $T_i$** if $v\notin T_i\cup\{y\}$ and $\mathrm{lev}_{b_{vy}}([B_{v,T_i}\,B_{y,T_i}\,B_{T_i}])\le1$.
--   2. For reserve-good $v$, let $\alpha^{(v)}$ be the minimum-norm coefficients of Eq. (7), $b_{vy}=B_{v,T_i}\alpha^{(v)}_{v,T_i}+B_{y,T_i}\alpha^{(v)}_{y,T_i}+B_{T_i}\alpha^{(v)}_{T_i}$. The **root-star term** is $B_{y,T_i}\alpha^{(v)}_{y,T_i}$ (set to $0$ when $v$ is not reserve-good).
--   3. For blocks $i,j$: $\beta^v=B_{y,T_i}\alpha^{(v)}_{y,T_i}-B_{y,T_j}\alpha^{(v)}_{y,T_j}$ when $v$ is reserve-good for both reserves, and $\beta^v=0$ otherwise.
--   4. For distinct $i,j$, **$i\to j$ is a transition** if the event $E_1$ of p. 16 holds: $x$ is reserve-good for $T_i$ and $T_j$, and $\mathrm{lev}_{\beta^x}\big((\beta^v)_{v\in S_i}\big)\le1$.
--   5. A **transition path** is an increasing list $0=i_0<i_1<\dots<i_m=\ell/2$ of blocks in which each consecutive pair is a transition. Its **cost** is $\sum_{j=1}^mL(i_j,i_{j-1})^8$.
--
--   These objects build the telescoping representation (8) of the query column. A transition depends only on $x,y,T_i,T_j,S_i$ (and the fixed matrix).
--
--   **Formalization Note.** The slot groups are fixed positions in `Fin (t+s+1)`, so only their labels are random. The minimum-norm coefficients are unique, so no ordering of coordinates is needed.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, pp. 14–17, §5.1 (reserve, auxiliary and spare slots; reserve-goodness; Eq. (7); telescoping (8)), proof of Lemma 5.4 p. 16 (β^v, event E_1), §5.3 p. 17 (transitions, paths), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage
import Definitions.Def_WeightedSpectralSketch_LowerBound_Ring

open Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-!
Reserve, auxiliary and spare slots (§5.1, p. 14). Every block of `b = t + s + 1` slots has the
positions `0, …, t-1` (reserve), `t, …, t+s-1` (auxiliary) and `t + s` (spare). A ring labeling is a
bijection `σ : Fin ℓ × Fin (t + s + 1) ≃ R`; the vertex in slot `(i, j)` is `σ (i, j)`.
-/

/-- The reserve `T_i`: the vertices in the `t` reserve slots of block `i`. -/
noncomputable def reserveSet {ℓ t s : ℕ} {R : Type*} [Fintype R] (σ : Fin ℓ × Fin (t + s + 1) ≃ R)
    (i : Fin ℓ) : Finset R :=
  open Classical in Finset.univ.filter fun v => (σ.symm v).1 = i ∧ ((σ.symm v).2 : ℕ) < t

/-- The auxiliary set `S_i`: the vertices in the `s` auxiliary slots of block `i`. -/
noncomputable def auxSet {ℓ t s : ℕ} {R : Type*} [Fintype R] (σ : Fin ℓ × Fin (t + s + 1) ≃ R)
    (i : Fin ℓ) : Finset R :=
  open Classical in Finset.univ.filter fun v =>
    (σ.symm v).1 = i ∧ t ≤ ((σ.symm v).2 : ℕ) ∧ ((σ.symm v).2 : ℕ) < t + s

/-- The query endpoint `x`: the vertex in the spare slot of block `0`. -/
def spareX {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} (σ : Fin ℓ × Fin (t + s + 1) ≃ R) : R :=
  σ (0, Fin.last (t + s))

/-- The query endpoint `y`: the vertex in the spare slot of block `ℓ / 2`. -/
def spareY {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} (σ : Fin ℓ × Fin (t + s + 1) ≃ R) : R :=
  σ (halfBlock ℓ, Fin.last (t + s))

/-- The query edge `q = xy`. -/
def querySym {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} (σ : Fin ℓ × Fin (t + s + 1) ≃ R) : Sym2 R :=
  s(spareX σ, spareY σ)

/-- `e` is a column of `[B_{v,T} B_{y,T} B_T]`: an edge within `T`, from `v` to `T`, or from `y`
to `T` (one endpoint in `T`, the other in `T ∪ {v, y}`). -/
def IsReserveCol {R : Type*} (T : Finset R) (v y : R) (e : EdgeSlot R) : Prop :=
  (∃ u ∈ e.1, u ∈ T) ∧ ∀ u ∈ e.1, u ∈ T ∨ u = v ∨ u = y

/-- `e` lies within `T`: `e ∈ binom(T, 2)`. -/
def IsWithin {R : Type*} (T : Finset R) (e : EdgeSlot R) : Prop := ∀ u ∈ e.1, u ∈ T

/-- `e = uv` with `u ∈ S` and `v ∈ T`. -/
def IsBetween {R : Type*} (S T : Finset R) (e : EdgeSlot R) : Prop :=
  ∃ u v, e.1 = s(u, v) ∧ u ∈ S ∧ v ∈ T

/-- The columns of `[B_{v,T} B_{y,T} B_T]`. -/
def reserveColFamily {R : Type*} {K : Type*} (B : Matrix K (EdgeSlot R) ℝ) (T : Finset R)
    (v y : R) : {e : EdgeSlot R // IsReserveCol T v y e} → K → ℝ :=
  fun e => Bᵀ e.1

/-- `v` is reserve-good for `T_i` with respect to the root `y` (p. 14): `v ∉ T_i ∪ {y}` and
`lev_{b_{vy}}([B_{v,T_i} B_{y,T_i} B_{T_i}]) ≤ 1`. -/
def ReserveGood {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} [Fintype R] {N : ℕ}
    (B : Matrix (Fin N) (EdgeSlot R) ℝ) (σ : Fin ℓ × Fin (t + s + 1) ≃ R) (i : Fin ℓ) (v : R) :
    Prop :=
  open Classical in
  v ∉ reserveSet σ i ∧ v ≠ spareY σ ∧
    lev (reserveColFamily B (reserveSet σ i) v (spareY σ)) (colS B s(v, spareY σ)) ≤ 1

/-- The root-star term `B_{y,T_i} α^{(v)}_{y,T_i}` (p. 15): the part on the `y`–`T_i` columns of the
minimum-norm representation (7) of `b_{vy}` by `[B_{v,T_i} B_{y,T_i} B_{T_i}]`, when `v` is
reserve-good for `T_i`; the zero vector otherwise. -/
noncomputable def rootStar {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} [Fintype R] {N : ℕ}
    (B : Matrix (Fin N) (EdgeSlot R) ℝ) (σ : Fin ℓ × Fin (t + s + 1) ≃ R) (i : Fin ℓ) (v : R) :
    Fin N → ℝ :=
  open Classical in
  if ReserveGood B σ i v then
    ∑ e : {e : EdgeSlot R // IsReserveCol (reserveSet σ i) v (spareY σ) e},
      (if spareY σ ∈ e.1.1 then
        minNormCoeff (reserveColFamily B (reserveSet σ i) v (spareY σ)) (colS B s(v, spareY σ)) e
        else 0) • Bᵀ e.1
  else 0

/-- `β^v = B_{y,T_i} α^{(v)}_{y,T_i} - B_{y,T_j} α^{(v)}_{y,T_j}` when `v` is reserve-good for both
reserves, and `0` otherwise (proof of Lemma 5.4, p. 16). -/
noncomputable def betaVec {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} [Fintype R] {N : ℕ}
    (B : Matrix (Fin N) (EdgeSlot R) ℝ) (σ : Fin ℓ × Fin (t + s + 1) ≃ R) (i j : Fin ℓ) (v : R) :
    Fin N → ℝ :=
  open Classical in
  if ReserveGood B σ i v ∧ ReserveGood B σ j v then rootStar B σ i v - rootStar B σ j v else 0

/-- The transition `i → j` (p. 17): for distinct blocks, the event `E₁` of p. 16 — `x` is
reserve-good for `T_i` and `T_j` and `lev_{β^x}((β^v)_{v ∈ S_i}) ≤ 1`. -/
def IsTransition {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} [Fintype R] {N : ℕ}
    (B : Matrix (Fin N) (EdgeSlot R) ℝ) (σ : Fin ℓ × Fin (t + s + 1) ≃ R) (i j : Fin ℓ) : Prop :=
  i ≠ j ∧ ReserveGood B σ i (spareX σ) ∧ ReserveGood B σ j (spareX σ) ∧
    lev (fun v : auxSet σ i => betaVec B σ i j v.1) (betaVec B σ i j (spareX σ)) ≤ 1

/-- An increasing path `0 = i₀ < i₁ < ⋯ < i_m = ℓ/2` of transitions. -/
def IsTransitionPath {ℓ t s : ℕ} [NeZero ℓ] {R : Type*} [Fintype R] {N : ℕ}
    (B : Matrix (Fin N) (EdgeSlot R) ℝ) (σ : Fin ℓ × Fin (t + s + 1) ≃ R) (l : List (Fin ℓ)) :
    Prop :=
  l.head? = some 0 ∧ l.getLast? = some (halfBlock ℓ) ∧
    l.IsChain (fun a c => a < c ∧ IsTransition B σ a c)

/-- The routing cost `∑_{j=1}^m L(i_j, i_{j-1})^8` of a path `[i₀, …, i_m]`. -/
def pathCost (ℓ : ℕ) (l : List (Fin ℓ)) : ℕ :=
  ((l.zip l.tail).map fun p => cycDist ℓ p.2 p.1 ^ 8).sum

end WeightedSpectralSketch.LowerBound


