-- Prove2me | Definitions.Def_IncrementalER_scCond
-- name    : IncrementalER_scCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:40.367202+00:00
-- url     : https://prove2.me/theorems/74e0cbbf-30ed-4d4c-8074-d731e51c90c6
-- title:
--   Schur complements $SC(G,S)$, $\ell^G_T$, $q^G_T$, insertion cost $f_T$, batch cost $g_Q(v;D)$, grounded inverse $K$
-- statement:
--   Let $G$ be a graph with Laplacian $L$ and $S\subseteq W\subseteq V$. Eliminating $W\setminus S$ gives the matrix on $S\times S$
--
--   $$L_{SS}-L_{S,W\setminus S}\,L_{W\setminus S,W\setminus S}^{-1}\,L_{W\setminus S,S}$$
--
--   (Definition 3.3 with ambient vertex set $W$). The **Schur complement** graph $SC(G,S)=G_S$ is the graph whose conductances are minus the off-diagonal entries of this matrix for $W=V$; it lives on $S$. Then:
--
--   1. $\ell^G_T(v)$ is the leverage degree of $v$ in $G_T$, and $q^G_T(v)=\ell^G_T(v)-2$ (Definition 3.5);
--   2. the insertion cost is $f_T(v)=\ell^G_{T\cup\{v\}}(v)$ for $v\notin T$ and $f_T(v)=0$ for $v\in T$ (p.14);
--   3. the batch cost is $g_Q(v;D)=f_{Q\cup D}(v)-f_Q(v)$ for $v\notin Q\cup D$ and $0$ otherwise (p.19);
--   4. $K=L^{-1}_{\bar S,\bar S}$ is the inverse of the grounded Laplacian on $\bar S=V\setminus S$ (p.29).
--
--   These are the objects in which the paper measures how a terminal set reacts to the insertion of further terminals.
--
--   **Formalization Note** The inverse is Mathlib's matrix inverse; it is a true inverse when $G$ is connected on $W$ and $S\neq\emptyset$ (the paper's standing assumption, p.10). $G_S$ is represented on all of $V$ with the vertices outside $S$ isolated, which changes no energy or resistance between vertices of $S$. A general ambient set $W$ is used for $SC(SC(G,T),S)$ and for the hierarchy of the proof of Theorem 1.1.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Definition 3.3, p.11; Definition 3.5, p.12; f_T, p.14; g_Q(v; D), p.19; K, p.29

import Mathlib
import Definitions.Def_IncrementalER_lap

open Matrix

namespace IncrementalER

/-!
# Schur complements, leverage degrees in Schur complements, insertion costs

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Definition 3.3 (p.11),
Definition 3.5 (p.12), the insertion cost `f_T` (p.14), the batch cost `g_Q(v; D)` (p.19), and the
grounded Laplacian inverse `K = L^{−1}_{S̄,S̄}` (p.29).

**Formalization Note.**
* `schurRel L W S` eliminates `W \ S` from `L`: on `S × S` it is
  `L_SS − L_{S,W∖S} (L_{W∖S,W∖S})^{−1} L_{W∖S,S}` (Definition 3.3 with ambient vertex set `W`), and
  it is `0` outside `S × S`. The inverse is Mathlib's matrix inverse, which is invertible here
  when the graph is connected on `W` and `S` is nonempty (the paper's standing assumption, p.10).
  `W = univ` is the paper's `SC(G, S)`; a general `W` is needed for `SC(SC(G, T), S)` (Fact 3.4.4)
  and for the hierarchy of p.39, whose graphs live on subsets.
* The Schur complement graph `G_S = SC(G, S)` is a graph on all of `V` whose conductances are
  minus the off-diagonal entries of `schurRel`; vertices outside `S` are isolated in it. Energies
  and resistances between vertices of `S` do not see isolated vertices.
* `ℓ^G_T(v)` is literally the leverage degree of `v` in the graph `G_T` (Definition 3.5); by
  Fact 3.4.2 it equals `∑_w c_{G_T}(v, w) Reff^G(v, w)`.
* `f_T(v) = 0` for `v ∈ T` (p.14) and `g_Q(v; D) = 0` for `v ∈ Q ∪ D` (p.19).
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Eliminate `W \ S` from `L`: `L_SS − L_{S,W∖S} L_{W∖S,W∖S}^{−1} L_{W∖S,S}` on `S × S`, zero
elsewhere (Definition 3.3). -/
noncomputable def schurRel (L : Matrix V V ℝ) (W S : Finset V) : Matrix V V ℝ :=
  let M : Matrix ↥(W \ S) ↥(W \ S) ℝ := fun a b => L a b
  fun x y =>
    if x ∈ S ∧ y ∈ S then L x y - ∑ a : ↥(W \ S), ∑ b : ↥(W \ S), L x a * M⁻¹ a b * L b y
    else 0

/-- The conductances of the Schur complement of `c` (on vertex set `W`) upon `S`: minus the
off-diagonal entries of `schurRel (lap c) W S`. -/
noncomputable def scCondRel (c : V → V → ℝ) (W S : Finset V) : V → V → ℝ :=
  fun x y => if x ≠ y then -schurRel (lap c) W S x y else 0

/-- The Schur complement graph `G_S = SC(G, S)` (Definition 3.3, p.11). -/
noncomputable def scCond (c : V → V → ℝ) (S : Finset V) : V → V → ℝ :=
  scCondRel c Finset.univ S

/-- The leverage degree `ℓ^G_T(v)` of `v` in the Schur complement `G_T` (Definition 3.5). -/
noncomputable def levDegT (c : V → V → ℝ) (T : Finset V) (v : V) : ℝ :=
  levDeg (scCond c T) v

/-- The excess `q^G_T(v) = ℓ^G_T(v) − 2` (Definition 3.5). -/
noncomputable def excessT (c : V → V → ℝ) (T : Finset V) (v : V) : ℝ :=
  levDegT c T v - 2

/-- The insertion cost `f_T(v) = ℓ^G_{T∪{v}}(v)` for `v ∉ T`, `0` for `v ∈ T` (p.14). -/
noncomputable def insCost (c : V → V → ℝ) (T : Finset V) (v : V) : ℝ :=
  if v ∈ T then 0 else levDegT c (insert v T) v

/-- `g_Q(v; D) = f_{Q∪D}(v) − f_Q(v)` for `v ∉ Q ∪ D`, `0` for `v ∈ Q ∪ D` (p.19). -/
noncomputable def gQ (c : V → V → ℝ) (Q D : Finset V) (v : V) : ℝ :=
  if v ∈ Q ∪ D then 0 else insCost c (Q ∪ D) v - insCost c Q v

/-- The grounded Laplacian inverse `K = L^{−1}_{S̄,S̄}` on `S̄ = V \ S` (p.29). -/
noncomputable def grounded (c : V → V → ℝ) (S : Finset V) : Matrix {x // x ∉ S} {x // x ∉ S} ℝ :=
  (fun a b : {x // x ∉ S} => lap c a b)⁻¹

end IncrementalER


