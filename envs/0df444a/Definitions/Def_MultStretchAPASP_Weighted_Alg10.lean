-- Prove2me | Definitions.Def_MultStretchAPASP_Weighted_Alg10
-- name    : MultStretchAPASP_Weighted_Alg10
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:09:37.055757+00:00
-- url     : https://prove2.me/theorems/31277cf5-30e6-4c31-b873-6cdfc04eab72
-- title:
--   Algorithm 10 (Weighted-2-APASP) and its subroutines (Algorithms 4, 5, 7, 8, 9) as a process over all admissible runs
-- statement:
--   Algorithm 10 maintains a symmetric table $d[\cdot,\cdot]$ of distance estimates with values in $[0,\infty]$. Given the graph $G=(V,E,w)$ with integer weights in $[W_{\max}]$ and the sample $S_1$:
--
--   1. (Algorithm 4, $q_2=0$) $d[u,v]=w(u,v)$ on edges and $\infty$ elsewhere; then $d[u,p(u)]=d[p(u),u]=\delta(u,S_1)$ for a pivot map $p$ of $S_1$; $E_1=E_{S_1}$, $G_1=(V,E_1,w)$.
--   2. (Lines 6–8) for every pair $(u,v)$, in some order: $d[p(u),v]\leftarrow\min\{\delta(p(u),u)+d[u,v],d[p(u),v]\}$, then $d[v,p(u)]\leftarrow\min\{\delta(p(u),u)+d[u,v],d[p(u),v]\}$.
--   3. (Line 9) Algorithm 5 twice on $G_1$ with all vertices as sources: for each source $u$, $\delta_{H_u}(u,\cdot)$ in $G_1$ plus the star $\{(u,v)\text{ of weight }d[u,v]\}$, computed from the table at the start of the call; then $d[u,v]$ and $d[v,u]$ are lowered to $\delta_{H_u}(u,v)$.
--   4. (Line 10, Algorithm 7 with $\varepsilon=0.05$) some $\bar\delta$ with $\delta_G\le\bar\delta\le(1+\varepsilon)\delta_G$ on $S_1\times V$; $d[u,v]$, $d[v,u]$ lowered to $\lfloor\bar\delta(u,v)\rfloor$.
--   5. (Line 11) some entrywise $(1+\varepsilon)$-approximation $\bar d$ of $d[V,S_1]\star d[S_1,V]$; $d[u,v],d[v,u]$ lowered to $\bar d[u,v]$.
--   6. (Lines 12–27) for $j=0,\dots,\lceil\log_2(nW_{\max})\rceil$: buckets $B_{i,j}=\{v: d[v,p(v)]\in[i2^j,(i+1)2^j)\}$; for each nonempty bucket, in some order: $P=p(B_{i,j})$, $Y=B_{i,j}\cup B_{i+1,j}$, $A[p(x),y]=\min\{d[p(x),x]+w(x,y)\}$ over $x\in B_{i,j}$ with $(x,y)\in E$, $w(x,y)\ge d[x,p(x)]$; $B[y,x']=d[x',y]$ for $x'\in Y$ with $d[x',y]\ge d[x',p(x')]$; $M$ a possible output of Algorithm 9 with shifts $2i2^j$, $i2^j$; then for every $(x,x')\in B_{i,j}\times Y$, in some order, $d[x,x']\leftarrow\min\{d[x,x'],d[x,p(x)]+M[p(x),x']\}$ and $d[x',x]\leftarrow\min\{d[x,x'],d[x',x]\}$.
--   7. (Line 28) Algorithm 5 twice again; the output is $d$.
--
--   A table $d$ is a **possible output for the sample $S_1$**, written $\mathrm{Alg10Run}(w,W_{\max},S_1,d)$, if some choice of the pivot map, the loop orders and the black-box outputs produces it. When $S_1=\emptyset$ there are no pivots and $E_1=E$; steps 2 and 4–6 are skipped.
--
--   **Formalization Note.** Every step is the printed one; what the paper leaves free is quantified (existentially in `Alg10Run`, hence universally in every statement about its outputs). Tables are `ℝ≥0∞`-valued because the approximations need not be integers. The sequential loops are folds over an enumeration of their index set (`Enumerates`, `RelFold`); the loops of Algorithms 4, 5, 7 and line 11 are written in closed form because their updates are minima (or, in Algorithm 4, coinciding assignments) and do not depend on the order. A vertex with $d[v,p(v)]=\infty$ lies in no bucket.
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), pp. 13–14, Algorithms 4–5; pp. 19–21, Algorithms 7–10

import Mathlib
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus

set_option autoImplicit false

open scoped ENNReal NNReal Classical

namespace MultStretchAPASP.Weighted

/-!
# Algorithm 10 (`Weighted-2-APASP`) and its subroutines as a mathematical process

Saggi, Sapir, *Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime*,
arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), Algorithms 4–5 (p. 13),
Algorithms 7–9 (pp. 19–20) and Algorithm 10 (p. 21).

A distance-estimate table is `d : Fin n → Fin n → ℝ≥0∞` (`Table n`). Every step is written
exactly as printed; what the paper leaves free is quantified, so that a statement about "the
output of Algorithm 10" holds for every run:

* the sample `S = S₁` (any subset of the vertices; the lemmas hold for every outcome), the pivot
  map `p` (any map with `p u ∈ S₁`, `δ(u, p u) = δ(u, S₁)`), every admissible output of the black
  boxes (the `(1 + ε)`-MSASP of Algorithm 7 and the `(1 + ε)`-approximate (min, +)-products of
  line 11 and of Algorithm 9), and the order in which every `foreach` loop with a sequential
  dependence visits its elements.

The steps:

* `initTable w S p` (Algorithm 4 with `q₂ = 0`, so `S₂ = ∅` and nothing is set for `p₂`):
  `d[u, v] = w(u, v)` (`⊤` off the edges), then `d[u, p(u)] = d[p(u), u] = δ(u, S₁)`. The loop of
  Algorithm 4 writes entry `(x, y)` from `u = x` when `p x = y` and from `u = y` when `p y = x`;
  both values are `δ(x, S₁) = δ(y, S₁) = 0` when both happen (then `x, y ∈ S₁`), so the result does
  not depend on the order of the loop.
* `pivotStep w p (u, v)` (lines 7–8, sequential): first
  `d[p(u), v] ← min{δ(p(u), u) + d[u, v], d[p(u), v]}`, then, on the updated table,
  `d[v, p(u)] ← min{δ(p(u), u) + d[u, v], d[p(u), v]}`. Lines 6–8 fold it over an enumeration of
  `V × V` (quantified).
* `starAug H d u`: `H_u = (V_H, E_H ∪ E_u)`, the star `E_u` having the edge `(u, v)` of weight
  `d[u, v]`; parallel edges keep the smaller weight. `alg5 H S d` (Algorithm 5): all the Dijkstra
  computations use the table at the start, then for every `(u, v) ∈ S × V_H`,
  `d[u, v] ← min{δ_{H_u}(u, v), d[u, v]}` and `d[v, u] ← min{δ_{H_u}(u, v), d[v, u]}`; these
  updates are minima and commute, so entry `(x, y)` becomes
  `min(d[x, y], δ_{H_x}(x, y) if x ∈ S, δ_{H_y}(y, x) if y ∈ S)`.
* `Alg7Out H S ε d d'` (Algorithm 7): some `δ̄` with `δ_H(s, v) ≤ δ̄(s, v) ≤ (1 + ε)δ_H(s, v)` on
  `S × V_H`, then `d[u, v] ← min{⌊δ̄(u, v)⌋, d[u, v]}`, `d[v, u] ← min{⌊δ̄(u, v)⌋, d[v, u]}`.
  `ennFloor` is the floor of a finite value and keeps `⊤`.
* `Line11Out S ε d d'` (line 11): some entrywise `(1 + ε)`-approximation `d̄` of
  `d[V, S₁] ⋆ d[S₁, V]`, then the symmetric update `d[u, v] ← min{d[u, v], d̄[u, v]}`,
  `d[v, u] ← min{d[v, u], d̄[u, v]}` over all pairs.
* `bucket p d j i = B_{i,j}` (Algorithm 8, line 14, width `2^j`): the vertices `v` with
  `d[v, p(v)] ∈ [i·2^j, (i+1)·2^j)`; a vertex with `d[v, p(v)] = ⊤` lies in no bucket. The family
  is computed once per `j` (line 14) and fixed during the loop of line 15.
* `matA w p d B` (lines 18–20): `A[p(x), y] = min{d[p(x), x] + w(x, y)}` over `x ∈ B` with
  `(x, y) ∈ E` and `w(x, y) ≥ d[x, p(x)]`, `⊤` otherwise (rows outside `P = p(B)` are never
  read). `matB p d Y` (lines 18, 21–22): `B[y, x'] = d[x', y]` for `x' ∈ Y` with
  `d[x', y] ≥ d[x', p(x')]`, `⊤` otherwise.
* `updStep p M (x, x')` (lines 26–27, sequential): `d[x, x'] ← min{d[x, x'], d[x, p(x)] +
  M[p(x), x']}`, then `d[x', x] ← min{d[x, x'], d[x', x]}` on the updated table.
* `BucketStep` (lines 16–27 for one bucket `i`): `P = {p(x) | x ∈ B_{i,j}}`,
  `Y = B_{i,j} ∪ B_{i+1,j}`, shifts `2·i·2^j` and `i·2^j`, some output `M` of Algorithm 9 with
  `ε`, and the fold of `updStep` over an enumeration of `B_{i,j} × Y` (quantified).
* `Line12Iter` (lines 13–27 for one `j`): the buckets of line 14, then `BucketStep` for every
  nonempty bucket, in an order that is quantified.
* `Alg10Run w Wmax S d` (Algorithm 10 with `ε = 0.05`, lines 3–29): `d` is a possible output
  when the sample is `S₁ = S`. Lines 6–8 and 10–27 need the pivots; when `S₁ = ∅` (possible, since
  `q₁ = n^{−a}`) there is no pivot, `E₁ = E`, and those lines are skipped: the run is Algorithm 4's
  table followed by the four calls of Algorithm 5 of lines 9 and 28. The loop of line 12 runs
  `j = 0, 1, …, ⌈log₂(n·Wmax)⌉` in increasing order (`Nat.clog 2 (n * Wmax)` is
  `⌈log₂(n·Wmax)⌉`).
-/

/-- A table of distance estimates `d[·, ·]`. -/
abbrev Table (n : ℕ) := Fin n → Fin n → ℝ≥0∞

/-- The list `l` enumerates the set `s`: each element of `s` exactly once, nothing else. -/
def Enumerates {β : Type*} (l : List β) (s : Set β) : Prop :=
  l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ s

/-- A loop with a nondeterministic body: `RelFold R l d d'` holds when `d'` can be reached from
`d` by performing one admissible step `R b` for every element `b` of `l`, in the order of `l`. -/
inductive RelFold {β γ : Type*} (R : β → γ → γ → Prop) : List β → γ → γ → Prop
  | nil (d : γ) : RelFold R [] d d
  | cons (b : β) (l : List β) (d d₁ d₂ : γ) :
      R b d d₁ → RelFold R l d₁ d₂ → RelFold R (b :: l) d d₂

/-- The table `d` with the entry `(x, y)` set to `val`. -/
def setEntry {n : ℕ} (d : Table n) (x y : Fin n) (val : ℝ≥0∞) : Table n :=
  fun a b => if a = x ∧ b = y then val else d a b

/-- Algorithm 4 with `q₂ = 0`: edge weights, `⊤` elsewhere, and `d[u, p(u)] = d[p(u), u] = δ(u, S)`. -/
noncomputable def initTable {n : ℕ} (w : WMat n) (S : Finset (Fin n)) (p : Fin n → Fin n) :
    Table n :=
  fun x y => if p x = y then distSet w x S else if p y = x then distSet w y S else w x y

/-- Lines 7–8 of Algorithm 10 for the pair `(u, v)`. -/
noncomputable def pivotStep {n : ℕ} (w : WMat n) (p : Fin n → Fin n) (uv : Fin n × Fin n)
    (d : Table n) : Table n :=
  let u := uv.1
  let v := uv.2
  let d₁ := setEntry d (p u) v (min (dist w (p u) u + d u v) (d (p u) v))
  setEntry d₁ v (p u) (min (dist w (p u) u + d₁ u v) (d₁ (p u) v))

/-- The star-augmented graph `H_u = (V_H, E_H ∪ E_u)` of Algorithm 5. -/
def starAug {n : ℕ} (H : WMat n) (d : Table n) (u : Fin n) : WMat n :=
  fun x y => min (H x y) (if x = u then d u y else if y = u then d u x else ⊤)

/-- Algorithm 5, `Estimate_augmented_MSSP(H, S, d)`: the table after the call. -/
noncomputable def alg5 {n : ℕ} (H : WMat n) (S : Finset (Fin n)) (d : Table n) : Table n :=
  fun x y => min (d x y)
    (min (if x ∈ S then dist (starAug H d x) x y else ⊤)
      (if y ∈ S then dist (starAug H d y) y x else ⊤))

/-- The floor of a finite value; `⊤` stays `⊤`. -/
noncomputable def ennFloor (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ((⌊x.toReal⌋₊ : ℕ) : ℝ≥0∞)

/-- Algorithm 7, `Approximate_MSSP(H, S, d, ε)`: `d'` is a possible table after the call. -/
def Alg7Out {n : ℕ} (H : WMat n) (S : Finset (Fin n)) (ε : ℝ) (d d' : Table n) : Prop :=
  ∃ δbar : Table n,
    (∀ s ∈ S, ∀ v : Fin n,
      dist H s v ≤ δbar s v ∧ δbar s v ≤ ENNReal.ofReal (1 + ε) * dist H s v) ∧
    d' = fun x y => min (d x y)
      (min (if x ∈ S then ennFloor (δbar x y) else ⊤) (if y ∈ S then ennFloor (δbar y x) else ⊤))

/-- Line 11 of Algorithm 10: `d'` is a possible table after the line. -/
def Line11Out {n : ℕ} (S : Finset (Fin n)) (ε : ℝ) (d d' : Table n) : Prop :=
  ∃ dbar : Table n, IsApproxMinPlus ε Finset.univ S Finset.univ d d dbar ∧
    d' = fun x y => min (d x y) (min (dbar x y) (dbar y x))

/-- Algorithm 8 with width `2^j`: the bucket `B_{i,j}`. -/
noncomputable def bucket {n : ℕ} (p : Fin n → Fin n) (d : Table n) (j i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v =>
    ((i * 2 ^ j : ℕ) : ℝ≥0∞) ≤ d v (p v) ∧ d v (p v) < (((i + 1) * 2 ^ j : ℕ) : ℝ≥0∞)

/-- Lines 18–20: the matrix `A_{i,j}` (rows indexed by pivots, columns by vertices). -/
noncomputable def matA {n : ℕ} (w : WMat n) (p : Fin n → Fin n) (d : Table n)
    (B : Finset (Fin n)) : Table n :=
  fun r y => ⨅ x ∈ B, if p x = r ∧ w x y ≠ ⊤ ∧ d x (p x) ≤ w x y then d (p x) x + w x y else ⊤

/-- Lines 18, 21–22: the matrix `B_{i,j}` (rows indexed by vertices `y`, columns by `x' ∈ Y`). -/
noncomputable def matB {n : ℕ} (p : Fin n → Fin n) (d : Table n) (Y : Finset (Fin n)) :
    Table n :=
  fun y x' => if x' ∈ Y ∧ d x' (p x') ≤ d x' y then d x' y else ⊤

/-- Lines 26–27 for the pair `(x, x')`. -/
noncomputable def updStep {n : ℕ} (p : Fin n → Fin n) (M : Table n) (xx : Fin n × Fin n)
    (d : Table n) : Table n :=
  let x := xx.1
  let x' := xx.2
  let d₁ := setEntry d x x' (min (d x x') (d x (p x) + M (p x) x'))
  setEntry d₁ x' x (min (d₁ x x') (d₁ x' x))

/-- Lines 16–27 for the bucket `B_{i,j} = Bfam i` of the family `Bfam` computed at line 14. -/
def BucketStep {n : ℕ} (ε : ℝ) (w : WMat n) (p : Fin n → Fin n) (Bfam : ℕ → Finset (Fin n))
    (j i : ℕ) (d d' : Table n) : Prop :=
  ∃ (M : Table n) (ord : List (Fin n × Fin n)),
    IsOffsetShiftedOut ε ((Bfam i).image p) Finset.univ (Bfam i ∪ Bfam (i + 1))
      (matA w p d (Bfam i)) (matB p d (Bfam i ∪ Bfam (i + 1)))
      (((2 * i * 2 ^ j : ℕ) : ℝ≥0)) (((i * 2 ^ j : ℕ) : ℝ≥0)) M ∧
    Enumerates ord ↑(Bfam i ×ˢ (Bfam i ∪ Bfam (i + 1))) ∧
    d' = ord.foldl (fun e xx => updStep p M xx e) d

/-- Lines 13–27 for one value of `j`. -/
def Line12Iter {n : ℕ} (ε : ℝ) (w : WMat n) (p : Fin n → Fin n) (j : ℕ) (d d' : Table n) :
    Prop :=
  ∃ l : List ℕ, Enumerates l {i | (bucket p d j i).Nonempty} ∧
    RelFold (BucketStep ε w p (bucket p d j) j) l d d'

/-- Algorithm 10 with `ε = 0.05`: `dOut` is a possible output when the sample is `S₁ = S`. -/
def Alg10Run {n : ℕ} (w : WMat n) (Wmax : ℕ) (S : Finset (Fin n)) (dOut : Table n) : Prop :=
  if S = ∅ then
    dOut = alg5 (restrictBelow w S) Finset.univ (alg5 (restrictBelow w S) Finset.univ
      (alg5 (restrictBelow w S) Finset.univ (alg5 (restrictBelow w S) Finset.univ w)))
  else
    ∃ (p : Fin n → Fin n) (ord : List (Fin n × Fin n)) (d₁₀ d₁₁ d₂₇ : Table n),
      IsPivotMap w S p ∧ Enumerates ord Set.univ ∧
      Alg7Out w S (1 / 20) (alg5 (restrictBelow w S) Finset.univ (alg5 (restrictBelow w S)
        Finset.univ (ord.foldl (fun e uv => pivotStep w p uv e) (initTable w S p)))) d₁₀ ∧
      Line11Out S (1 / 20) d₁₀ d₁₁ ∧
      RelFold (Line12Iter (1 / 20) w p) (List.range (Nat.clog 2 (n * Wmax) + 1)) d₁₁ d₂₇ ∧
      dOut = alg5 (restrictBelow w S) Finset.univ (alg5 (restrictBelow w S) Finset.univ d₂₇)

end MultStretchAPASP.Weighted


