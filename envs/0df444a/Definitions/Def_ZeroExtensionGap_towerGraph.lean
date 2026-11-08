-- Prove2me | Definitions.Def_ZeroExtensionGap_towerGraph
-- name    : ZeroExtensionGap_towerGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:37.582377+00:00
-- url     : https://prove2.me/theorems/f321f329-1157-420f-b6f0-ac73be490e0f
-- title:
--   Expander towers: stages, projections, clouds, levels, lengths and validity
-- statement:
--   An **expander tower** with base graph $H$ is a sequence $X_t,\dots,X_1$ with $X_t=H$ and $X_i=\widehat{\mathrm{Ext}}(X_{i+1},H)$, a realization being chosen at each step, and $X:=X_1$ is its final graph. Vertices of $X_i$ are tuples $(x_t,\dots,x_i)\in V(H)^{t-i+1}$. The projection $\pi_i:V(X)\to V(X_i)$ drops the trailing coordinates. An **$i$-cloud** is obtained by fixing $(x_t,\dots,x_{i+1})$, and fixing $x_i$ too selects one of its $n$ children.
--
--   Every edge of $X_t$ has **level** $t$; the inter edges introduced in $X_i$ have level $i$; a surviving outer edge inherits the level of its corresponding edge in $X_{i+1}$. A level-$i$ edge has length $\ell_i:=(\log n)^{i/(t+1)}$, and $\sigma_i:=\ell_i\log n$. A **level-$i$ lift** of an edge $\{u,v\}$ of a core of $X_i$ is an edge $\{x,y\}$ of $X$ with $\{\pi_i(x),\pi_i(y)\}=\{u,v\}$.
--
--   A tower is **valid** if $H$ has the properties of Lemma 2 and the tower has the properties of Lemma 7: each $X_i$ is simple and connected with $n^{t-i+1}$ vertices, maximum degree at most $10(t-i+1)$ and girth at least $g:=\lfloor\gamma\log n\rfloor$; each outer matching retains at least $n-\lceil n^{0.99}\rceil$ edges; and $\Gamma(X_i[S])\le1+\kappa_{\mathrm{tow}}/\log n$ for core-sparse $S$.
--
--   **Formalization Note.** The tower is a recursive construction from $H$ and the realizations, not an arbitrary family: `towerGraph H g φ j` is $X_{t-j}$, on the nested product `TowerV n j`, so that $X_i$ is literally the pruned extension of $X_{i+1}$. Levels are computed from the two tuples, since an edge's level is determined by the first coordinate in which its endpoints differ. Clouds are defined by the first $t-i$ coordinates, which also covers $i=t$ (the whole vertex set) and $i=0$ (singletons).
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Definition 3, p.15 (PDF p.17); pp.16–17 (PDF pp.18–19); Lemma 2, p.6 (PDF p.8); Lemma 7, p.16 (PDF p.18); $\tau_0$, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_ZeroExtensionGap_extGraph

open scoped ENNReal

namespace ZeroExtensionGap

/-- The vertex type of the graph at depth `j` of an expander tower. Depth `j` is the paper's stage
`i = t − j`: depth `0` is `X_t = H` with vertices `V(H) = Fin n`, and depth `j + 1` has vertices
`V(depth j) × V(H)`, the tuples `(x_t, …, x_{t-j-1})` of p.15 (PDF p.17) (Chen, Zhu, *Almost Tight
Hardness of Approximation for 0-Extension*, STOC 2027 submission, manuscript sha256 0cdea87b…). -/
@[reducible] def TowerV (n : ℕ) : ℕ → Type
  | 0 => Fin n
  | j + 1 => TowerV n j × Fin n

noncomputable instance towerVFintype (n : ℕ) : ∀ j, Fintype (TowerV n j)
  | 0 => inferInstanceAs (Fintype (Fin n))
  | j + 1 => by
      have := towerVFintype n j
      exact inferInstanceAs (Fintype (TowerV n j × Fin n))

noncomputable instance towerVDecidableEq (n j : ℕ) : DecidableEq (TowerV n j) := Classical.decEq _

/-- The choices of a tower: at each depth, a bijection per unordered vertex pair. Only the values on
edges of the graph at that depth are read. -/
abbrev Realization (n : ℕ) := ∀ j : ℕ, Sym2 (TowerV n j) → Equiv.Perm (Fin n)

/-- The expander tower with base graph `H`, pruning threshold `g` and realizations `φ`. Definition 3,
p.15 (PDF p.17): `X_t = H` and `X_i = Êxt(X_{i+1}, H)`, a realization being chosen at each step.
`towerGraph H g φ j` is the paper's `X_{t-j}`; the sequence `X_t, …, X_1` is the depths
`0, …, t - 1`, and the final graph `X = X_1` is depth `t - 1`.
**Formalization Note.** A tower is a recursive construction from `H` and the realizations, not an
arbitrary family of graphs. Depths `≥ t` exist in Lean and are never read. -/
def towerGraph {n : ℕ} (H : SimpleGraph (Fin n)) (g : ℕ) (φ : Realization n) :
    ∀ j, SimpleGraph (TowerV n j)
  | 0 => H
  | j + 1 => prunedExt (towerGraph H g φ j) H g fun e => φ j e.1

/-- The pruning threshold `g := ⌊γ log n⌋`, p.11 (PDF p.13). -/
noncomputable def gOf (γ : ℝ) (n : ℕ) : ℕ := ⌊γ * Real.log n⌋₊

/-- The tuple `(x_t, …, x_i)` of a vertex at depth `j = t - i`, coordinate `0` being `x_t`. -/
def towerCoords {n : ℕ} : ∀ j, TowerV n j → List (Fin n)
  | 0, a => [a]
  | j + 1, x => towerCoords j x.1 ++ [x.2]

/-- The projection from depth `J` to depth `j ≤ J`, dropping the trailing coordinates. With `J = j+1`
this is `p_i` (the first component), with `J = t - 1` it is `π_{t-j}` (p.16, PDF p.18). -/
def towerProj {n : ℕ} (j : ℕ) : ∀ J, j ≤ J → TowerV n J → TowerV n j
  | 0, h, x => by
      obtain rfl : j = 0 := by omega
      exact x
  | J + 1, h, x =>
      if h' : j = J + 1 then h' ▸ x else towerProj j J (by omega) x.1

/-- `π_i : V(X) → V(X_i)` for `i ≥ 1` (p.16, PDF p.18). `π_1` is the identity. -/
def piProj {n : ℕ} (t i : ℕ) (hi : 1 ≤ i) (x : TowerV n (t - 1)) : TowerV n (t - i) :=
  towerProj (t - i) (t - 1) (by omega) x

/-- The `i`-cloud containing `x` (p.16, PDF p.18): the vertices of `X` whose first `t - i` coordinates
`(x_t, …, x_{i+1})` agree with those of `x`. -/
noncomputable def cloudOf {n : ℕ} (t i : ℕ) (x : TowerV n (t - 1)) : Finset (TowerV n (t - 1)) :=
  Finset.univ.filter fun y => (towerCoords (t - 1) y).take (t - i) = (towerCoords (t - 1) x).take (t - i)

/-- `C` is an `i`-cloud (p.16, PDF p.18). -/
def IsCloud {n : ℕ} (t i : ℕ) (C : Finset (TowerV n (t - 1))) : Prop := ∃ x, C = cloudOf t i x

/-- `C_i`, the collection of `i`-clouds (p.29, PDF p.31). -/
noncomputable def cloudsAt {n : ℕ} (t i : ℕ) : Finset (Finset (TowerV n (t - 1))) :=
  Finset.univ.image (cloudOf t i)

/-- The child of an `i`-cloud `C` indexed by `a ∈ V(H)` (p.16 and p.29, PDF pp.18, 31): the vertices
of `C` whose coordinate `x_i` (position `t - i` of the tuple) is `a`. -/
noncomputable def childOf {n : ℕ} (t i : ℕ) (C : Finset (TowerV n (t - 1))) (a : Fin n) :
    Finset (TowerV n (t - 1)) :=
  C.filter fun x => (towerCoords (t - 1) x)[t - i]? = some a

/-- The level of an edge `{x, y}` at depth `j` (p.16, PDF p.18): every edge of `X_t = H` has level `t`;
for `i = t - (j+1)` the inter edges introduced in `X_i` have level `i`, and each surviving outer edge
inherits the level of its corresponding edge in `X_{i+1}`.
**Formalization Note.** Computed from the two vertex tuples, so it does not depend on the
realization. It is symmetric in `x, y`. -/
noncomputable def edgeLevel {n : ℕ} (t : ℕ) : ∀ j, TowerV n j → TowerV n j → ℕ
  | 0, _, _ => t
  | j + 1, x, y => if x.1 = y.1 then t - (j + 1) else edgeLevel t j x.1 y.1

/-- `ℓ_i := (log n)^{i/(t+1)}` (p.16, PDF p.18). -/
noncomputable def ell (t n i : ℕ) : ℝ := Real.log n ^ ((i : ℝ) / ((t : ℝ) + 1))

/-- `σ_i := ℓ_i log n` (p.16, PDF p.18). -/
noncomputable def sigma (t n i : ℕ) : ℝ := ell t n i * Real.log n

/-- `η := 50/h₀`, Lemma 2, p.6 (PDF p.8). -/
noncomputable def eta (h₀ : ℝ) : ℝ := 50 / h₀

/-- The shortest-path distance `d_{X_i}` at depth `j = t - i`: each level-`i` edge has length `ℓ_i`
(p.16, PDF p.18). -/
noncomputable def towerDist {n : ℕ} (t : ℕ) (H : SimpleGraph (Fin n)) (g : ℕ) (φ : Realization n)
    (j : ℕ) (x y : TowerV n j) : ℝ≥0∞ :=
  wdist (towerGraph H g φ j) (fun a b => ell t n (edgeLevel t j a b)) x y

/-- Core-sparsity at depth `j` (p.16, PDF p.18). `X_t = H` is its sole core, so at depth `0` the set
is core-sparse precisely when `|S| ≤ n^{0.9}`. At depth `j + 1` the cores are indexed by the vertices
of depth `j`. -/
def IsTowerCoreSparse (n : ℕ) : ∀ j, Finset (TowerV n j) → Prop
  | 0, S => (S.card : ℝ) ≤ (n : ℝ) ^ (0.9 : ℝ)
  | _ + 1, S => IsCoreSparse n S

/-- The five properties of the base graph in Lemma 2, p.6 (PDF p.8). -/
structure BaseGraphProps {n : ℕ} (h₀ γ κ : ℝ) (H : SimpleGraph (Fin n)) : Prop where
  maxDegree : MaxDegreeLE H 3
  expansion : EdgeExpansionAtLeast H h₀
  girth : GirthAtLeast H (⌊γ * Real.log n⌋₊ : ℝ)
  diameter : UnweightedDiameterLE H (eta h₀ * Real.log n)
  sparse : ∀ S : Finset (Fin n), (S.card : ℝ) ≤ (n : ℝ) ^ (0.9 : ℝ) →
    fracArb (H.induce (S : Set (Fin n))) ≤ 1 + κ / Real.log n

/-- The constants of Lemma 2, p.6 (PDF p.8): `0 < h₀ ≤ 1`, `κ > 0` and
`0 < γ ≤ 1/(40000 t log(40t))`. They are fixed from `t` before `n`. -/
structure BaseConstants (t : ℕ) (h₀ γ κ : ℝ) : Prop where
  h₀_pos : 0 < h₀
  h₀_le : h₀ ≤ 1
  γ_pos : 0 < γ
  γ_le : γ ≤ 1 / (40000 * (t : ℝ) * Real.log (40 * (t : ℝ)))
  κ_pos : 0 < κ

/-- Clauses 1–3 of Lemma 7, p.16 (PDF p.18), for the tower with base graph `H` and realizations `φ`,
with depth `j = t - i`: `i ∈ [t]` is `j < t`, and `i ∈ [t-1]` is `j + 1 < t` for the step from depth
`j` (`X_{i+1}`) to depth `j + 1` (`X_i`). -/
structure TowerProps {n : ℕ} (t : ℕ) (γ κtow : ℝ) (H : SimpleGraph (Fin n)) (φ : Realization n) :
    Prop where
  connected : ∀ j, j < t → (towerGraph H (gOf γ n) φ j).Connected
  card : ∀ j, j < t → Fintype.card (TowerV n j) = n ^ (j + 1)
  maxDegree : ∀ j, j < t → MaxDegreeLE (towerGraph H (gOf γ n) φ j) (10 * (j + 1))
  girth : ∀ j, j < t → GirthAtLeast (towerGraph H (gOf γ n) φ j) (gOf γ n : ℝ)
  matching : ∀ j, j + 1 < t → ∀ e : (towerGraph H (gOf γ n) φ j).edgeSet,
    (n : ℝ) - (⌈(n : ℝ) ^ (0.99 : ℝ)⌉₊ : ℝ) ≤
      (((outerMatching (towerGraph H (gOf γ n) φ j) (fun e' => φ j e'.1) e).card : ℝ) -
        (deletedCount (towerGraph H (gOf γ n) φ (j + 1))
          (outerMatching (towerGraph H (gOf γ n) φ j) (fun e' => φ j e'.1) e) : ℝ))
  sparse : ∀ j, j < t → ∀ S : Finset (TowerV n j), IsTowerCoreSparse n j S →
    fracArb ((towerGraph H (gOf γ n) φ j).induce (S : Set (TowerV n j))) ≤ 1 + κtow / Real.log n

/-- A valid expander tower (p.17, PDF p.19: "We call an expander tower valid if it satisfies the
properties in Lemma 7"), with a base graph as in Lemma 2 (fixed for the rest of §3, p.11, PDF p.13). -/
structure IsValidTower {n : ℕ} (t : ℕ) (h₀ γ κ κtow : ℝ) (H : SimpleGraph (Fin n))
    (φ : Realization n) : Prop where
  base : BaseGraphProps h₀ γ κ H
  props : TowerProps t γ κtow H φ

/-- `τ₀ := 1/(200 log(20t))`, §5, p.21 (PDF p.23). -/
noncomputable def tau0 (t : ℕ) : ℝ := 1 / (200 * Real.log (20 * (t : ℝ)))

/-- The child `C_u` of the `i`-cloud `C` corresponding to the vertex `u` of its core in `X_i`
(p.16, PDF p.18): the vertices of `C` that `π_i` sends to `u`. -/
noncomputable def cloudChild {n : ℕ} (t i : ℕ) (hi : 1 ≤ i) (C : Finset (TowerV n (t - 1)))
    (u : TowerV n (t - i)) : Finset (TowerV n (t - 1)) :=
  C.filter fun x => piProj t i hi x = u

open Classical in
/-- The level-`i` lifts of `{u, v}` (p.16, PDF p.18): the edges `{x, y}` of the final graph `X` with
`{π_i(x), π_i(y)} = {u, v}`. -/
noncomputable def levelLifts {n : ℕ} (t : ℕ) (H : SimpleGraph (Fin n)) (g : ℕ) (φ : Realization n)
    (i : ℕ) (hi : 1 ≤ i) (u v : TowerV n (t - i)) : Finset (Sym2 (TowerV n (t - 1))) :=
  (edgeFin (towerGraph H g φ (t - 1))).filter fun e =>
    ∃ x y, e = s(x, y) ∧ piProj t i hi x = u ∧ piProj t i hi y = v

/-- `M` is a matching between `C` and `C'`: each edge joins `C` to `C'`, and distinct edges have
disjoint endpoints. -/
def IsMatchingBetween {W : Type*} (M : Finset (Sym2 W)) (C C' : Finset W) : Prop :=
  (∀ e ∈ M, ∃ x ∈ C, ∃ y ∈ C', e = s(x, y)) ∧
    ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ v, v ∈ e → v ∉ e'

end ZeroExtensionGap


