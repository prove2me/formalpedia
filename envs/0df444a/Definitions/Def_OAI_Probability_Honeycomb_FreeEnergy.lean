-- Prove2me | Definitions.Def_OAI_Probability_Honeycomb_FreeEnergy
-- name    : OAI_Probability_Honeycomb_FreeEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:29:49.119442+00:00
-- url     : https://prove2.me/theorems/85e1224a-beb4-4099-afb3-02ccf5d399f9
-- title:
--   Honeycomb adjacency, self-avoiding-walk Green function, lattice translations and zigzag rays for the forced free energy
-- statement:
--   Throughout, the honeycomb lattice has vertex set $\mathbb{Z}\times\mathbb{Z}\times\{\uparrow,\downarrow\}$. A vertex $(i,j,\uparrow)$ ("up") or $(i,j,\downarrow)$ ("down") sits at the centroid of an upward or downward triangle of the unit triangular lattice $\mathbb{Z}+\omega\mathbb{Z}$, $\omega=e^{\mathrm{i}\pi/3}$, namely at
--
--   $$
--   x_{(i,j,\uparrow)}=i+\tfrac{j}{2}+\tfrac12+\mathrm{i}\,\tfrac{\sqrt3}{2}\bigl(j+\tfrac13\bigr),\qquad x_{(i,j,\downarrow)}=i+\tfrac{j}{2}+1+\mathrm{i}\,\tfrac{\sqrt3}{2}\bigl(j+\tfrac23\bigr)\in\mathbb{C}.
--   $$
--
--   The underlying base definitions also provide the constant $\rho=1/\sqrt{2+\sqrt2}$; the finite set $\mathrm{SAW}_n(o)$ of $n$-step self-avoiding walks from a vertex $o$, i.e. sequences $\gamma=(\gamma_0,\dots,\gamma_n)$ of pairwise distinct vertices with $\gamma_0=o$ and consecutive vertices adjacent, with endpoint $\operatorname{end}(\gamma)=\gamma_n$; the pairing $\langle e,w\rangle=\operatorname{Re}(\bar e\,w)$ for $e,w\in\mathbb{C}$; and, for a direction $e\in\mathbb{C}$ and a force $s\in\mathbb{R}$, the tilted partition function
--
--   $$
--   Z_n(o;e,s)=\sum_{\gamma\in\mathrm{SAW}_n(o)}\rho^{n}\exp\bigl(s\,\langle e,\,x_{\operatorname{end}(\gamma)}-x_o\rangle\bigr).
--   $$
--
--   This file introduces the following objects.
--
--   1. **Adjacency.** An up vertex $v=(i,j,\uparrow)$ is joined to a down vertex $w$ exactly when $w\in\{(i,j-1,\downarrow),\,(i,j,\downarrow),\,(i-1,j,\downarrow)\}$, and the symmetric relation $v\sim w$ holds when $v$ is joined to $w$ or $w$ is joined to $v$. This is the nearest-neighbour relation of the honeycomb lattice: every vertex has three neighbours, all of the opposite type, at Euclidean distance $1/\sqrt3$.
--
--   2. **Step weight.** For $t\in\mathbb{R}$, $z(t)=\rho\,e^{-t}$.
--
--   3. **Green function.** For vertices $o,y$ and $t\in\mathbb{R}$,
--
--      $$
--      G_t(o,y)=\sum_{n=0}^{\infty}\ \sum_{\substack{\gamma\in\mathrm{SAW}_n(o)\\ \operatorname{end}(\gamma)=y}}z(t)^{n}\ \in[0,\infty],
--      $$
--
--      the generating function of self-avoiding walks from $o$ to $y$ with weight $z(t)$ per step.
--
--   4. **Susceptibility.** $\chi_t(o)=\sum_{y}G_t(o,y)\in[0,\infty]$, the sum running over all vertices $y$.
--
--   5. **Exponential moments of the endpoint.** For $e\in\mathbb{C}$ and $s,t\in\mathbb{R}$, the directional and radial sums
--
--      $$
--      D_t(o;e,s)=\sum_{y}e^{s\langle e,\,x_y-x_o\rangle}\,G_t(o,y),\qquad R_t(o;s)=\sum_{y}e^{s\,|x_y-x_o|}\,G_t(o,y),
--      $$
--
--      both with values in $[0,\infty]$. For $s=0$ both reduce to $\chi_t(o)$.
--
--   6. **Translations.** For $(a,b)\in\mathbb{Z}^2$, $T_{a,b}(i,j,\tau)=(i+a,\,j+b,\,\tau)$. Translations keep the type of a vertex, satisfy $T_{a,b}\circ T_{a',b'}=T_{a'+a,\,b'+b}$ and $T_{0,0}=\mathrm{id}$, and preserve adjacency: $T_{a,b}v\sim T_{a,b}w$ if and only if $v\sim w$.
--
--   7. **Zigzag rays.** The row sequence $(r_k)_{k\in\mathbb{N}}$ is $r_k=(k/2,\,0,\uparrow)$ for even $k$ and $r_k=((k-1)/2,\,0,\downarrow)$ for odd $k$, that is $(0,0,\uparrow),(0,0,\downarrow),(1,0,\uparrow),(1,0,\downarrow),\dots$ along the row $j=0$. The ray from $o=(i_0,j_0,\tau)$ is $\mathrm{ray}_o(k)=T_{i_0,j_0}(r_{k+\delta})$, where $\delta=0$ if $o$ is up and $\delta=1$ if $o$ is down, so that $\mathrm{ray}_o(0)=o$. The ray path of length $n$ is the sequence $(\mathrm{ray}_o(0),\dots,\mathrm{ray}_o(n))$; its endpoint is $\mathrm{ray}_o(n)$.
--
--   8. **Base vertices.** $o_\uparrow=(0,0,\uparrow)$ and $o_\downarrow=(0,0,\downarrow)$.
--
--   9. **Splitting a walk.** For $n\in\mathbb{N}$ and a vertex sequence $\gamma=(\gamma_0,\dots,\gamma_L)$ with $n\le L$, $\mathrm{split}_n(\gamma)=\bigl((\gamma_0,\dots,\gamma_n),\,(\gamma_n,\dots,\gamma_L)\bigr)$: the first $n+1$ vertices and the rest of the walk from $\gamma_n$ on, the two pieces sharing the vertex $\gamma_n$.
--
--   10. **Maximal partition function.** $M_n(e,s)=\max\bigl(Z_n(o_\uparrow;e,s),\,Z_n(o_\downarrow;e,s)\bigr)$. Since $\mathrm{SAW}_0(o)$ consists of the one-vertex walk $(o)$, one has $Z_0(o;e,s)=1$ and $M_0(e,s)=1$.
--
--   11. **Row cost.** $c(e,s)=\bigl|\tfrac12\,s\operatorname{Re}e\bigr|+\bigl|\tfrac13\cdot\tfrac{\sqrt3}{2}\,s\operatorname{Im}e\bigr|$, a cost per step for the exponential tilt along a zigzag ray.
--
--   Items 2 to 5 are the standard generating functions of honeycomb self-avoiding walks with step weight $\rho e^{-t}$ (here $1/\rho=\sqrt{2+\sqrt2}$ is the connective constant of the honeycomb lattice), together with exponential moments of the endpoint displacement; taking values in $[0,\infty]$ lets them be defined whether or not the series converge. Items 6 to 11 are the tools for the existence of the fixed-length free energy $\lim_{n\to\infty}\frac1n\log Z_n(o;e,s)$: translations reduce every starting vertex to one of the two base vertices, zigzag rays provide self-avoiding walks of every length with explicitly known displacement, and the splitting map compares walks of length $n+m$ with pairs of walks of lengths $n$ and $m$, which is what makes $\log M_n$ subadditive.
--
--   **Formalization Note** Vertices are records `Vertex` with fields `col`, `row` and `up : Bool`, positions are given by `position`, and `rowSpacing` is $\sqrt3/2$. The Lean names are `UpDownAdj` and `Adj` (item 1), `z`, `green`, `susceptibility`, `directionalSum`, `radialSum` (items 2 to 5), `shiftVertex a b`, `rowVertex`, `ray`, `rayPath`, `baseVertex`, `splitWalk`, `maxPartition` and `rowCost` (items 6 to 11). Walks are lists of vertices, and `splitWalk n γ` is the pair `(γ.take (n+1), γ.drop n)` packaged as a non-dependent sigma type; for a list with at most $n$ entries the first component is the whole list and the second is empty. The Green function and the derived sums are `tsum`s in the extended nonnegative reals `ℝ≥0∞`, where every series has a sum (possibly $\infty$), and the real weights enter through `ENNReal.ofReal`. The simp lemmas `saws_zero`, `partition_zero`, `directionalSum_zero`, `radialSum_zero`, `shiftVertex_adj`, `shiftVertex_shift`, `shiftVertex_zero`, `ray_zero`, `endpoint_rayPath` and `maxPartition_zero` record the identities stated above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Honeycomb/FreeEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Honeycomb/FreeEnergy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombFreeEnergy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombFreeEnergy

namespace OAI

/-! Forced honeycomb walks and existence of their fixed-length free energy. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

def UpDownAdj (v w : Vertex) : Prop :=
  v.up = true ∧ w.up = false ∧
    ((w.col = v.col ∧ w.row + 1 = v.row) ∨
     (w.col = v.col ∧ w.row = v.row) ∨
     (w.col + 1 = v.col ∧ w.row = v.row))

def Adj (v w : Vertex) : Prop := UpDownAdj v w ∨ UpDownAdj w v

def z (t : ℝ) : ℝ := rho * Real.exp (-t)

def green (o b : Vertex) (t : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑ γ ∈ saws o n,
    if endpoint o γ = b then ENNReal.ofReal (z t ^ n) else 0

def susceptibility (o : Vertex) (t : ℝ) : ℝ≥0∞ :=
  ∑' b : Vertex, green o b t

def directionalSum (o : Vertex) (e : ℂ) (t s : ℝ) : ℝ≥0∞ :=
  ∑' b : Vertex,
    ENNReal.ofReal (Real.exp (s * projection e (position b - position o))) * green o b t

def radialSum (o : Vertex) (t s : ℝ) : ℝ≥0∞ :=
  ∑' b : Vertex, ENNReal.ofReal (Real.exp (s * ‖position b - position o‖)) * green o b t

@[simp] theorem saws_zero (o : Vertex) : saws o 0 = {[o]} := by
  simp [saws, walkLists]

@[simp] theorem partition_zero (o : Vertex) (e : ℂ) (s : ℝ) :
    partition o e s 0 = 1 := by
  simp [partition, endpoint, displacement, projection]

@[simp] theorem directionalSum_zero (o : Vertex) (e : ℂ) (t : ℝ) :
    directionalSum o e t 0 = susceptibility o t := by
  simp [directionalSum, susceptibility]

@[simp] theorem radialSum_zero (o : Vertex) (t : ℝ) :
    radialSum o t 0 = susceptibility o t := by
  simp [radialSum, susceptibility]

def shiftVertex (i j : ℤ) (v : Vertex) : Vertex :=
  ⟨v.col + i, v.row + j, v.up⟩

@[simp] theorem shiftVertex_adj (i j : ℤ) (v w : Vertex) :
    Adj (shiftVertex i j v) (shiftVertex i j w) ↔ Adj v w := by
  simp only [Adj, UpDownAdj, shiftVertex]
  constructor <;> intro h <;> rcases h with ⟨hv, hw, h⟩ | ⟨hw, hv, h⟩
  · left; refine ⟨hv, hw, ?_⟩; omega
  · right; refine ⟨hw, hv, ?_⟩; omega
  · left; refine ⟨hv, hw, ?_⟩; omega
  · right; refine ⟨hw, hv, ?_⟩; omega

def rowVertex (k : ℕ) : Vertex :=
  if k % 2 = 0 then up ((k / 2 : ℕ) : ℤ) 0 else down ((k / 2 : ℕ) : ℤ) 0

def ray (o : Vertex) (k : ℕ) : Vertex :=
  shiftVertex o.col o.row (rowVertex (k + if o.up then 0 else 1))

@[simp] theorem ray_zero (o : Vertex) : ray o 0 = o := by
  rcases o with ⟨i, j, u⟩
  cases u <;> simp [ray, rowVertex, shiftVertex, up, down]

def rayPath (o : Vertex) (n : ℕ) : List Vertex :=
  List.ofFn (fun i : Fin (n+1) => ray o i.val)

@[simp] theorem shiftVertex_shift (i j k l : ℤ) (v : Vertex) :
    shiftVertex i j (shiftVertex k l v) = shiftVertex (k+i) (l+j) v := by
  cases v
  simp [shiftVertex, add_assoc]

@[simp] theorem shiftVertex_zero (v : Vertex) : shiftVertex 0 0 v = v := by
  cases v
  simp [shiftVertex]

def baseVertex (u : Bool) : Vertex := ⟨0, 0, u⟩

def splitWalk (n : ℕ) (γ : List Vertex) : (Σ _ : List Vertex, List Vertex) :=
  ⟨γ.take (n+1), γ.drop n⟩

def maxPartition (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  max (partition (baseVertex true) e s n) (partition (baseVertex false) e s n)

@[simp] theorem maxPartition_zero (e : ℂ) (s : ℝ) : maxPartition e s 0 = 1 := by
  simp [maxPartition]

@[simp] theorem endpoint_rayPath (o : Vertex) (n : ℕ) :
    endpoint o (rayPath o n) = ray o n := by
  have hne : rayPath o n ≠ [] := by simp [rayPath]
  rw [endpoint, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
  simp only [Option.getD_some, rayPath, List.getLast_ofFn, Nat.add_sub_cancel]

def rowCost (e : ℂ) (s : ℝ) : ℝ :=
  |s * e.re / 2| + |s * e.im * rowSpacing / 3|

end HoneycombForce

end

end OAI


