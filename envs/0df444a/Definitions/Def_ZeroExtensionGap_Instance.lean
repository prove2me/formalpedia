-- Prove2me | Definitions.Def_ZeroExtensionGap_Instance
-- name    : ZeroExtensionGap_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:39.432761+00:00
-- url     : https://prove2.me/theorems/3691a7a7-0b44-4720-a362-af55f911e01a
-- title:
--   0-Extension instances, $\mathrm{OPT}$, the earthmover distance $W_D$ and the relaxation $\mathrm{EM}$
-- statement:
--   An instance $I=(G,w,T,D)$ of **0-Extension** consists of an undirected graph $G=(V,E)$ with edge weights $w:E\to\mathbb R_{\ge0}$, a set $T\subseteq V$ of terminals, and a metric $D$ on $T$. A **retraction** is a map $f:V\to T$ with $f(t)=t$ for every $t\in T$, of cost $\sum_{\{u,v\}\in E}w_{\{u,v\}}D(f(u),f(v))$, and $\mathrm{OPT}(I)$ is the minimum cost of a retraction.
--
--   For distributions $\mu,\nu$ on $T$, the **earthmover distance** is
--
--   $$W_D(\mu,\nu)=\min_{\pi\ge0}\Big\{\sum_{a,b\in T}\pi(a,b)D(a,b):\ \sum_b\pi(a,b)=\mu(a)\ \ \forall a,\ \ \sum_a\pi(a,b)=\nu(b)\ \ \forall b\Big\}.$$
--
--   The **earthmover relaxation** assigns a distribution $\mu_v$ on $T$ to each vertex, with $\mu_a(a)=1$ for every terminal $a$, and
--
--   $$\mathrm{EM}(I)=\min_\mu\sum_{\{u,v\}\in E}w_{\{u,v\}}W_D(\mu_u,\mu_v).$$
--
--   The **integrality gap** of $I$ is the ratio $\mathrm{OPT}(I)/\mathrm{EM}(I)$. These objects are all the goal theorem needs.
--
--   **Formalization Note.** `Instance` is plain data and `Instance.IsValid` is the constraints: nonnegative weights on the edges and all four metric axioms on $T$. `G` is a `SimpleGraph`, since parallel edges can be merged by adding weights and loops cost $D(x,x)=0$, so neither value changes. An undirected edge is summed once, with endpoints `edgeTail`, `edgeHead`, a choice-based ordering that the symmetric data do not see. The minima are written as `sInf`; on the simplex the coupling set is nonempty and compact, so they are attained. When $T=\emptyset\ne V$ the sets are empty and the values are junk $0$, which `0 < EM` excludes.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), §1, pp.1–2 (PDF pp.3–4)

import Mathlib

namespace ZeroExtensionGap

/-- The fixed ordering of the endpoints of an undirected edge: `edgeTail e` is its first endpoint
and `edgeHead e` its second (`s(edgeTail e, edgeHead e) = e`, see `mk_edgeTail_edgeHead`).
**Formalization Note.** A choice-based representative. Every quantity below is symmetric in the two
endpoints whenever the data are (a metric, the earthmover distance of a metric), so the choice does
not matter, and it lets an edge sum be written without a symmetry proof inside a definition. -/
noncomputable def edgeTail {V : Type*} (e : Sym2 V) : V := (Quot.out e).1

/-- The second endpoint of an undirected edge; see `edgeTail`. -/
noncomputable def edgeHead {V : Type*} (e : Sym2 V) : V := (Quot.out e).2

theorem mk_edgeTail_edgeHead {V : Type*} (e : Sym2 V) : s(edgeTail e, edgeHead e) = e :=
  Quot.out_eq e

open Classical in
/-- The edge set of a graph on a finite vertex type, as a `Finset` (each undirected edge once). -/
noncomputable def edgeFin {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeFinset

/-- A transportation plan from `μ` to `ν`, the constraints of the linear program for `W_D`. Chen,
Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript
sha256 0cdea87b…), §1, p.2 (PDF p.4): `π ≥ 0`, `∑_b π(a,b) = μ(a)`, `∑_a π(a,b) = ν(b)`. -/
def IsCoupling {α : Type*} [Fintype α] (π : α → α → ℝ) (μ ν : α → ℝ) : Prop :=
  (∀ a b, 0 ≤ π a b) ∧ (∀ a, ∑ b, π a b = μ a) ∧ (∀ b, ∑ a, π a b = ν b)

/-- The earthmover distance `W_D(μ, ν)` (Chen, Zhu, manuscript sha256 0cdea87b…, §1, p.2 (PDF p.4)):
the minimum of `∑_{a,b} π(a,b) D(a,b)` over couplings of `μ` and `ν`.
**Formalization Note.** The page has a minimum. For `μ, ν` in the simplex the coupling set is
nonempty (the product coupling) and compact, so the infimum is attained and equals it. Off the
simplex the set may be empty and the value is junk `0`; the relaxation below only evaluates it on
the simplex. -/
noncomputable def earthmover {α : Type*} [Fintype α] (D : α → α → ℝ) (μ ν : α → ℝ) : ℝ :=
  sInf {c | ∃ π, IsCoupling π μ ν ∧ c = ∑ a, ∑ b, π a b * D a b}

/-- A 0-Extension instance `I = (G, w, T, D)` (Chen, Zhu, manuscript sha256 0cdea87b…, §1, p.1
(PDF p.3)): a graph on the vertex type `V`, edge weights, a terminal set and a function on the
terminals. The constraints of the page (nonnegative weights, `D` a metric) are the separate predicate
`Instance.IsValid`, so that the instance of §4.1 can be written down as plain data.
**Formalization Note.** `G` is a `SimpleGraph`. The page's graph may have parallel edges and loops,
but merging parallel edges and adding their weights, and dropping loops (which cost `D(x,x) = 0`),
changes neither `OPT` nor `EM`. Weights are read on the edges of `G` only. -/
structure Instance (V : Type*) [Fintype V] where
  /-- The undirected graph `G = (V, E)`. -/
  G : SimpleGraph V
  /-- The edge weights `w`. -/
  w : Sym2 V → ℝ
  /-- The terminal set `T ⊆ V`. -/
  T : Finset V
  /-- The terminal metric `D`, on `T` only. -/
  D : T → T → ℝ

namespace Instance

variable {V : Type*} [Fintype V]

/-- The constraints of §1, p.1 (PDF p.3): `w ≥ 0` on the edges and `D` a metric on `T`, with all four
metric axioms. -/
structure IsValid (I : Instance V) : Prop where
  w_nonneg : ∀ e ∈ edgeFin I.G, 0 ≤ I.w e
  D_self : ∀ a, I.D a a = 0
  D_symm : ∀ a b, I.D a b = I.D b a
  D_triangle : ∀ a b c, I.D a c ≤ I.D a b + I.D b c
  D_pos : ∀ a b, a ≠ b → 0 < I.D a b

/-- A retraction `f : V → T`, with `f(t) = t` for every terminal (§1, p.1, PDF p.3). -/
def IsRetraction (I : Instance V) (f : V → I.T) : Prop := ∀ t : I.T, f t = t

/-- The objective `∑_{{u,v}∈E} w_{u,v} D(f(u), f(v))` of §1, p.1 (PDF p.3); each undirected edge
counts once. -/
noncomputable def cost (I : Instance V) (f : V → I.T) : ℝ :=
  ∑ e ∈ edgeFin I.G, I.w e * I.D (f (edgeTail e)) (f (edgeHead e))

/-- `OPT(I)`, the minimum cost of a retraction (§1, p.1, PDF p.3).
**Formalization Note.** The set of retractions is finite, and nonempty iff `T` is nonempty or `V` is
empty, so the infimum is the page's minimum. With `T = ∅ ≠ V` the set is empty and the value is junk
`0`; such an instance also has `EM = 0`, which the goal theorem excludes. -/
noncomputable def OPT (I : Instance V) : ℝ :=
  sInf {c | ∃ f, I.IsRetraction f ∧ c = I.cost f}

/-- Feasibility in the earthmover relaxation (§1, p.2, PDF p.4): `μ_v ∈ Δ(T)` for every vertex and
`μ_a(a) = 1` for every terminal. -/
def IsFeasibleEM (I : Instance V) (μ : V → I.T → ℝ) : Prop :=
  (∀ v, μ v ∈ stdSimplex ℝ I.T) ∧ ∀ a : I.T, μ a a = 1

/-- The objective `∑_{{u,v}∈E} w_{u,v} W_D(μ_u, μ_v)` of the earthmover relaxation. -/
noncomputable def costEM (I : Instance V) (μ : V → I.T → ℝ) : ℝ :=
  ∑ e ∈ edgeFin I.G, I.w e * earthmover I.D (μ (edgeTail e)) (μ (edgeHead e))

/-- `EM(I)`, the value of the earthmover relaxation (§1, p.2, PDF p.4).
**Formalization Note.** The page's minimum exists on a valid instance with `T ≠ ∅`, since `W_D` is
continuous on the compact product of simplices. With `T = ∅ ≠ V` the feasible set is empty and the
value is junk `0`. The integrality gap is the ratio `OPT I / EM I`, computed on p.32 (PDF p.34);
statements about it keep the hypothesis `0 < EM I`, because `x / 0 = 0` in Lean. -/
noncomputable def EM (I : Instance V) : ℝ :=
  sInf {c | ∃ μ, I.IsFeasibleEM μ ∧ c = I.costEM μ}

end Instance

end ZeroExtensionGap


