-- Prove2me | Definitions.Def_EuclidCVRP_Main_Instance
-- name    : EuclidCVRP_Main_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:00.966053+00:00
-- url     : https://prove2.me/theorems/2af7f6ab-e543-46ce-ad47-bdee5f204cc6
-- title:
--   Euclidean unsplittable CVRP: instances, tours, solutions, cost
-- statement:
--   An **instance** of Euclidean unsplittable CVRP consists of a depot $r\in\mathbb R^2$, $n$ clients with locations $x_1,\dots,x_n\in\mathbb R^2$ (not necessarily distinct; a client may sit at the depot), a capacity $Q$ and integer demands $d(v)$. It is **valid** when $Q\ge 1$ and $0\le d(v)\le Q$ for every client. Distances are Euclidean, $c(u,v)=\|u-v\|_2$.
--
--   A **tour** is the list $T=(v_1,\dots,v_k)$ of the clients it visits in order; its curve is the closed polygon $r\to x_{v_1}\to\dots\to x_{v_k}\to r$ and its cost is
--
--   $$c(T)=c(r,v_1)+\sum_{i=1}^{k-1}c(v_i,v_{i+1})+c(v_k,r),$$
--
--   with $c(T)=0$ for the empty tour. A **feasible solution** is a finite collection $\mathcal T$ of tours in which every client occurs exactly once and every tour satisfies $d(V(T))=\sum_{v\in V(T)}d(v)\le Q$; its cost is $c(\mathcal T)=\sum_{T\in\mathcal T}c(T)$. A solution is **optimal** if no feasible solution is cheaper.
--
--   Writing $|S|$ for the number of nonempty tours of $S$, an instance has **many tours** (threshold $\Gamma$) if every optimal solution has $|S|\ge\Gamma$, and **few tours** if some optimal solution has $|S|\le\Gamma$. With $\mathrm{OPT}$ the optimum with the minimum number of tours, these are $|\mathrm{OPT}|\ge\Gamma$ and $|\mathrm{OPT}|\le\Gamma$. The instance is **$D$-bounded** if $1\le c(r,x_v)\le D$ for every client $v$.
--
--   The file also defines the length of a closed polygonal walk through a list of points (in any metric space), its point set as a union of segments, and **traversal**: a walk traverses a set $C$ when its curve meets $C$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin 2)` with its $\ell^2$ distance (never the sup metric of `ℝ × ℝ`). Empty tours are allowed in a solution; they cost $0$ and are not counted by $|S|$.
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), Abstract and §1, pp. 1–2 (model); §1.3 Preliminaries, p. 6 (c(T), c(𝒯)); p. 3 (|OPT|); §3, p. 13 (instances with many tours); p. 2 (D-bounded instances)

import Mathlib

set_option autoImplicit false

namespace EuclidCVRP.Main

/-!
# Euclidean unsplittable CVRP: instances, tours, solutions, cost

Blauth, Grandoni, Mátravölgyi, Mousavi, Ren, Salavatipour, *Packing Bins in the Euclidean Plane:
An Almost-Optimal Approximation for Unsplittable Capacitated Vehicle Routing*, STOC 2027 submission
#1236 (October 2026), Abstract and §1, pp. 1–2; Preliminaries §1.3, p. 6; |OPT|, p. 3; "instance
with many tours", §3, p. 13; D-bounded instances, p. 2.
-/

/-- The Euclidean plane `ℝ²` with the Euclidean (`ℓ²`) distance. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The consecutive pairs of a closed polygonal walk through the points of `l` in order, including
the closing pair (last point, first point). -/
def closedEdges {X : Type*} (l : List X) : List (X × X) := l.zip (l.rotate 1)

/-- The length of the closed polygonal walk through the points of `l` in order (and back to the first
point); `0` for the empty list and for a single point. -/
noncomputable def closedLen {X : Type*} [MetricSpace X] (l : List X) : ℝ :=
  ((closedEdges l).map (fun e => dist e.1 e.2)).sum

/-- The point set of the closed polygonal curve through the points of `l`: the union of the
straight segments between consecutive points, including the closing segment. -/
def curve (l : List Pt) : Set Pt := ⋃ e ∈ closedEdges l, segment ℝ e.1 e.2

/-- A closed polygonal walk `l` **traverses** a set `C` when its curve meets `C` (p. 7). -/
def Traverses (l : List Pt) (C : Set Pt) : Prop := (curve l ∩ C).Nonempty

/-- **An instance of Euclidean unsplittable CVRP** (Abstract, p. 1): a depot, `n` clients with
locations in the plane (not necessarily distinct), a vehicle capacity `Q` and integer demands. -/
structure Instance where
  /-- number of clients -/
  n : ℕ
  /-- the depot `r` -/
  depot : Pt
  /-- client locations -/
  loc : Fin n → Pt
  /-- the vehicle capacity `Q` -/
  Q : ℕ
  /-- the demands `d(v)` -/
  dem : Fin n → ℕ

namespace Instance

variable (I : Instance)

/-- The instance is well formed: `Q` is a positive integer and `0 ≤ d(v) ≤ Q` for every client. -/
def Valid : Prop := 1 ≤ I.Q ∧ ∀ v, I.dem v ≤ I.Q

/-- The vertices of the closed curve of a tour `T` (the list of the clients it visits, in order):
the depot, then the clients' locations. -/
def tourPts (T : List (Fin I.n)) : List Pt := I.depot :: T.map I.loc

/-- The cost `c(T) = c(r,v₁) + ∑ c(vᵢ,vᵢ₊₁) + c(v_k,r)` of a tour; the empty tour costs `0`. -/
noncomputable def tourCost (T : List (Fin I.n)) : ℝ := closedLen (I.tourPts T)

/-- The total demand `d(S) = ∑_{v ∈ S} d(v)` of a set of clients. -/
def demSet (S : Finset (Fin I.n)) : ℕ := ∑ v ∈ S, I.dem v

/-- The total demand `d(V(T))` of the clients of a tour. -/
def tourDem (T : List (Fin I.n)) : ℕ := I.demSet T.toFinset

/-- A **feasible solution**: a finite collection of tours, each of total demand at most `Q`, in which
every client occurs exactly once (so every client lies on exactly one tour, once). -/
def Feasible (S : List (List (Fin I.n))) : Prop :=
  (∀ T ∈ S, I.tourDem T ≤ I.Q) ∧ ∀ v : Fin I.n, S.flatten.count v = 1

/-- The cost `c(𝒯) = ∑_{T ∈ 𝒯} c(T)` of a collection of tours. -/
noncomputable def cost (S : List (List (Fin I.n))) : ℝ := (S.map I.tourCost).sum

/-- An optimal solution: feasible, and no feasible solution is cheaper. -/
def IsOptimal (S : List (List (Fin I.n))) : Prop :=
  I.Feasible S ∧ ∀ S' : List (List (Fin I.n)), I.Feasible S' → I.cost S ≤ I.cost S'

/-- The number of (nonempty) tours of a solution. -/
def numTours (S : List (List (Fin I.n))) : ℕ := S.countP (fun T => !T.isEmpty)

/-- **Many tours** (§3, p. 13): every optimal solution has at least `Γ` tours, i.e. `|OPT| ≥ Γ` for
the optimum `OPT` with the minimum number of tours. -/
def ManyTours (Γ : ℕ) : Prop := ∀ S, I.IsOptimal S → Γ ≤ I.numTours S

/-- **Few tours** (p. 3): some optimal solution has at most `Γ` tours, i.e. `|OPT| ≤ Γ` for the
optimum `OPT` with the minimum number of tours. -/
def FewTours (Γ : ℕ) : Prop := ∃ S, I.IsOptimal S ∧ I.numTours S ≤ Γ

/-- **D-bounded** (p. 2): every client is at Euclidean distance between `1` and `D` from the depot. -/
def DBounded (D : ℝ) : Prop := ∀ v, 1 ≤ dist I.depot (I.loc v) ∧ dist I.depot (I.loc v) ≤ D

end Instance

end EuclidCVRP.Main


