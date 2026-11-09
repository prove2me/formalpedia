-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Instance
-- name    : MultiSpinCounting_Positive_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:15:25.895426+00:00
-- url     : https://prove2.me/theorems/297c0f13-7921-479e-98ed-b50d7ef5f36a
-- title:
--   Positive multi-spin instances, Gibbs marginals and derived sub-instances
-- statement:
--   Let $G$ be a finite simple graph with ordered vertices, $S$ its active vertex set, $q$ the number of spins, $A_{uv}$ a symmetric interaction matrix on each edge, and $h_u$ an external field at each active vertex. Positive instances require strictly positive fields and matrix entries; the two orientations of an edge carry the same matrix. For configurations on $S$ define
--   $$w(\sigma)=\prod_{u\in S}h_u(\sigma(u))\prod_{\{u,v\}\in E(G[S])}A_{uv}(\sigma(u),\sigma(v)),\qquad Z=\sum_\sigma w(\sigma),\qquad \mu(v\leftarrow a)=Z^{-1}\sum_{\sigma(v)=a}w(\sigma).$$
--   Each edge occurs once. The definitions include restriction to an active set, the child instance of Definition 3.1 (earlier neighbors use $a$, later neighbors use $b$, and the queried neighbor is unchanged), single-vertex pinning and the explicit outer-pinning fields. A derived instance is reached only by these operations at active vertices.
--
--   For a positive real matrix, $\Delta_B=\log\eta$ and $c_B=\tanh(\Delta_B/4)$, with the published cross-ratio maximum $\eta$. Self-avoiding walks are injective sequences of adjacent active vertices; $S_0=1$ and $S_\ell$ is the maximum count over starting vertices. The walk-bound predicate is
--   $$\forall\ell\ge0,\quad S_\ell\le K N^\alpha D^\ell.$$
--   These definitions supply the common model for all statements, retaining real data in the marginal identity and rational data in computational claims.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), pp. 1, 3–4, 8, 11, 13, 17, (1.1)–(1.4), Definition 3.1 and §4.2

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

noncomputable section

namespace MultiSpinCounting.Positive

/-- The active set implements the paper's sub-instance (S,h). Unused data are ignored.
An edge is stored in both orientations; IsPositive imposes both symmetries on active edges. -/
structure Instance (n q : ℕ) (R : Type) where
  graph : SimpleGraph (Fin n)
  active : Finset (Fin n)
  interaction : Fin n → Fin n → Fin q → Fin q → R
  field : Fin n → Fin q → R

def neighbors {n q : ℕ} {R : Type} (Φ : Instance n q R) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Φ.active.filter (Φ.graph.Adj v)

def edges {n q : ℕ} {R : Type} (Φ : Instance n q R) : Finset (Fin n × Fin n) := by
  classical
  exact (Φ.active ×ˢ Φ.active).filter (fun e => e.1 < e.2 ∧ Φ.graph.Adj e.1 e.2)

def IsPositive {n q : ℕ} {R : Type} [Zero R] [LT R] (Φ : Instance n q R) : Prop :=
  (∀ u ∈ Φ.active, ∀ a, 0 < Φ.field u a) ∧
  (∀ u ∈ Φ.active, ∀ v ∈ Φ.active, Φ.graph.Adj u v →
    (∀ a b, 0 < Φ.interaction u v a b) ∧
    (∀ a b, Φ.interaction u v a b = Φ.interaction v u a b) ∧
    (∀ a b, Φ.interaction u v a b = Φ.interaction u v b a))

/-- Product over each unordered edge exactly once, on the actual active carrier. -/
def weight {n q : ℕ} {R : Type} [CommMonoid R] (Φ : Instance n q R)
    (σ : {u // u ∈ Φ.active} → Fin q) : R := by
  classical
  exact (∏ u : {u // u ∈ Φ.active}, Φ.field u.val (σ u)) *
    ∏ u : {u // u ∈ Φ.active}, ∏ v : {v // v ∈ Φ.active},
      if u.val < v.val ∧ Φ.graph.Adj u.val v.val then
        Φ.interaction u.val v.val (σ u) (σ v) else 1

def partition {n q : ℕ} {R : Type} [CommSemiring R] (Φ : Instance n q R) : R := by
  classical
  exact ∑ σ : ({u // u ∈ Φ.active} → Fin q), weight Φ σ

/-- The Gibbs probability mass of (1.1), on configurations of the active carrier. -/
def gibbsProbability {n q : ℕ} {R : Type} [Field R] (Φ : Instance n q R)
    (σ : {u // u ∈ Φ.active} → Fin q) : R := weight Φ σ / partition Φ

def marginal {n q : ℕ} {R : Type} [Field R] (Φ : Instance n q R)
    (v : Fin n) (a : Fin q) : R := by
  classical
  exact (∑ σ : ({u // u ∈ Φ.active} → Fin q),
    if h : v ∈ Φ.active then (if σ ⟨v,h⟩ = a then weight Φ σ else 0) else 0) / partition Φ

def realInstance {n q : ℕ} (Φ : Instance n q ℚ) : Instance n q ℝ :=
  ⟨Φ.graph, Φ.active, fun u v a b => (Φ.interaction u v a b : ℝ),
    fun u a => (Φ.field u a : ℝ)⟩

/-- Definition 3.1: the current neighbor i receives no extra factor. -/
def child {n q : ℕ} {R : Type} [Mul R] (Φ : Instance n q R)
    (v i : Fin n) (a b : Fin q) : Instance n q R := by
  classical
  exact { Φ with
    active := Φ.active.erase v
    field := fun u c => if u ∈ neighbors Φ v then
      if u < i then Φ.interaction v u a c * Φ.field u c
      else if i < u then Φ.interaction v u b c * Φ.field u c
      else Φ.field u c
    else Φ.field u c }

/-- Pinning v to a multiplies every surviving neighboring field. -/
def pin {n q : ℕ} {R : Type} [Mul R] (Φ : Instance n q R)
    (v : Fin n) (a : Fin q) : Instance n q R := by
  classical
  exact { Φ with
    active := Φ.active.erase v
    field := fun u c => if u ∈ neighbors Φ v then
      Φ.interaction v u a c * Φ.field u c else Φ.field u c }

def outerPinned {n q : ℕ} {R : Type} [CommMonoid R]
    (Φ : Instance n q R) (σ : Fin n → Fin q) (j : ℕ) : Instance n q R := by
  classical
  exact { Φ with
    active := Φ.active.filter (fun u => j ≤ u.val)
    field := fun u a => Φ.field u a *
      ∏ v ∈ Φ.active.filter (fun v => v.val < j ∧ Φ.graph.Adj v u),
        Φ.interaction v u (σ v) a }

/-- (1.2)-(1.3), with the paper's tanh convention rather than Sinkhorn's algebraic form. -/
def deltaB {q : ℕ} (A : Fin q → Fin q → ℝ) : ℝ :=
  Real.log (CompOT.Sinkhorn.eta A)

def cB {q : ℕ} (A : Fin q → Fin q → ℝ) : ℝ := Real.tanh (deltaB A / 4)

/-- A walk is a sequence of distinct active vertices with adjacent consecutive terms. -/
def sawCount {n q : ℕ} {R : Type} (Φ : Instance n q R) (v : Fin n) (l : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Fin (l+1) → Fin n =>
    f 0 = v ∧ Function.Injective f ∧ (∀ k, f k ∈ Φ.active) ∧
    ∀ k : Fin l, Φ.graph.Adj (f k.castSucc) (f k.succ))).card

def sawMax {n q : ℕ} {R : Type} (Φ : Instance n q R) (l : ℕ) : ℕ :=
  if l = 0 then 1 else Φ.active.sup (fun v => sawCount Φ v l)

def WalkBound {n q : ℕ} {R : Type} (Φ : Instance n q R) (N : ℕ)
    (K α D : ℝ) : Prop := ∀ l : ℕ, (sawMax Φ l : ℝ) ≤ K * (N : ℝ) ^ α * D ^ l

/-- Only the two operations in the source create derived instances; no supplied correctness fields. -/
inductive Derived {n q : ℕ} {R : Type} [Mul R] (Φ : Instance n q R) : Instance n q R → Prop
  | root : Derived Φ Φ
  | pinStep {Ψ : Instance n q R} (h : Derived Φ Ψ) (v : Fin n)
      (hv : v ∈ Ψ.active) (a : Fin q) : Derived Φ (pin Ψ v a)
  | childStep {Ψ : Instance n q R} (h : Derived Φ Ψ) (v i : Fin n)
      (hv : v ∈ Ψ.active) (hi : i ∈ neighbors Ψ v) (a b : Fin q) :
      Derived Φ (child Ψ v i a b)

end MultiSpinCounting.Positive


