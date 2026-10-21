-- Prove2me | Definitions.Def_BilevelSOC_SecondOrder_Model
-- name    : BilevelSOC_SecondOrder_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:19.658621+00:00
-- url     : https://prove2.me/theorems/2df3761b-67b1-4432-9321-e2117483afd3
-- title:
--   The bilevel model, value function, and second-order variational notions
-- statement:
--   The data are twice continuously differentiable functions $F,f$ and component families $G_i,g_j$ on $\mathbb R^n\times\mathbb R^m$. The lower-level feasible and solution sets are
--   $$K(x)=\{y:g_j(x,y)\le0\ \forall j\},\qquad S(x)=\operatorname*{argmin}_{y\in K(x)}f(x,y).$$
--   The bilevel feasible set is $M=\{(x,y):G_i(x,y)\le0\ \forall i,\ y\in S(x)\}$ and the lower-level value is $\varphi(x)=\inf_{y\in K(x)}f(x,y)$.
--
--   The module also defines one-sided and Hadamard directional derivatives, second-order directional differentiability and epi-regularity, a sequential tangent cone, growth conditions, active constraints, the cones in (5.1), and positivity of the program (5.5). These notions form the shared language for the goal and its milestones.
--
--   **Formalization Note** The value function is extended-real. Directions and derivative values in the mission are real and finite; constraint indices are zero-based.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 1–9, 18–20, (BPP), (1.1), §2.2–§2.4, Definitions 2.3 and 2.6, (3.1), (5.1)

import Mathlib
open scoped Topology

namespace BilevelSOC.SecondOrder
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Y (m : ℕ) := EuclideanSpace ℝ (Fin m)
structure Data (n m p q : ℕ) where
  F : E n × Y m → ℝ
  f : E n × Y m → ℝ
  G : Fin p → E n × Y m → ℝ
  g : Fin q → E n × Y m → ℝ
def Standing {n m p q : ℕ} (D : Data n m p q) : Prop :=
  ContDiff ℝ 2 D.F ∧ ContDiff ℝ 2 D.f ∧
    (∀ i, ContDiff ℝ 2 (D.G i)) ∧ (∀ j, ContDiff ℝ 2 (D.g j))
def lowerFeas {n m p q : ℕ} (D : Data n m p q) (x : E n) : Set (Y m) :=
  {y | ∀ j, D.g j (x, y) ≤ 0}
def solMap {n m p q : ℕ} (D : Data n m p q) (x : E n) : Set (Y m) :=
  {y | y ∈ lowerFeas D x ∧ ∀ y' ∈ lowerFeas D x, D.f (x, y) ≤ D.f (x, y')}
def feasSet {n m p q : ℕ} (D : Data n m p q) : Set (E n × Y m) :=
  {z | (∀ i, D.G i z ≤ 0) ∧ z.2 ∈ solMap D z.1}
noncomputable def valueFn {n m p q : ℕ} (D : Data n m p q) (x : E n) : EReal :=
  ⨅ y ∈ lowerFeas D x, (D.f (x, y) : EReal)
def lowerSet {n m p q : ℕ} (D : Data n m p q) : Set (E n × Y m) :=
  {z | ∀ j, D.g j z ≤ 0}
def actG {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m) : Set (Fin p) :=
  {i | D.G i z = 0}
def actg {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m) : Set (Fin q) :=
  {j | D.g j z = 0}
def HasDirDerivAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x d : V) (v : ℝ) : Prop :=
  Filter.Tendsto (fun t : ℝ => (θ (x + t • d) - θ x) / t)
    (𝓝[>] (0 : ℝ)) (𝓝 v)
def HasHadamardDirDerivAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x d : V) (v : ℝ) : Prop :=
  Filter.Tendsto (fun r : ℝ × V => (θ (x + r.1 • r.2) - θ x) / r.1)
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 v)
def SecondOrderDirDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x : V) (θ' : V → ℝ) (θ'' : V → V → ℝ) : Prop :=
  ∀ d, HasDirDerivAt θ x d (θ' d) ∧
    ∀ w, Filter.Tendsto
      (fun t : ℝ => (θ (x + t • d + (t ^ 2 / 2) • w) - θ x - t * θ' d) /
        (t ^ 2 / 2)) (𝓝[>] (0 : ℝ)) (𝓝 (θ'' d w))
def SecondOrderEpiRegular {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x : V) (θ' : V → ℝ) (θ'' : V → V → ℝ) : Prop :=
  ∀ d (w : ℝ → V),
    Filter.Tendsto (fun t : ℝ => t • w t) (𝓝[>] (0 : ℝ)) (𝓝 0) →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        θ x + t * θ' d + (t ^ 2 / 2) * θ'' d (w t) - ε * t ^ 2 ≤
          θ (x + t • d + (t ^ 2 / 2) • w t)
def tangentCone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : Set V) (x : V) : Set V :=
  {d | ∃ (t : ℕ → ℝ) (dk : ℕ → V),
    (∀ k, 0 < t k) ∧ Filter.Tendsto t Filter.atTop (𝓝 0) ∧
    Filter.Tendsto dk Filter.atTop (𝓝 d) ∧ ∀ k, x + t k • dk k ∈ C}
def GrowthCondition {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (X : Set V) (x : V) (α : ℝ) : Prop :=
  x ∈ X ∧ ∃ U : Set V, U ∈ 𝓝 x ∧ ∃ C : ℝ, 0 < C ∧
    ∀ z ∈ X ∩ U, θ x + C * ‖z - x‖ ^ α ≤ θ z
def maxFn {V ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : ι → V → ℝ) (z : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => θ i z)
def linCone52 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m) : Set (E n × Y m) :=
  {d | ∀ j ∈ actg D z, fderiv ℝ (D.g j) z d ≤ 0}
def ACQ52 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m) : Prop :=
  tangentCone (lowerSet D) z = linCone52 D z
def linConeVF {n m p q : ℕ} (D : Data n m p q)
    (z : E n × Y m) (φ' : E n → ℝ) : Set (E n × Y m) :=
  {d | (∀ i ∈ actG D z, fderiv ℝ (D.G i) z d ≤ 0) ∧
    fderiv ℝ D.f z d - φ' d.1 ≤ 0 ∧
    ∀ j ∈ actg D z, fderiv ℝ (D.g j) z d ≤ 0}
def critConeVF {n m p q : ℕ} (D : Data n m p q)
    (z : E n × Y m) (φ' : E n → ℝ) : Set (E n × Y m) :=
  linConeVF D z φ' ∩ {d | fderiv ℝ D.F z d ≤ 0}
def actGd {n m p q : ℕ} (D : Data n m p q)
    (z d : E n × Y m) : Set (Fin p) :=
  {i | i ∈ actG D z ∧ fderiv ℝ (D.G i) z d = 0}
def actgd {n m p q : ℕ} (D : Data n m p q)
    (z d : E n × Y m) : Set (Fin q) :=
  {j | j ∈ actg D z ∧ fderiv ℝ (D.g j) z d = 0}
def Prog55Pos {n m p q : ℕ} (D : Data n m p q)
    (z : E n × Y m) (φ'' : E n → E n → ℝ) (d : E n × Y m) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ w : E n × Y m,
    c ≤ fderiv ℝ D.F z w + fderiv ℝ (fderiv ℝ D.F) z d d ∨
    (∃ i ∈ actGd D z d,
      c ≤ fderiv ℝ (D.G i) z w + fderiv ℝ (fderiv ℝ (D.G i)) z d d) ∨
    c ≤ fderiv ℝ D.f z w + fderiv ℝ (fderiv ℝ D.f) z d d - φ'' d.1 w.1 ∨
    (∃ j ∈ actgd D z d,
      c ≤ fderiv ℝ (D.g j) z w + fderiv ℝ (fderiv ℝ (D.g j)) z d d)
def psi {n m p q : ℕ} (D : Data n m p q)
    (φr : E n → ℝ) (z₀ : E n × Y m) (z : E n × Y m) : ℝ :=
  Finset.univ.sup' (by simp : (Finset.univ : Finset (Option (Fin p ⊕ Fin q))).Nonempty)
    (fun i => match i with
      | none => max (D.F z - D.F z₀) (D.f z - φr z.1)
      | some (Sum.inl j) => D.G j z
      | some (Sum.inr j) => D.g j z)
end BilevelSOC.SecondOrder


