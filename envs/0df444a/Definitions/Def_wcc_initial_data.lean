-- Prove2me | Definitions.Def_wcc_initial_data
-- name    : wcc_initial_data
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T12:53:30.669141+00:00
-- url     : https://prove2.me/theorems/5ff3dca5-7fe0-4527-b6aa-492dc6392350
-- title:
--   Vacuum initial data on $\mathbb R^3$: constraints and asymptotic flatness
-- statement:
--   This file builds the initial-data side of the vacuum Einstein initial-value problem in a single coordinate chart on $\mathbb R^3$.
--
--   A point is an element of $\mathbb R^3$; the metric $\bar g$ and the second fundamental form $k$ are fields of $3\times3$ real matrices. From the partial derivatives $\partial_a$ (Fréchet derivatives in the coordinate directions, with Lean's junk value $0$ where a function is not differentiable) the file defines the Christoffel symbols, Riemann tensor, Ricci tensor and scalar curvature $R(\bar g)$ of $\bar g$, the covariant derivative $\nabla_a k_{bc}$, the trace $\operatorname{tr}_{\bar g}k=\bar g^{ab}k_{ab}$ and the squared norm $|k|_{\bar g}^2=\bar g^{ac}\bar g^{bd}k_{ab}k_{cd}$.
--
--   The **vacuum constraint equations** are
--   $$R(\bar g)+(\operatorname{tr}_{\bar g}k)^2-|k|_{\bar g}^2=0,\qquad \nabla^a k_{ab}-\nabla_b(\operatorname{tr}_{\bar g}k)=0,$$
--   written pointwise as `HamiltonianConstraint` and `MomentumConstraint`.
--
--   **Asymptotic flatness** is the weighted $C^3$ class: `weightedSize3 k δ F` is the extended nonnegative real $\sum_{n\le k}\sum_{a,b}\sup_x (1+|x|)^{\delta+n}\,|\partial^n F_{ab}(x)|$, which is $\top$ exactly when the decay fails. `IsAFInitialData h k` asserts that $h,k$ are smooth, $h$ is positive definite, $k$ is symmetric, the two constraints hold, and `weightedSize3 3 1 (h−δ)` and `weightedSize3 3 2 k` are finite — i.e. $h-\delta=O(r^{-1})$ and $k=O(r^{-2})$ with matching derivative decay.
--
--   These definitions are the reusable initial-data layer for the mission; every later statement imports them.
--
--   **Formalization Note.** Derivatives use `fderiv`/`iteratedFDeriv` with Lean's total-function junk values; smoothness hypotheses make them agree with the classical derivatives on the data. The weighted size lives in `ENNReal` so that an unbounded supremum is $\top$ rather than a junk real number, and finiteness is the decay condition.
-- source:
--   Christodoulou 1999, On the global initial value problem and the issue of singularities, CQG 16 A23-A35, §1 pp. A23-A24 (initial data set, constraint equations, asymptotic flatness); https://doi.org/10.1088/0264-9381/16/12A/302

import Mathlib

open scoped Matrix
open Set

namespace WeakCosmicCensorship

abbrev Coords3 := Fin 3 → ℝ
abbrev Field3 := Coords3 → Matrix (Fin 3) (Fin 3) ℝ

noncomputable def dir3 (a : Fin 3) : Coords3 := Pi.single a 1
noncomputable def pd3 (a : Fin 3) (f : Coords3 → ℝ) (x : Coords3) : ℝ :=
  fderiv ℝ f x (dir3 a)

def euclidean3 : Field3 := fun _ => 1
noncomputable def ginv3 (h : Field3) (x : Coords3) : Matrix (Fin 3) (Fin 3) ℝ := (h x)⁻¹
noncomputable def gip3 (h : Field3) (x : Coords3) (u v : Coords3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, h x a b * u a * v b

def IsRiemannian3 (h : Field3) : Prop :=
  ∀ x : Coords3, ∀ v : Coords3, v ≠ 0 → 0 < gip3 h x v v

noncomputable def christoffel3 (h : Field3) (a b c : Fin 3) (x : Coords3) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin 3, ginv3 h x a d *
    (pd3 b (fun y => h y d c) x + pd3 c (fun y => h y b d) x - pd3 d (fun y => h y b c) x)

noncomputable def riemann3 (h : Field3) (a b c d : Fin 3) (x : Coords3) : ℝ :=
  pd3 c (christoffel3 h a d b) x - pd3 d (christoffel3 h a c b) x
    + (∑ e : Fin 3, christoffel3 h a c e x * christoffel3 h e d b x)
    - (∑ e : Fin 3, christoffel3 h a d e x * christoffel3 h e c b x)

noncomputable def ricci3 (h : Field3) (b d : Fin 3) (x : Coords3) : ℝ :=
  ∑ a : Fin 3, riemann3 h a b a d x

noncomputable def scalarCurvature3 (h : Field3) (x : Coords3) : ℝ :=
  ∑ b : Fin 3, ∑ d : Fin 3, ginv3 h x b d * ricci3 h b d x

noncomputable def covDeriv3 (h k : Field3) (a b c : Fin 3) (x : Coords3) : ℝ :=
  pd3 a (fun y => k y b c) x
    - ∑ d : Fin 3, christoffel3 h d a b x * k x d c
    - ∑ d : Fin 3, christoffel3 h d a c x * k x b d

noncomputable def tr3 (h k : Field3) (x : Coords3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ginv3 h x a b * k x a b

noncomputable def kNormSq3 (h k : Field3) (x : Coords3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    ginv3 h x a c * ginv3 h x b d * k x a b * k x c d

def HamiltonianConstraint (h k : Field3) : Prop :=
  ∀ x : Coords3, scalarCurvature3 h x + (tr3 h k x) ^ 2 - kNormSq3 h k x = 0

def MomentumConstraint (h k : Field3) : Prop :=
  ∀ x : Coords3, ∀ b : Fin 3,
    (∑ a : Fin 3, ∑ c : Fin 3, ginv3 h x a c * covDeriv3 h k c a b x)
      - pd3 b (fun y => tr3 h k y) x = 0

def IsSymmetric3 (k : Field3) : Prop :=
  ∀ x : Coords3, ∀ a b : Fin 3, k x a b = k x b a

noncomputable def weightedSize3 (k : ℕ) (δ : ℝ) (F : Field3) : ENNReal :=
  ∑ n : Fin (k + 1), ∑ a : Fin 3, ∑ b : Fin 3,
    ⨆ x : Coords3,
      ENNReal.ofReal (Real.rpow (1 + ‖x‖) (δ + ((n : ℕ) : ℝ))) *
        ENNReal.ofReal ‖iteratedFDeriv ℝ (n : ℕ) (fun y => F y a b) x‖

structure IsAFInitialData (h k : Field3) : Prop where
  smooth_h : ∀ a b : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => h x a b)
  smooth_k : ∀ a b : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => k x a b)
  riemannian : IsRiemannian3 h
  symmetric : IsSymmetric3 k
  hamiltonian : HamiltonianConstraint h k
  momentum : MomentumConstraint h k
  decay_h : weightedSize3 3 1 (fun x => h x - euclidean3 x) < ⊤
  decay_k : weightedSize3 3 2 k < ⊤

end WeakCosmicCensorship


