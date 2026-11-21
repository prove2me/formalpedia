-- Prove2me | Definitions.Def_wcc_spacetime
-- name    : wcc_spacetime
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T12:54:00.452385+00:00
-- url     : https://prove2.me/theorems/60181b91-89fa-40ed-afd2-f17d7074acdb
-- title:
--   Developments of vacuum initial data and maximality
-- statement:
--   This file builds the spacetime side of the mission on top of the reused coordinate framework (which supplies Lorentzian metrics, curvature, geodesics and causal curves on open subsets of $\mathbb R^4$).
--
--   Given an embedding $\iota:\mathbb R^3\to\mathbb R^4$ with Jacobian $J^A_a=\partial_a\iota^A$, the **induced metric** is $(\iota^*g)_{ab}=g_{AB}J^A_aJ^B_b$ and, for a unit normal field $n$, the **second fundamental form** is $k_{ab}=-g_{AB}(\partial_aJ^A_b+\Gamma^A_{CD}J^C_aJ^D_b)n^B$ (sign convention $k(X,Y)=-g(n,\nabla_XY)$).
--
--   A time orientation is a continuous timelike vector field $T$; a causal vector $v$ is future-directed when $g(v,T)<0$. `CausalRel q p` means $q=p$ or there is a future-directed causal curve from $q$ to $p$; `causalFuture S` is $J^+(S)$; `futureDomainOfDependence H B` is the future domain of dependence $D^+(B)=\{p\in J^+(H):J^-(p)\cap H\subseteq B\}$ relative to the Cauchy surface $H$. `IsNullGeodesicOn` is a nonconstant null geodesic.
--
--   A **development** of $(h,k)$ (`Development h k`) is a vacuum spacetime $(U,g)$ with time orientation $T$ and a smooth embedding $\iota$ of $\mathbb R^3$ as a Cauchy surface, such that some unit normal $n$ makes the induced metric equal $h$ and the second fundamental form equal $k$. `IsMaximalDevelopment` is the Choquet-Bruhat–Geroch universal property: every other development embeds isometrically into it, preserving the initial surface.
--
--   **Formalization Note.** A development is represented as a globally hyperbolic spacetime with Cauchy surface $\iota(\mathbb R^3)$; the maximal future development of the source is its restriction to $J^+(H)$. The unit normal is bundled existentially. All curves are coordinate curves with `deriv`-based velocities.
-- source:
--   Christodoulou 1999, CQG 16 A23-A35, §1 p. A23-A24 (future development, maximal future development); Choquet-Bruhat & Geroch 1969, CMP 14 329-335, https://doi.org/10.1007/BF01645389

import Mathlib
import Definitions.Def_scc_coordinate_framework
import Definitions.Def_wcc_initial_data

open scoped Matrix
open Set StrongCosmicCensorship

namespace WeakCosmicCensorship

noncomputable def jac34 (ι : Coords3 → Coords) (x : Coords3) : Matrix (Fin 4) (Fin 3) ℝ :=
  Matrix.of fun A a => pd3 a (fun y => ι y A) x

noncomputable def inducedMetric (g : MetricField) (ι : Coords3 → Coords) (x : Coords3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => ∑ A : Fin 4, ∑ B : Fin 4, g (ι x) A B * jac34 ι x A a * jac34 ι x B b

noncomputable def secondFundForm (g : MetricField) (ι : Coords3 → Coords)
    (n : Coords3 → Coords) (x : Coords3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => -∑ A : Fin 4, ∑ B : Fin 4, g (ι x) A B *
    (pd3 a (fun y => jac34 ι y A b) x
      + ∑ C : Fin 4, ∑ D : Fin 4, christoffel g A C D (ι x) * jac34 ι x C a * jac34 ι x D b) * n x B

def IsFutureCausalVec (g : MetricField) (T : Coords → Coords) (x v : Coords) : Prop :=
  IsCausalVec g x v ∧ gip g x v (T x) < 0

def CausalRel (U : Set Coords) (g : MetricField) (T : Coords → Coords) (q p : Coords) : Prop :=
  q ∈ U ∧ p ∈ U ∧ (q = p ∨ ∃ γ : ℝ → Coords,
    (∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ U) ∧
    (∀ τ ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ γ τ) ∧
    (∀ τ ∈ Icc (0 : ℝ) 1, IsFutureCausalVec g T (γ τ) (vel γ τ)) ∧
    γ 0 = q ∧ γ 1 = p)

def causalFuture (U : Set Coords) (g : MetricField) (T : Coords → Coords) (S : Set Coords) :
    Set Coords :=
  {p | ∃ q ∈ S, CausalRel U g T q p}

def futureDomainOfDependence (U : Set Coords) (g : MetricField) (T : Coords → Coords)
    (H B : Set Coords) : Set Coords :=
  {p ∈ causalFuture U g T H | ∀ q ∈ H, CausalRel U g T q p → q ∈ B}

def IsNullGeodesicOn (U : Set Coords) (g : MetricField) (I : Set ℝ) (γ : ℝ → Coords) : Prop :=
  IsGeodesicOn g I γ ∧ (∀ τ ∈ I, γ τ ∈ U) ∧
    (∀ τ ∈ I, gip g (γ τ) (vel γ τ) (vel γ τ) = 0) ∧ (∀ τ ∈ I, vel γ τ ≠ 0)

structure Development (h k : Field3) where
  U : Set Coords
  g : MetricField
  T : Coords → Coords
  ι : Coords3 → Coords
  spacetime : IsSpacetime U g
  vacuum : IsVacuum U g
  timeOrient : ContinuousOn T U ∧ ∀ x ∈ U, IsTimelikeVec g x (T x)
  ι_smooth : ContDiff ℝ (⊤ : ℕ∞) ι
  ι_inj : Function.Injective ι
  ι_immersion : ∀ x : Coords3, ∀ v : Coords3, v ≠ 0 → (jac34 ι x).mulVec v ≠ 0
  ι_maps : ∀ x, ι x ∈ U
  cauchy : IsCauchyHypersurface U g (ι '' univ)
  induced : ∃ n : Coords3 → Coords,
    (∀ x, gip g (ι x) (n x) (n x) = -1) ∧
    (∀ x b, ∑ A : Fin 4, ∑ B : Fin 4, g (ι x) A B * n x A * jac34 ι x B b = 0) ∧
    (∀ x a b, h x a b = inducedMetric g ι x a b) ∧
    (∀ x a b, k x a b = secondFundForm g ι n x a b)

def IsMaximalDevelopment (h k : Field3) (D : Development h k) : Prop :=
  ∀ D' : Development h k, ∃ F : Coords → Coords,
    MapsTo F D'.U D.U ∧ InjOn F D'.U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F D'.U ∧
    (∀ x ∈ D'.U, ∀ v w : Coords,
      gip D'.g x v w = gip D.g (F x) ((jac F x).mulVec v) ((jac F x).mulVec w)) ∧
    (∀ x : Coords3, F (D'.ι x) = D.ι x)

end WeakCosmicCensorship


