-- Prove2me | Definitions.Def_Subamenable_EpiDiff_PWLQ
-- name    : Subamenable_EpiDiff_PWLQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:10.165368+00:00
-- url     : https://prove2.me/theorems/e6d0ca51-c95b-4115-bbe1-6ff60e89bff3
-- title:
--   Equation (2.9) — convex piecewise linear-quadratic functions
-- statement:
--   A piecewise linear-quadratic representation consists of finitely many polyhedral convex sets $\Omega_i$, symmetric linear operators $A_i$, vectors $a_i$, and constants $\alpha_i$. Its function has domain $\bigcup_i\Omega_i$ and obeys
--
--   $$\vartheta(y)=\tfrac12\langle A_i y,y\rangle+\langle a_i,y\rangle+\alpha_i\quad(y\in\Omega_i).$$
--
--   The convex PWLQ class adds convexity of the epigraph and excludes $-\infty$ values. The module records the active pieces at a point and their critical tangent directions. It also defines Lipschitz continuity relative to the finite domain, used in the first-order chain rules.
--
--   **Formalization Note** A polyhedral set is a finite intersection of closed half-spaces; zero half-spaces describe the whole space. Convexity is expressed through the epigraph because the functions are extended-real-valued.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, pp. 5–6, 19, (2.9), (2.13), (4.8)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Base

open Filter Topology
open scoped InnerProductSpace

namespace Subamenable.EpiDiff

/-- Data in the representation (2.9), kept separate from the composite model. -/
structure PWLQRep (m : ℕ) where
  s : ℕ
  Omega : Fin s → Set (E m)
  A : Fin s → E m →L[ℝ] E m
  a : Fin s → E m
  alpha : Fin s → ℝ

/-- A closed polyhedral set as a finite intersection of half spaces. -/
def IsPolyhedral {m : ℕ} (C : Set (E m)) : Prop :=
  ∃ k : ℕ, ∃ c : Fin k → E m, ∃ b : Fin k → ℝ,
    C = {y | ∀ j, ⟪c j, y⟫_ℝ ≤ b j}

/-- Equation (2.9), including its domain decomposition. -/
def IsPWLQRep {m : ℕ} (theta : E m → EReal) (R : PWLQRep m) : Prop :=
  (∀ i, IsPolyhedral (R.Omega i)) ∧
  (∀ i, IsSelfAdjoint (R.A i)) ∧
  dom theta = ⋃ i, R.Omega i ∧
  ∀ i y, y ∈ R.Omega i →
    theta y = (((1 / 2 : ℝ) * ⟪R.A i y, y⟫_ℝ +
      ⟪R.a i, y⟫_ℝ + R.alpha i : ℝ) : EReal)

/-- Convexity, proper codomain, and a PWLQ representation. -/
def IsConvexPWLQ {m : ℕ} (theta : E m → EReal) : Prop :=
  (∀ y, theta y ≠ ⊥) ∧
  Convex ℝ {p : E m × ℝ | theta p.1 ≤ (p.2 : EReal)} ∧
  ∃ R : PWLQRep m, IsPWLQRep theta R

/-- The local relative-domain Lipschitz property used in Theorems 3.4 and 3.6. -/
def LipschitzRelativeAt {m : ℕ} (theta : E m → EReal) (ybar : E m)
    (ell : ℝ) : Prop :=
  0 ≤ ell ∧ ∃ U ∈ 𝓝 ybar,
    ∀ y ∈ U, y ∈ dom theta → ∀ z ∈ U, z ∈ dom theta →
      |(theta y).toReal - (theta z).toReal| ≤ ell * ‖y - z‖

/-- Active pieces in (2.13). -/
def activePieces {m : ℕ} (R : PWLQRep m) (ybar : E m) : Set (Fin R.s) :=
  {i | ybar ∈ R.Omega i}

/-- Directions of piece `i` on which the residual subgradient is orthogonal, (4.8). -/
def pieceCritical {m : ℕ} (R : PWLQRep m) (ybar ubar : E m)
    (i : Fin R.s) : Set (E m) :=
  {w | i ∈ activePieces R ybar ∧ w ∈ tangentCone (R.Omega i) ybar ∧
    ⟪ubar - R.A i ybar - R.a i, w⟫_ℝ = 0}

end Subamenable.EpiDiff


