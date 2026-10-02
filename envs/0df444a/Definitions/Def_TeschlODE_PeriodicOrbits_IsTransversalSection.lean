-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_IsTransversalSection
-- name    : TeschlODE_PeriodicOrbits_IsTransversalSection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T03:41:53.013374+00:00
-- url     : https://prove2.me/theorems/1e62c8e2-2455-42ea-a912-71cc81fec4f8
-- title:
--   Codimension-one submanifold $\Sigma = \{S = 0\}$ transversal to $f$ (6.23)
-- statement:
--   Let $f$ be a vector field on $M \subseteq \mathbb{R}^n$ and $k \in \mathbb{N}$. A set
--   $$\Sigma = \{x \in U \mid S(x) = 0\}$$
--   is a **submanifold of codimension one transversal to** $f$ if $U \subseteq \mathbb{R}^n$ is open, $S \in C^k(U)$, and for every $x \in \Sigma$: $x \in M$, $\frac{\partial S}{\partial x}(x) \neq 0$, and
--   $$\frac{\partial S}{\partial x}(x)\, f(x) \neq 0 .$$
--
--   Transversal sections are where the Poincaré map lives: the flow crosses $\Sigma$ with nonzero speed in the normal direction.
--
--   **Formalization Note.** $\Sigma$ is not a separate object; theorems carry $U$ and $S$ and write $\Sigma$ as $\{y \mid y \in U \wedge S(y) = 0\}$. The clause $x \in M$ is implicit in the book, which needs $f(x)$ to be defined.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 197, §6.4, Eq. (6.23)

import Mathlib

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §6.4, p. 197, (6.23): `Σ = {x ∈ U | S(x) = 0}` is a submanifold of codimension one
which is transversal to the vector field `f` (defined on the phase space `M`). That is: `U ⊆ ℝⁿ`
is open, `S ∈ Cᵏ(U)`, and for every `x ∈ Σ` one has `x ∈ M` (so that `f(x)` is meaningful),
`∂S/∂x (x) ≠ 0`, and the transversality condition `(∂S/∂x)(x) f(x) ≠ 0`. -/
def IsTransversalSection {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (k : ℕ) (U : Set (Fin n → ℝ)) (S : (Fin n → ℝ) → ℝ) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ k S U ∧
    ∀ x ∈ U, S x = 0 → x ∈ M ∧ fderiv ℝ S x ≠ 0 ∧ fderiv ℝ S x (f x) ≠ 0

end TeschlODE.PeriodicOrbits


