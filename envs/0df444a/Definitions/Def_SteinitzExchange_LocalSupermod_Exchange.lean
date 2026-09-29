-- Prove2me | Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
-- name    : SteinitzExchange_LocalSupermod_Exchange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:47:12.829734+00:00
-- url     : https://prove2.me/theorems/0875cb3f-4379-40c6-b0db-3446a5e49155
-- title:
--   The exchange property (EXC) of a function on a base set, linear perturbations and argmax
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite and $\omega:B\to\mathbb R$. The function $\omega$ satisfies the **exchange property (EXC)** (is **M-concave**) if for all $x,y\in B$ and $u\in\operatorname{supp}^+(x-y)$ there is $v\in\operatorname{supp}^-(x-y)$ such that $x-\chi_u+\chi_v\in B$, $y+\chi_u-\chi_v\in B$ and
--
--   $$\omega(x)+\omega(y)\le\omega(x-\chi_u+\chi_v)+\omega(y+\chi_u-\chi_v).$$
--
--   For $p\in\mathbb R^V$ the **linear perturbation** is $\omega[p](x)=\omega(x)+\langle p,x\rangle$, and for $g:B\to\mathbb R$ the set of maximizers is
--
--   $$\operatorname{argmax}(g)=\{x\in B\mid g(x)\ge g(y)\ \ \forall y\in B\}.$$
--
--   (EXC) is the quantitative version of the simultaneous exchange axiom for base sets; the concave conjugate of an M-concave function is the object of this mission.
--
--   **Formalization Note.** A function on $B$ is a total function `(V → ℤ) → ℝ` of which only the values on $B$ are used; every statement quantifies over points of $B$. `argmaxB B g` is a `Finset`, a subset of `B`.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 278 (EXC), Eq. (2.4); p. 280, Eq. (2.7); p. 285, Eq. (4.5)

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet

namespace SteinitzExchange.LocalSupermod

/-- The linear perturbation `ω[p](x) = ω(x) + ⟨p, x⟩` (Murota 1996, p. 280, Eq. (2.7)).
A function on `B` is modelled as a total function `(V → ℤ) → ℝ` of which only the values on `B`
are ever used. -/
def perturb {V : Type*} [Fintype V] (ω : (V → ℤ) → ℝ) (p : V → ℝ) : (V → ℤ) → ℝ :=
  fun x => ω x + pairing p (toReal x)

/-- The exchange property (EXC) of `ω : B → ℝ` (Murota 1996, p. 278, Eq. (2.4)): for `x, y ∈ B`
and `u ∈ supp⁺(x − y)` there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B`,
`y + χ_u − χ_v ∈ B` and `ω(x) + ω(y) ≤ ω(x − χ_u + χ_v) + ω(y + χ_u − χ_v)`.
A function satisfying (EXC) is called M-concave. -/
def SatisfiesEXC {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
    ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B ∧
      ω x + ω y ≤ ω (x - chi u + chi v) + ω (y + chi u - chi v)

open Classical in
/-- `argmax(g) = {x ∈ B | g(x) ≥ g(y) ∀ y ∈ B}` (Murota 1996, p. 285, Eq. (4.5)). -/
noncomputable def argmaxB {V : Type*} (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ) :
    Finset (V → ℤ) :=
  B.filter (fun x => ∀ y ∈ B, g y ≤ g x)

end SteinitzExchange.LocalSupermod


