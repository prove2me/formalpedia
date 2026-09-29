-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Exchange
-- name    : SteinitzExchange_Duality_Exchange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:53:52.114856+00:00
-- url     : https://prove2.me/theorems/66ca3244-2e65-47bb-93f7-3927403fdb30
-- title:
--   The exchange property (EXC) (M-concavity) and the linear perturbation $\omega[p]$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite. A function $\omega:B\to\mathbb R$ satisfies the **exchange property (EXC)** if for all $x,y\in B$ and $u\in\operatorname{supp}^+(x-y)$ there exists $v\in\operatorname{supp}^-(x-y)$ such that $x-\chi_u+\chi_v\in B$, $y+\chi_u-\chi_v\in B$ and
--
--   $$\omega(x)+\omega(y)\le\omega(x-\chi_u+\chi_v)+\omega(y+\chi_u-\chi_v).$$
--
--   Such an $\omega$ is called **M-concave**; a function $\zeta$ is **M-convex** when $-\zeta$ satisfies (EXC). For $p\in\mathbb R^V$ the **linear perturbation** of $\omega$ is
--
--   $$\omega[p](x)=\omega(x)+\langle p,x\rangle\qquad(x\in B).$$
--
--   (EXC) is the hypothesis of the duality theorem: it is imposed on $\omega$ and on $-\zeta$.
--
--   **Formalization Note.** A function on $B$ is a total function `(V → ℤ) → ℝ` of which only the values on $B$ are used; every statement quantifies over points of $B$. M-convexity of `ζ` is written `SatisfiesEXC B (fun x => -ζ x)`.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 278, (EXC) Eq. (2.4); p. 280, Eq. (2.7)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet

namespace SteinitzExchange.Duality

/-- The linear perturbation `ω[p](x) = ω(x) + ⟨p, x⟩` (Murota 1996, p. 280, Eq. (2.7)).
A function on `B` is modelled as a total function `(V → ℤ) → ℝ` of which only the values on `B`
are ever used. -/
def perturb {V : Type*} [Fintype V] (ω : (V → ℤ) → ℝ) (p : V → ℝ) : (V → ℤ) → ℝ :=
  fun x => ω x + pairing p (toReal x)

/-- The exchange property (EXC) of `ω : B → ℝ` (Murota 1996, p. 278, Eq. (2.4)): for `x, y ∈ B`
and `u ∈ supp⁺(x − y)` there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B`,
`y + χ_u − χ_v ∈ B` and `ω(x) + ω(y) ≤ ω(x − χ_u + χ_v) + ω(y + χ_u − χ_v)`.
A function satisfying (EXC) is called M-concave; `ζ` is M-convex when `−ζ` satisfies (EXC). -/
def SatisfiesEXC {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
    ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B ∧
      ω x + ω y ≤ ω (x - chi u + chi v) + ω (y + chi u - chi v)

end SteinitzExchange.Duality


