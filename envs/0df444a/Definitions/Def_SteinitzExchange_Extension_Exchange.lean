-- Prove2me | Definitions.Def_SteinitzExchange_Extension_Exchange
-- name    : SteinitzExchange_Extension_Exchange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:40:01.179534+00:00
-- url     : https://prove2.me/theorems/b59c69c7-ff60-4ee4-b1e8-ebc8c7e1dff6
-- title:
--   The exchange property (EXC), its local version (EXC$_{\mathrm{loc}}$), linear perturbation $\omega[p]$ and $\operatorname{argmax}$ on $B$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite and $\omega:B\to\mathbb R$.
--
--   1. **Linear perturbation.** For $p:V\to\mathbb R$, $\omega[p]:B\to\mathbb R$ is $\omega[p](x)=\omega(x)+\langle p,x\rangle$ (Eq. (2.7); written $\omega_p$ in Section 3 and $g[p]$ in Eq. (4.7)).
--   2. **Exchange property (EXC).** For all $x,y\in B$ and $u\in\operatorname{supp}^+(x-y)$ there is $v\in\operatorname{supp}^-(x-y)$ such that $x-\chi_u+\chi_v\in B$, $y+\chi_u-\chi_v\in B$ and
--   $$\omega(x)+\omega(y)\le\omega(x-\chi_u+\chi_v)+\omega(y+\chi_u-\chi_v).\qquad(2.4)$$
--   A function with (EXC) is called **M-concave**.
--   3. **Local exchange property (EXC$_{\mathrm{loc}}$).** For all $x,y\in B$ with $\|x-y\|=\sum_{v\in V}|x(v)-y(v)|=4$ there **exist** $u\in\operatorname{supp}^+(x-y)$ and $v\in\operatorname{supp}^-(x-y)$ with both exchanged points in $B$ and the inequality (3.1), which is (2.4) for this pair.
--   4. **Maximizers.** $\operatorname{argmax}(g)=\{x\in B\mid g(x)\ge g(y)\ \forall y\in B\}$ (Eq. (4.5)).
--
--   Note the different quantifiers: (EXC) is "for every $u$ there is $v$", (EXC$_{\mathrm{loc}}$) is "there are $u$ and $v$", and only for pairs at $\ell_1$-distance $4$.
--
--   **Formalization Note.** A function $\omega:B\to\mathbb R$ is modelled as a total function `(V → ℤ) → ℝ`; every definition evaluates it only at points that are required to lie in $B$, so its values off $B$ never matter. The norm $\|x-y\|$ is the $\ell_1$ norm, written as an explicit sum (Mathlib's norm on `V → ℤ` is the sup norm).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 278, (EXC) Eq. (2.4); p. 280, Eq. (2.7); p. 282, (EXC_loc) Eq. (3.1); p. 285, Eqs. (4.5), (4.7)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet

namespace SteinitzExchange.Extension

/-- The linear perturbation `ω[p](x) = ω(x) + ⟨p, x⟩` (Murota 1996, p. 280, Eq. (2.7); written
`ω_p` in §3 and `g[p]` in Eq. (4.7)). A function on `B` is modelled as a total function
`(V → ℤ) → ℝ` of which only the values on `B` are ever used. -/
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

/-- The local exchange property (EXC_loc) (Murota 1996, p. 282, Eq. (3.1)): for `x, y ∈ B` with
`‖x − y‖ = ∑_v |x(v) − y(v)| = 4` there **exist** `u ∈ supp⁺(x − y)` and `v ∈ supp⁻(x − y)` with
`x − χ_u + χ_v ∈ B`, `y + χ_u − χ_v ∈ B` and
`ω(x) + ω(y) ≤ ω(x − χ_u + χ_v) + ω(y + χ_u − χ_v)`. -/
def SatisfiesEXCLoc {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∑ w, |x w - y w| = 4 →
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧ x - chi u + chi v ∈ B ∧
      y + chi u - chi v ∈ B ∧ ω x + ω y ≤ ω (x - chi u + chi v) + ω (y + chi u - chi v)

open Classical in
/-- `argmax(g) = {x ∈ B | g(x) ≥ g(y) ∀ y ∈ B}` (Murota 1996, p. 285, Eq. (4.5)). -/
noncomputable def argmaxB {V : Type*} (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ) :
    Finset (V → ℤ) :=
  B.filter (fun x => ∀ y ∈ B, g y ≤ g x)

end SteinitzExchange.Extension


