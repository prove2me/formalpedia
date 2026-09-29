-- Prove2me | Definitions.Def_SteinitzExchange_LocalSupermod_Localization
-- name    : SteinitzExchange_LocalSupermod_Localization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:48:22.281209+00:00
-- url     : https://prove2.me/theorems/13ffc68a-6c41-4c47-8e4c-957adc09884d
-- title:
--   The concave conjugate ω°, its subdifferential, the localization L̂(ω°, p₀) and the concave closure ω̂
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite and nonempty and $\omega:B\to\mathbb R$. The **concave conjugate** of $\omega$ is
--
--   $$\omega^\circ(p)=\min\{\langle p,x\rangle-\omega(x)\mid x\in B\}\qquad(p\in\mathbb R^V),$$
--
--   and the **concave closure** of $\omega$ is $\hat\omega(b)=\inf\{\langle p,b\rangle-\omega^\circ(p)\mid p\in\mathbb R^V\}$. For a function $F:\mathbb R^V\to\mathbb R$ and $p_0\in\mathbb R^V$, the **subdifferential** (in the sense of concave functions) is
--
--   $$\partial F(p_0)=\{b\in\mathbb R^V\mid F(p)-F(p_0)\le\langle p-p_0,b\rangle\ \ \forall p\in\mathbb R^V\},$$
--
--   and the **localization** of $F$ at $p_0$ is the positively homogeneous function
--
--   $$\hat L(F,p_0)(p)=\inf\{\langle p,b\rangle\mid b\in\partial F(p_0)\}.$$
--
--   The paper applies these with $F=\omega^\circ$: $\hat L(\omega^\circ,p_0)$ describes $\omega^\circ$ near $p_0$, and the Local Supermodularity Theorem asks when all these local pieces are "matroidal".
--
--   **Formalization Note.** `concaveConj` is a real infimum over the finite index set $B$ (the minimum for nonempty $B$; junk value $0$ for empty $B$, which no statement uses). `concaveClosure` is a real infimum over $p$; it is used only at points $x\in B$, where the family is bounded below by $\omega(x)$, so it is the paper's value there. `localization` is a real `sInf`; on an empty or unbounded-below set of values it would return $0$, but for $F=\omega^\circ$ with $B$ finite and nonempty $\partial\omega^\circ(p_0)$ is a nonempty polytope, so the infimum is attained (this is a fact proved in the mission, Eq. (5.12), not an assumption). The localization is defined through the subdifferential exactly as in (5.8)–(5.9), not through the formula (5.12).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 284, Eqs. (4.1), (4.2); p. 291, Eqs. (5.6), (5.8), (5.9); p. 292 (localization)

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet

namespace SteinitzExchange.LocalSupermod

/-- The concave conjugate `ω°(p) = min{⟨p, x⟩ − ω(x) | x ∈ B}` of `ω : B → ℝ` for a nonempty
finite `B ⊆ ℤ^V` (Murota 1996, p. 291, Eq. (5.6); p. 284, Eq. (4.1)). For nonempty `B` the
infimum over the finite index set is the minimum; for empty `B` the value is the junk value `0`,
and every statement assumes `B` nonempty. -/
noncomputable def concaveConj {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (p : V → ℝ) : ℝ :=
  ⨅ x : (B : Set (V → ℤ)), (pairing p (toReal (x : V → ℤ)) - ω x)

/-- The concave closure `ω̂(b) = inf{⟨p, b⟩ − ω°(p) | p ∈ ℝ^V}` (Murota 1996, p. 284, Eq. (4.2)).
At a point `b = x` of `B` the family is bounded below by `ω(x)`, so this real infimum is the
paper's value there; it is used only at points of `B`. -/
noncomputable def concaveClosure {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (b : V → ℝ) : ℝ :=
  ⨅ p : V → ℝ, (pairing p b - concaveConj B ω p)

/-- The subdifferential (in the concave sense) of `F : ℝ^V → ℝ` at `p₀`:
`∂F(p₀) = {b ∈ ℝ^V | F(p) − F(p₀) ≤ ⟨p − p₀, b⟩ ∀ p ∈ ℝ^V}` (Murota 1996, p. 291, Eq. (5.8),
with `F = ω°`). -/
def superdiff {V : Type*} [Fintype V] (F : (V → ℝ) → ℝ) (p₀ : V → ℝ) : Set (V → ℝ) :=
  {b | ∀ p : V → ℝ, F p - F p₀ ≤ pairing (p - p₀) b}

/-- The localization `L̂(F, p₀)(p) = inf{⟨p, b⟩ | b ∈ ∂F(p₀)}` of `F` at `p₀` (Murota 1996,
p. 291, Eq. (5.9), with `F = ω°`). This is a real `sInf`: on an empty or unbounded-below set of
values it returns the junk value `0`. For `F = ω°` with `B` finite nonempty, `∂ω°(p₀)` is a
nonempty polytope, so the infimum is attained and this is the paper's value. -/
noncomputable def localization {V : Type*} [Fintype V] (F : (V → ℝ) → ℝ) (p₀ : V → ℝ)
    (p : V → ℝ) : ℝ :=
  sInf ((fun b => pairing p b) '' superdiff F p₀)

end SteinitzExchange.LocalSupermod


