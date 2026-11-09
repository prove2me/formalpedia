-- Prove2me | Definitions.Def_DetComplexityPowerSum_Quadratic_AmendedProxySystem
-- name    : DetComplexityPowerSum_Quadratic_AmendedProxySystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:36:47.044891+00:00
-- url     : https://prove2.me/theorems/3ff86c10-6215-46b6-85e2-82487fe095a4
-- title:
--   Definition 3.12 — the choices $q,\Gamma$ and the square system $T'$
-- statement:
--   Let $g,h\in\mathbb C^m$ and let $T$ be the proxy system. A pair $(q,\Gamma)$ with $q\in\mathbb C^m$ and $\Gamma\in\mathbb C^{(m-1)\times m}$ is **amendment data** if $b^Tq\ne 0$ for every $b$ for which there exist $a,c$ with $(a,b,c)\in T$, and $\ker\Gamma=\operatorname{span}\{q\}$.
--
--   The set $T'\subseteq\mathbb C^n\times\mathbb C^m\times\mathbb C^m\times\mathbb C$ consists of all $(a,b,c,z)$ satisfying
--
--   1. $b^TM(a)=0$,
--   2. $\Gamma M(a)c=0$,
--   3. $b^TM_ic=b^TM_{n-1}c$ for every $i\le n-2$,
--   4. $a_{n-1}=1$,
--   5. $g^Tb=1$,
--   6. $h^Tc=1$,
--   7. $z\,b^Tq=1$.
--
--   Replacing the $m$ equations $M(a)c=0$ by the $m-1$ equations $\Gamma M(a)c=0$ and adding the variable $z$ with its equation yields $2m+n+1$ equations in $2m+n+1$ variables, the square shape that the multi-homogeneous Bézout theorem requires.
--
--   **Formalization Note** The row index of $\Gamma$ is `Fin (m - 1)`. Every representation of $F_n$ with $n\ge 2$ has $m\ge 1$, so the subtraction is not truncated in any theorem of the mission. Existence of amendment data is a separate theorem item, not a field of the definition.
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 9, Definition 3.12

import Mathlib
import Definitions.Def_DetComplexityPowerSum_Quadratic_ProxySystem

namespace DetComplexityPowerSum.Quadratic

open Matrix

/-- The choices of Definition 3.12: `q ∈ ℂᵐ` with `bᵀq ≠ 0` for every `b` for which some `a, c`
have `(a, b, c) ∈ T`, and an `(m - 1) × m` matrix `Γ` with `ker Γ = span {q}`. -/
def IsAmendmentData {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (g h q : Fin m → ℂ)
    (Γ : Matrix (Fin (m - 1)) (Fin m) ℂ) : Prop :=
  (∀ (a : Fin n → ℂ) (b c : Fin m → ℂ), (a, b, c) ∈ proxySystem M₀ M g h → b ⬝ᵥ q ≠ 0) ∧
  LinearMap.ker Γ.mulVecLin = Submodule.span ℂ {q}

/-- The equations of Definition 3.12 at `x = a`, `u = b`, `v = c`, `z`: those of Definition 3.7,
with the group `M(a)c = 0` replaced by `ΓM(a)c = 0`, together with `z bᵀq = 1`. -/
def IsAmendedSolution {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (g h q : Fin m → ℂ)
    (Γ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (a : Fin n → ℂ) (b c : Fin m → ℂ) (z : ℂ) : Prop :=
  b ᵥ* pencil M₀ M a = 0 ∧
  Γ *ᵥ (pencil M₀ M a *ᵥ c) = 0 ∧
  (∀ i j : Fin n, IsEarly i → IsPenultimate j → b ⬝ᵥ (M i *ᵥ c) = b ⬝ᵥ (M j *ᵥ c)) ∧
  (∀ j : Fin n, IsPenultimate j → a j = 1) ∧
  g ⬝ᵥ b = 1 ∧
  h ⬝ᵥ c = 1 ∧
  z * (b ⬝ᵥ q) = 1

/-- Definition 3.12: the set `T′ ⊆ ℂⁿ × ℂᵐ × ℂᵐ × ℂ` of all solutions `(a, b, c, z)`. -/
def amendedProxySystem {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (g h q : Fin m → ℂ)
    (Γ : Matrix (Fin (m - 1)) (Fin m) ℂ) :
    Set ((Fin n → ℂ) × (Fin m → ℂ) × (Fin m → ℂ) × ℂ) :=
  {p | IsAmendedSolution M₀ M g h q Γ p.1 p.2.1 p.2.2.1 p.2.2.2}

end DetComplexityPowerSum.Quadratic


