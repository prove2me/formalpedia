-- Prove2me | Definitions.Def_DetComplexityPowerSum_Quadratic_ProxySystem
-- name    : DetComplexityPowerSum_Quadratic_ProxySystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:54.086352+00:00
-- url     : https://prove2.me/theorems/f120ae32-0a5d-48fd-a1fc-c11a44de5aec
-- title:
--   Definition 3.7 — the proxy system $T$
-- statement:
--   Let $g,h\in\mathbb C^m$. The set $T\subseteq\mathbb C^n\times\mathbb C^m\times\mathbb C^m$ consists of all $(a,b,c)$ satisfying the six groups of equations
--
--   1. $b^TM(a)=0$,
--   2. $M(a)c=0$,
--   3. $b^TM_ic=b^TM_{n-1}c$ for every $i\le n-2$,
--   4. $a_{n-1}=1$,
--   5. $g^Tb=1$,
--   6. $h^Tc=1$.
--
--   This is a system of $2m+n+1$ equations in $2m+n$ variables, in which the first-order partial derivatives of $F$ appear as bilinear forms in kernel vectors. The relations $F(a)=0$ and $\operatorname{rank}M(a)=m-1$ are not part of the system: they are consequences, proved in Claim 3.8.
--
--   **Formalization Note** The definition accepts any $g,h$; the theorems about $T$ assume the admissibility property of Claim 3.6. A point is a nested pair `(a, b, c)`.
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 7, Definition 3.7

import Mathlib
import Definitions.Def_DetComplexityPowerSum_Quadratic_KernelNormalizers

namespace DetComplexityPowerSum.Quadratic

open Matrix

/-- The six equation groups of Definition 3.7 at the assignment `x = a`, `u = b`, `v = c`:
`bᵀM(a) = 0`, `M(a)c = 0`, `bᵀMᵢc = bᵀM_{n-1}c` for every `i ≤ n - 2`, `a_{n-1} = 1`, `gᵀb = 1`
and `hᵀc = 1`. -/
def IsProxySolution {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (g h : Fin m → ℂ)
    (a : Fin n → ℂ) (b c : Fin m → ℂ) : Prop :=
  b ᵥ* pencil M₀ M a = 0 ∧
  pencil M₀ M a *ᵥ c = 0 ∧
  (∀ i j : Fin n, IsEarly i → IsPenultimate j → b ⬝ᵥ (M i *ᵥ c) = b ⬝ᵥ (M j *ᵥ c)) ∧
  (∀ j : Fin n, IsPenultimate j → a j = 1) ∧
  g ⬝ᵥ b = 1 ∧
  h ⬝ᵥ c = 1

/-- Definition 3.7: the set `T ⊆ ℂⁿ × ℂᵐ × ℂᵐ` of all solutions `(a, b, c)` of the system. -/
def proxySystem {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (g h : Fin m → ℂ) :
    Set ((Fin n → ℂ) × (Fin m → ℂ) × (Fin m → ℂ)) :=
  {p | IsProxySolution M₀ M g h p.1 p.2.1 p.2.2}

end DetComplexityPowerSum.Quadratic


