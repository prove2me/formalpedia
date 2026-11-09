-- Prove2me | Definitions.Def_LinearChoresCLS_RightDeriv
-- name    : LinearChoresCLS_RightDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:53.451716+00:00
-- url     : https://prove2.me/theorems/09a48562-a802-444d-9777-87c80424253a
-- title:
--   Right derivatives and feasible coordinate directions
-- statement:
--   A curve $\gamma:\mathbb R\to E$ (with $E=\mathbb R$ or $E=\mathbb R^M$) has **finite right derivative** $D$ at $0$ if
--   $$
--   \lim_{h\downarrow 0}\frac{\gamma(h)-\gamma(0)}{h}=D .
--   $$
--   The right directional derivative $f'(y;w)$ of a function $f$ is the right derivative of $h\mapsto f(y+hw)$, whenever it exists. A coordinate direction $\tilde v\in\{e_i,-e_i\}$ is **feasible** at $x$ if $x+h\tilde v\in[0,1]^n$ for all sufficiently small $h>0$.
--
--   These notions appear in Theorem 2.3, in hypothesis (a)(ii) of Proposition 4.1, in the right-derivative clauses of the error bounds and in Lemma 7.5.
--
--   **Formalization Note** The limit is taken along $h\to0^+$ (`nhdsWithin 0 (Ioi 0)`), coordinatewise for vector-valued curves. Directions are encoded as pairs $(i,s)$, $s=$ `true` for $+e_i$. The box is the public `InCube`.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 2.3, p.7; Definition 2.4, p.7; Proposition 4.1 (a)(ii), p.11; Lemma 7.5, p.38

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics

open Filter Topology

namespace LinearChoresCLS

/-- **Finite right derivative at `0`** of a curve `γ : ℝ → E`: the limit
`lim_{h ↓ 0} (γ(h) − γ(0))/h` exists and equals `D` (arXiv:2611.06589, held version sha256
85d34a9e…, Theorem 2.3, p.7: `Ψ′(p; v) := lim_{h↓0} (Ψ(p + hv) − Ψ(p))/h`, "whenever the right-hand
limit exists"; Proposition 4.1 (a)(ii), p.11; Lemma 7.5, p.38).

**Formalization Note.** The right directional derivative `f′(y; w)` of the paper is
`HasRightDerivAt0 (fun h => f (y + h • w)) D`. For vector-valued curves (`E = M → ℝ`, Lemma 7.5)
the limit is taken in the product topology. -/
def HasRightDerivAt0 {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (γ : ℝ → E) (D : E) : Prop :=
  Tendsto (fun h : ℝ => h⁻¹ • (γ h - γ 0)) (𝓝[>] (0 : ℝ)) (𝓝 D)

/-- The **coordinate direction** `+eᵢ` (`s = true`) or `−eᵢ` (`s = false`) in `ℝⁿ`
(arXiv:2611.06589, Definition 2.4, p.7: `ṽ ∈ {eᵢ, −eᵢ}`). -/
def coordDir {n : ℕ} (i : Fin n) (s : Bool) : Fin n → ℝ :=
  Pi.single i (if s then 1 else -1)

/-- A coordinate direction `ṽ ∈ {eᵢ, −eᵢ}` is **feasible** at `x` if `x + hṽ ∈ [0,1]ⁿ` for all
sufficiently small `h > 0` (arXiv:2611.06589, Definition 2.4, p.7).

**Formalization Note.** "For all sufficiently small `h > 0`" is `∀ᶠ h in 𝓝[>] 0`. The box
`[0,1]ⁿ` is the public `NetworkEquilibriumCLS.LinearNash.InCube`. -/
def FeasibleCoordDir {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (s : Bool) : Prop :=
  ∀ᶠ h in 𝓝[>] (0 : ℝ), NetworkEquilibriumCLS.LinearNash.InCube (x + h • coordDir i s)

end LinearChoresCLS


