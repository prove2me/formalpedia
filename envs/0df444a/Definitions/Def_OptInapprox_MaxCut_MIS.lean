-- Prove2me | Definitions.Def_OptInapprox_MaxCut_MIS
-- name    : OptInapprox_MaxCut_MIS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:06.102099+00:00
-- url     : https://prove2.me/theorems/40152496-5609-41f3-a33e-55a2533921ba
-- title:
--   Majority Is Stablest theorem, pp. 6, 17 — as a proposition (proved in [45])
-- statement:
--   The statement of the **Majority Is Stablest theorem** (p. 17, also p. 6), proved by Mossel, O'Donnell and Oleszkiewicz [45], packaged as a proposition so that it can be used as a hypothesis:
--
--   Fix $\rho\in[0,1)$. For every $\epsilon>0$ there is $\delta=\delta(\epsilon,\rho)>0$ such that every function $f:\{-1,1\}^n\to[-1,1]$ (for any $n$) with $\mathbf E[f]=0$ and $\mathrm{Inf}_i(f)\le\delta$ for all $i=1,\dots,n$ satisfies
--   $$\mathbb S_\rho(f)\le 1-\tfrac{2}{\pi}\arccos\rho+\epsilon.$$
--
--   Here $\mathbb S_\rho$ is the noise stability (Definition 3) and $\mathrm{Inf}_i$ the influence (Definition 2). The paper does not prove this theorem; it cites it, and the soundness of its MAX-CUT verifier rests on it.
--
--   **Formalization Note.** $\delta$ is chosen before $n$ and $f$, so it depends on $(\epsilon,\rho)$ only. Boundedness of $f$ is `∀ x, |f x| ≤ 1`.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 6, 17, Majority Is Stablest theorem (§4, §7.3)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

namespace OptInapprox.MaxCut

/-- The Majority Is Stablest theorem (pp. 6, 17; proved in [45]), as a proposition: for every
`ρ ∈ [0, 1)` and `ε > 0` there is `δ > 0` such that every `f : {-1,1}ⁿ → [-1,1]` (any `n`) with
`E[f] = 0` and `Inf_i(f) ≤ δ` for all `i` has `S_ρ(f) ≤ 1 - (2/π) arccos ρ + ε`. -/
def MajorityIsStablest : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, |f x| ≤ 1) → cubeE f = 0 →
      (∀ i, influence i f ≤ δ) → noiseStab ρ f ≤ 1 - 2 / Real.pi * Real.arccos ρ + ε

end OptInapprox.MaxCut


