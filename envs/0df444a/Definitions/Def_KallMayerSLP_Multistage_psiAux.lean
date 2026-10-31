-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_psiAux
-- name    : KallMayerSLP_Multistage_psiAux
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:18:36.552676+00:00
-- url     : https://prove2.me/theorems/06465553-822d-4532-b1ca-8c65dbd0949f
-- title:
--   Backward recursion behind $\Psi_t$
-- statement:
--   This auxiliary function runs the recursion (3.17) on the tree, for a node $h$ of stage $t$ and $k$ remaining stages: with $k=0$ it is $0$, and otherwise it is the sum over the children $\nu$ of $h$ of $\mathbb P_{\xi_{t+1}}(\Xi^{t+1}_\nu)$ times the stage value at $\nu$. It is used through $\Psi$.
--
--   **Formalization Note** The product is in the extended reals, with $0\cdot(-\infty)=0$, so a null cell contributes nothing.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.17), p.264 (PDF 273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_stageMin
import Definitions.Def_KallMayerSLP_Multistage_zetaHat

namespace KallMayerSLP.Multistage

open MeasureTheory

open Classical in
/-- The backward recursion behind `Psi`, for a node `h` of stage `t` and `k` stages remaining
(Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (3.17), p.264, PDF 273):
`psiAux 𝒯 P ξ 0 t h ≡ 0`, and `psiAux 𝒯 P ξ (k+1) t h` sums over the children `ν` of `h` the
probability `ℙ_{ξ_{t+1}}(Ξ^{t+1}_ν)` times the stage value at `ν`. Use it through `Psi`.

**Formalization Note.** The product is in `EReal`, with `0 * (-∞) = 0`, so a null cell contributes
nothing. -/
noncomputable def psiAux {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) :
    (k t : ℕ) → 𝒯.Node t → (∀ τ, Fin (D.n τ) → ℝ) → EReal
  | 0, _, _, _ => 0
  | k + 1, t, h, z =>
    ∑ ν : {ν : 𝒯.Node (t + 1) // 𝒯.parent t ν = h},
      ((P.real (ξ (t + 1) ⁻¹' 𝒯.cell (t + 1) ν) : ℝ) : EReal) *
        stageMin D (t + 1) (D.b (t + 1) (zetaHat 𝒯 P ξ ν.1)) (psiAux 𝒯 P ξ k (t + 1) ν.1) z

end KallMayerSLP.Multistage


