-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_nodeProb
-- name    : KallMayerSLP_Multistage_nodeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:57.459847+00:00
-- url     : https://prove2.me/theorems/e0a78588-8694-4e44-a6f9-172e871164a1
-- title:
--   Node probability $p_n$ of (3.13)
-- statement:
--   For a node $n$ of stage $t$ with history $\{\ell_1,\dots,\ell_t=n\}$,
--   $$
--   p_n=\prod_{\nu=2}^{t}\mathbb P_{\xi_\nu}\big(\Xi^\nu_{\ell_\nu}\big).
--   $$
--   The root has $p_1=1$, an empty product.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.13), p.262 (PDF 271)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree_anc

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The node probability `p_n = Π_{ν=2}^{t_n} ℙ_{ξ_ν}(Ξ^ν_{ℓ_ν})`, the last line of (3.13) (Kall &
Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (3.13), p.262, PDF 271). The root has
`p_1 = 1`, an empty product.

**Formalization Note.** `ℙ_{ξ_ν}(Ξ^ν_{ℓ_ν})` is written `ℙ(ξ_ν ∈ Ξ^ν_{ℓ_ν})`, in `ℝ`. -/
noncomputable def nodeProb {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    {t : ℕ} (n : 𝒯.Node t) : ℝ :=
  ∏ s : Set.Icc 2 t, P.real (ξ s ⁻¹' 𝒯.cell s (𝒯.anc s.2.2 n))

end KallMayerSLP.Multistage


