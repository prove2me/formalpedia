-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_omegaNode
-- name    : KallMayerSLP_Multistage_omegaNode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:57.338512+00:00
-- url     : https://prove2.me/theorems/cda102ae-3582-43a5-87a6-ca374b2c0c2f
-- title:
--   The event $\Omega^{(n)}$ of a node
-- statement:
--   The event of a node is defined recursively by $\Omega^{(1)}:=\Omega$ and $\Omega^{(n)}:=\Omega^{(h_n)}\cap\xi_t^{-1}[\Xi^t_n]$ for $n$ of stage $t$ with parent $h_n$. Unrolled along the history of $n$,
--   $$
--   \Omega^{(n)}=\bigcap_{s=2}^{t}\xi_s^{-1}\big[\Xi^s_{\ell_s}\big].
--   $$
--   These events generate the subfiltration $\widehat{\mathcal F}$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, p.261 (PDF 270)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree_anc

namespace KallMayerSLP.Multistage

/-- The event `Ω^(n)` of a node `n` (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3,
p.261, PDF 270): `Ω^(1) := Ω` and `Ω^(n) := Ω^(h_n) ∩ ξ_t^{-1}[Ξ^t_n]`.

**Formalization Note.** The book's recursion, unrolled along the history of `n`:
`Ω^(n) = ⋂_{s=2}^{t_n} ξ_s^{-1}[Ξ^s_{ℓ_s}]`. At the root the intersection is empty, giving `Ω`. -/
def omegaNode {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) {t : ℕ} (n : 𝒯.Node t) : Set Ω :=
  ⋂ s : Set.Icc 2 t, ξ s ⁻¹' 𝒯.cell s (𝒯.anc s.2.2 n)

end KallMayerSLP.Multistage


