-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ScenarioTree_anc
-- name    : KallMayerSLP_Multistage_ScenarioTree_anc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:54.593606+00:00
-- url     : https://prove2.me/theorems/f427f622-a4e0-4873-9881-58a8715dc59e
-- title:
--   Ancestor of a node (history $\mathcal H(n)$)
-- statement:
--   For a node $n$ of stage $t$ and a stage $s\le t$, this is the unique ancestor of $n$ in stage $s$: the element $\ell_s$ of the history $\mathcal H(n)=\{\ell_1=1,\dots,\ell_{t}=n\}$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, p.262 (PDF 271)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree

namespace KallMayerSLP.Multistage

/-- The ancestor in stage `s` of a node `n` of stage `t ≥ s`, i.e. the element `ℓ_s` of the history
`ℋ(n) = {ℓ_1 = 1, …, ℓ_{t_n} = n}` of `n` (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 3, p.262, PDF 271). -/
def ScenarioTree.anc {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {s t : ℕ} (h : s ≤ t) (n : 𝒯.Node t) : 𝒯.Node s :=
  Nat.leRec (motive := fun t _ => 𝒯.Node t → 𝒯.Node s) id (fun k _ ih m => ih (𝒯.parent k m)) h n

end KallMayerSLP.Multistage


