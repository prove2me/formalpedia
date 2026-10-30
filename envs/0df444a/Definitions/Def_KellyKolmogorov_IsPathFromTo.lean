-- Prove2me | Definitions.Def_KellyKolmogorov_IsPathFromTo
-- name    : KellyKolmogorov_IsPathFromTo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:23.787514+00:00
-- url     : https://prove2.me/theorems/8ff62218-8683-47bf-8b52-1d06bf71bbdf
-- title:
--   Sequence of states leading from $j$ to $j_0$
-- statement:
--   A finite sequence of states $l=(a_0,a_1,\dots,a_m)$ **leads from $j$ to $j_0$** if it is nonempty, $a_0=j$ and $a_m=j_0$. A one-element sequence leads from $j$ to $j$.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25)

import Mathlib

namespace KellyKolmogorov

/-- **A sequence of states leading from `j` to `j₀`.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22: "a
sequence of states `j, jₙ, jₙ₋₁, …, j₁, j₀` leading from `j` to `j₀`".

`IsPathFromTo l j j₀` says that the list `l` is nonempty, starts at `j` and ends at `j₀`. -/
def IsPathFromTo {𝒮 : Type*} (l : List 𝒮) (j j₀ : 𝒮) : Prop :=
  l.head? = some j ∧ l.getLast? = some j₀

end KellyKolmogorov


