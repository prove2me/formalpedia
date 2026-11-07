-- Prove2me | Definitions.Def_StochAutoreg_cotLaw
-- name    : StochAutoreg_cotLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:18.234295+00:00
-- url     : https://prove2.me/theorems/4e9067a5-68c8-418d-b520-e418071f7b15
-- title:
--   Law of a chain-of-thoughts sample
-- statement:
--   The law of one **chain-of-thoughts** sample $(X,Z_1,\dots,Z_M)$: $X\sim P$, and the tokens are generated autoregressively from $g$. Its mass at $(x,z)$ is $P(x)P_g^M(z\mid x)$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.2

import Mathlib
import Definitions.Def_StochAutoreg_trajPMF

namespace StochAutoreg

/-- The law of one **chain-of-thoughts** sample `(X, Z₁, …, Z_M)`, with `X ∼ P` and the tokens generated
autoregressively from `g`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.2.

**Formalization Note.** The mass at `(x, z)` is `P x * trajMass g M x z` (verification file). -/
noncomputable def cotLaw (g : Generator) (M : ℕ) (P : PMF (List Bool)) :
    PMF (List Bool × (Fin M → Bool)) :=
  P.bind fun x => (trajPMF g M x).map fun z => (x, z)

end StochAutoreg


