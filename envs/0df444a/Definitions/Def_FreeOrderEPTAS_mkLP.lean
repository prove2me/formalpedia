-- Prove2me | Definitions.Def_FreeOrderEPTAS_mkLP
-- name    : FreeOrderEPTAS_mkLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:07.535763+00:00
-- url     : https://prove2.me/theorems/556a37f6-c882-467a-8712-e33490469eb7
-- title:
--   The (LP) of an instance and a guess
-- statement:
--   The program (LP) of a Santa Claus instance for the classes given by $(\epsilon,\delta)$, the parameter $\xi$, and guesses $N^\downarrow,N^\uparrow,S^\downarrow$. A triple is constrained by (S4) exactly when $d\in A_i$ and $\mathcal T^{(t)}_{id}=0$.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.4, p.11

import Mathlib
import Definitions.Def_FreeOrderEPTAS_LPData
import Definitions.Def_FreeOrderEPTAS_typeList

namespace FreeOrderEPTAS

variable {m D n : ℕ}

/-- The program (LP) of p.11 (arXiv:2007.13121v3) for a Santa Claus instance, the classes given by
`(ϵ, δ)`, the parameter `ξ`, and the guesses `N↓`, `N↑`, `S↓`. -/
noncomputable def mkLP (I : SCInstance m D n) (ϵ δ ξ : ℝ)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ) : LPData where
  m := m
  D := D
  n := n
  T := numTypes I ϵ δ
  ρ := rho I ϵ δ
  ℓ := I.ℓ
  small i d t := decide (d ∈ I.A i ∧ typeOf I ϵ δ t i d = 0)
  Nlo := Nlo
  Nhi := Nhi
  Slo := Slo
  ξ := ξ

end FreeOrderEPTAS


