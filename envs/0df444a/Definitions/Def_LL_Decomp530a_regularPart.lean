-- Prove2me | Definitions.Def_LL_Decomp530a_regularPart
-- name    : LL_Decomp530a_regularPart
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-17T15:35:02.509839+00:00
-- url     : https://prove2.me/theorems/c89a422e-c85b-4966-a222-2e6dc37066d7
-- title:
--   Dirichlet L-function with the principal pole removed
-- statement:
--   For $q\ge1$ and a Dirichlet character $\chi$ modulo $q$, the function $R_\chi:\mathbb C\to\mathbb C$ is defined as follows. If $\chi$ is the principal character, let $F(s)$ be the entire extension of $(s-1)L(s,\chi)$, whose value at $s=1$ is the residue $\prod_{p\mid q}(1-p^{-1})$, and set $R_\chi(s)=\big(F(s)-F(1)\big)/(s-1)$ for $s\ne1$ and $R_\chi(1)=F'(1)$. Otherwise $R_\chi(s)=L(s,\chi)$, the entire Dirichlet $L$-function.

import Mathlib

open Classical Complex

namespace LL_Decomp530a
noncomputable def regularPart {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 else χ.LFunction
end LL_Decomp530a


