-- Prove2me | Definitions.Def_RandPurIso_Completion_projM0
-- name    : RandPurIso_Completion_projM0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:20.782746+00:00
-- url     : https://prove2.me/theorems/ced9b035-4e3c-4986-8b21-2bc41e753ced
-- title:
--   $\Pi_{M_0}$, $\Pi_{M_1}$ and $\Pi^U_{M_b}$ (Definition 5.1)
-- statement:
--   For $1\le N<M$, identify $[N]$ with its inclusion in $[M]$, $M_0=[N]$, $M_1=[M]\setminus M_0$. $\Pi_{M_0}$ is the projector onto $\mathcal H(M_0)$, $\Pi_{M_1}=I-\Pi_{M_0}$, and for a unitary $U$ on $\mathcal H([M])$, $\Pi^U_{M_b}=U\Pi_{M_b}U^\dagger$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 5.1, p. 28

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **`Π_{M0}`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 5.1, p. 28): the projector onto `H(M0)`, `M0 = [N] ⊆ [M]`. -/
def projM0 (N M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal fun x => if x.val < N then 1 else 0

/-- **`Π_{M1} = I − Π_{M0}`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 5.1, p. 28), `M1 = [M] ∖ M0`. -/
def projM1 (N M : ℕ) : Matrix (Fin M) (Fin M) ℂ := 1 - projM0 N M

/-- **Basis-shifted projector** `Π^U = U Π U†` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 5.1, p. 28). -/
def rotProj {M : ℕ} (D : Matrix.unitaryGroup (Fin M) ℂ) (P : Matrix (Fin M) (Fin M) ℂ) :
    Matrix (Fin M) (Fin M) ℂ := (D : Matrix (Fin M) (Fin M) ℂ) * P * (D : Matrix (Fin M) (Fin M) ℂ)ᴴ

end RandPurIso.Completion


