-- Prove2me | Definitions.Def_LockingAccInfo_lockState
-- name    : LockingAccInfo_lockState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:53.088535+00:00
-- url     : https://prove2.me/theorems/6bb2c7bf-22be-4581-8f9c-7dbca7ce1961
-- title:
--   The conditional states $\rho_{E|(X,Y)=(x,y)} = 2^{-m}(\mathrm{id} + (-1)^x\sigma_y)$, Eq. (3)
-- statement:
--   Let $m\ge1$, $\mathcal X=\{0,1\}$ and $\mathcal Y=\{1,2,3\}^m$. For $x\in\mathcal X$ and $y\in\mathcal Y$ the operator
--
--   $$
--   \rho_{E|(X,Y)=(x,y)} := 2^{-m}\bigl(\mathrm{id}_{(\mathbb C^2)^{\otimes m}} + (-1)^x\sigma_y\bigr)
--   $$
--
--   on $(\mathbb C^2)^{\otimes m}$ is the state of the quantum system $E$ conditioned on $X=x$ and $Y=y$. For fixed $y$ the two states are orthogonal projections scaled by $2^{-m}$, onto the $\pm1$ eigenspaces of $\sigma_y$.
--
--   **Formalization Note** $\sigma_y$ is the published Pauli string `QMaxCutSDP.Rounding.pauliString` ($\sigma_0,\dots,\sigma_3=\mathrm{id},X,Y,Z$, the $m$-fold tensor product on $(\mathbb C^2)^{\otimes m}$ indexed by bit strings). $x$ is a `Bool` (`false` $=0$), so $(-1)^x$ is $1$ or $-1$; a letter $j$ of `y : Fin m → Fin 3` stands for the Pauli index $j+1$ (`Fin.succ`), so $\sigma_0$ never occurs. The operator is defined for every $m$ but is a state only for $m\ge1$; every statement using it assumes $1\le m$.
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, Eq. (3), p.2

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
open QMaxCutSDP.Rounding (pauli pauliString)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §III, Eq. (3), p.2: for x ∈ X =
{0, 1} and y ∈ Y = {1, 2, 3}^m,
"ρE|(X,Y)=(x,y) := 2^{−m} (id_{(C2)⊗m} + (−1)^x σy)",
the state of the quantum system E conditioned on X = x and Y = y.

**Formalization Note.** σ_y is the published `QMaxCutSDP.Rounding.pauliString` (Pauli indices
0, 1, 2, 3 = id, X, Y, Z; `(ℂ²)^{⊗m}` indexed by `Fin m → Fin 2`; entrywise tensor product).
X = {0, 1} is `Bool` with `false` = 0 and `true` = 1, so
`(−1)^x` is `1` for `false` and `−1` for `true`. A letter `j : Fin 3` of y stands for the Pauli
index `j + 1 ∈ {1, 2, 3}` (`Fin.succ`), so σ0 = id never occurs in y. The operator is defined for
every `m`; it is a state only for `m ≥ 1` (at `m = 0` it is the scalar 2 or 0), and every
statement using it assumes `1 ≤ m`. -/
noncomputable def lockState {m : ℕ} (x : Bool) (y : Fin m → Fin 3) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  ((2 : ℂ) ^ m)⁻¹ • (1 + (if x then (-1 : ℂ) else 1) • pauliString (fun i => (y i).succ))

end LockingAccInfo


