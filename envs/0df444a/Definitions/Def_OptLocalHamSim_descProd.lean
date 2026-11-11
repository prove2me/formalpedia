-- Prove2me | Definitions.Def_OptLocalHamSim_descProd
-- name    : OptLocalHamSim_descProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:43.819803+00:00
-- url     : https://prove2.me/theorems/26119300-798b-4043-899a-e3b977e897b9
-- title:
--   Ordered products $V_s\cdots V_{j+1}$ for the telescoping identity (102)
-- statement:
--   For a sequence of square matrices $X_1,X_2,\dots$ the ordered product of $k$ consecutive terms after index $a$ is
--
--   $$
--   X_{a+k}X_{a+k-1}\cdots X_{a+1},
--   $$
--
--   with the latest factor on the left and the empty product equal to $I$. In particular $V_s\cdots V_{j+1}$ and $U_{j-1}\cdots U_1$ in eq. (102) are such products.
--
--   This is notation for the composition of the block circuits in execution order in the proof of Theorem 16.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §5.3, eq. (102), p.36

import Mathlib

namespace OptLocalHamSim

/-- The ordered product `X_{a+k} ⋯ X_{a+1}` of `k` consecutive terms of a sequence of matrices (the
latest on the left), as in eq. (102), p.36 (Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission, held
version, sha256 44a9768a…): `descProd V j (s − j) = V_s ⋯ V_{j+1}` and
`descProd U 0 (j − 1) = U_{j−1} ⋯ U_1`; the empty product is `I`. -/
def descProd {n : Type} [Fintype n] [DecidableEq n] (X : ℕ → Matrix n n ℂ) (a k : ℕ) :
    Matrix n n ℂ :=
  (List.ofFn fun i : Fin k => X (a + i + 1)).reverse.prod

end OptLocalHamSim


