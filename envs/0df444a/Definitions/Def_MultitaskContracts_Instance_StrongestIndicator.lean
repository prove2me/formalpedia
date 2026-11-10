-- Prove2me | Definitions.Def_MultitaskContracts_Instance_StrongestIndicator
-- name    : MultitaskContracts_Instance_StrongestIndicator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:33.242447+00:00
-- url     : https://prove2.me/theorems/70525660-d5e6-480e-8bf2-7d78e51f6472
-- title:
--   Success on all tasks is the strongest indicator of full effort, eq. (3)
-- statement:
--   In an instance, **success on all tasks is the strongest indicator of full effort** if
--   $$P_K(K)\,P_S(Y)\ \ge\ P_K(Y)\,P_S(K)\qquad\text{for every strategy } S \text{ and performance } Y. \tag{3}$$
--   When $P_S(Y)>0$ this says that the likelihood ratio $P_K(Y)/P_S(Y)$ of full effort against $S$ is largest at $Y=K$. It is the third class of the dependence hierarchy and the hypothesis under which all-or-nothing contracts are optimal for Min-Pay.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), eq. (3), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **Success on all tasks is the strongest indicator of full effort** (eq. (3), §2, p.7,
PDF 9): `P_K(K) P_S(Y) ≥ P_K(Y) P_S(K)` for every strategy `S` and performance `Y`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), eq. (3), p.7. -/
def Instance.StrongestIndicator {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K) : Prop :=
  ∀ S Y : Finset K, I.P Finset.univ Y * I.P S Finset.univ ≤ I.P Finset.univ Finset.univ * I.P S Y

end MultitaskContracts


