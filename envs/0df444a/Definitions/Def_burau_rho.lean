-- Prove2me | Definitions.Def_burau_rho
-- name    : burau_rho
-- status  : Definition
-- author  : @lt9
-- created : 2026-09-30T23:32:12.677695+00:00
-- url     : https://prove2.me/theorems/40afb52f-732a-40c4-93da-7d24d725fefb
-- title:
--   The Euclidean descent section rho of the reduced braid quotient
-- statement:
--   **The descent section $\rho:\mathrm{SL}(2,\mathbb Z)\to Q$ of the reduced braid quotient.** The
--   definition node records the section of the quotient map
--   $q:B_3\to Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$ built from the Euclidean descent on
--   $2\times2$ integer matrices: the terminal value
--   $$ \mathtt{baseQ}(M)=\begin{cases} \mathrm{liftS}\,\mathrm{liftT}^{M_{11}} & M_{01}=-1,\\ \mathrm{liftS}^3\,\mathrm{liftT}^{-M_{11}} & \text{else,}\end{cases} $$
--   the iterated descent $\mathtt{rhoIter}$ with its budget, and $\rho(M)=\mathtt{rhoIter}(|M_{00}|,M)$. Alongside
--   them it records the reformulations $\mathtt{cfEnd}$ (the terminal matrix reached by the descent) and
--   $\mathtt{cfWord}$ (the `Q`-word accumulated from the quotient list), so that
--   $\rho(M)=\mathtt{baseQ}(\mathtt{cfEnd}(M))\cdot\mathtt{cfWord}(\mathtt{cfList}(M))$. The two rules
--   $\rho(M\cdot T^j)=\rho(M)\,\mathrm{liftT}^j$ and the $S$-rule
--   $\rho(M\cdot S)=\rho(M)\,\mathrm{liftS}$ are the content of the milestone's reduction, and this node makes
--   the section itself reusable by later platform nodes.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

open Matrix

namespace BurauNC

noncomputable def baseQ (M : M2) : Q :=
  if M 0 1 = -1 then liftS * liftT ^ (M 1 1) else liftS ^ 3 * liftT ^ (-(M 1 1))


noncomputable def rhoIter : ℕ → M2 → Q
  | 0, M => baseQ M
  | k + 1, M =>
      if M 0 0 = 0 then baseQ M
      else rhoIter k ((M * Tm (-(M 0 1 / M 0 0))) * Sm) * liftS⁻¹ * liftT ^ (M 0 1 / M 0 0)


noncomputable def rho (M : M2) : Q := rhoIter (M 0 0).natAbs M

noncomputable def cfWord : List ℤ → Q
  | [] => 1
  | e :: l => cfWord l * (liftS⁻¹ * liftT ^ e)


noncomputable def cfEnd : M2 → M2
  | M => if h : M 0 0 = 0 then M else cfEnd ((M * Tm (-(M 0 1 / M 0 0))) * Sm)
termination_by M => (M 0 0).natAbs
decreasing_by exact euclid_decrease M h

end BurauNC


