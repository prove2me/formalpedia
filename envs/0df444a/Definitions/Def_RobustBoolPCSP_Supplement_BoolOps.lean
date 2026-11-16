-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_BoolOps
-- name    : RobustBoolPCSP_Supplement_BoolOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:21:55.368147+00:00
-- url     : https://prove2.me/theorems/b92006b1-920b-425d-81e9-b04b62b32b9f
-- title:
--   Boolean Plurality $M^\tau_n$, ternary majority, binary minimum and maximum
-- statement:
--   For a Boolean word $x\in\{0,1\}^n$, the **symmetric majority with tie bit** $\tau$ is
--
--   $$M^\tau_n(x)=\begin{cases}1,&\#\{k:x_k=1\}>n/2,\\0,&\#\{k:x_k=1\}<n/2,\\\tau,&\text{otherwise.}\end{cases}$$
--
--   For odd $n$ it does not depend on $\tau$; these are the only symmetric Boolean Plurality operations of arity $n$. The module also defines ternary majority and the binary minimum and maximum.
--
--   These operations appear in Theorems 2.7, 7.8 and 7.16.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §7.2, p.59 (M^τ_n); §7.3, pp.60, 64 (minimum, maximum, ternary majority)

import Mathlib

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

/-- The number of ones (`true` entries) of a Boolean word. -/
def onesCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun k => x k = true)).card

/-- The **symmetric Boolean Plurality (majority) operation** `M^τ_n` of arity `n` with tie bit `τ`.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §7.2, p.59: "For Boolean inputs, let M^τ_n denote symmetric majority with tie bit
τ ∈ {0, 1}. For odd n, the operation is independent of τ." It returns `1` when more than half of the
inputs are `1`, `0` when fewer than half are, and `τ` on a tie (possible only for even `n`). These
are the only symmetric Boolean Plurality operations of arity `n` (the tie rule can only depend on the
input multiset, which is fixed at a tie). -/
def plurB (n : ℕ) (τ : Bool) (x : Fin n → Bool) : Bool :=
  if n < 2 * onesCount x then true else if 2 * onesCount x < n then false else τ

/-- The ternary Boolean **majority** operation (§7.3, p.64, "ternary majority"). -/
def maj3 (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

/-- The binary Boolean **minimum** operation (§7.3, p.64, "minimum"). -/
def minB (x : Fin 2 → Bool) : Bool := x 0 && x 1

/-- The binary Boolean **maximum** operation (§7.3, p.60, "maximum"). -/
def maxB (x : Fin 2 → Bool) : Bool := x 0 || x 1

end RobustBoolPCSP.Supplement


