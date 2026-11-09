-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
-- name    : LinearSetReconciliation327_Main_Pinsketch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:45.847331+00:00
-- url     : https://prove2.me/theorems/4062c0c1-af3c-42e3-b37e-beec99909b21
-- title:
--   §2.2 — Pinsketch syndromes and field straight-line programs
-- statement:
--   For a field $F$ of characteristic two and $\iota$ on addresses, $P_a(x)=\sum_{i\in\mathrm{supp}(x)}\iota(i)^a$ and $\mathrm{Pin}_{N,t}(x)=(P_1(x),P_3(x),\dots,P_{2t-1}(x))$. `pinBits` lists a syndrome's $tw$ bits in a fixed basis. A straight-line program adds or multiplies earlier values, counting field operations.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), §2.2 and equation (2), PDF p.10 (printed p.9)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! Pinsketch, §2.2 (PDF p.10). -/

/-- `P_a(x) = ∑_{i∈supp(x)} ι(i)^a` over a binary vector, §2.2 (PDF p.10). -/
def pinPower {F : Type} [Field F] [Algebra (ZMod 2) F] {N : ℕ} (ι : ℕ → F) (a : ℕ)
    (x : Fin N → ZMod 2) : F :=
  ∑ i : Fin N, x i • ι i.val ^ a

/-- `Pin_{N,t}(x) = (P_{2j-1}(x))_{j=1}^t`, equation (2), with the source's `j` written as `j + 1`. -/
def pin {F : Type} [Field F] [Algebra (ZMod 2) F] {N : ℕ} (ι : ℕ → F) (t : ℕ)
    (x : Fin N → ZMod 2) : Fin t → F :=
  fun j => pinPower ι (2 * j.val + 1) x

/-- The bits of a syndrome in the fixed basis: word `j`, bit `k` is bit `jw + k`. -/
def pinBits {F : Type} [Field F] [Algebra (ZMod 2) F] {w t : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (s : Fin t → F) : Fin (t * w) → ZMod 2 :=
  fun p => b.repr (s (finProdFinEquiv.symm p).1) (finProdFinEquiv.symm p).2

/-- A straight-line program of field operations: each operation adds or multiplies two earlier
values (`true` multiplies); inputs are the initial values. -/
def slpEval {F : Type} [Field F] (inputs : List F) (ops : List (Bool × ℕ × ℕ)) : List F :=
  ops.foldl (fun vals o =>
    vals ++ [if o.1 then vals.getD o.2.1 0 * vals.getD o.2.2 0
             else vals.getD o.2.1 0 + vals.getD o.2.2 0]) inputs

end LinearSetReconciliation327.Main


