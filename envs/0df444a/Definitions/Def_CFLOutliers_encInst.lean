-- Prove2me | Definitions.Def_CFLOutliers_encInst
-- name    : CFLOutliers_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:27.684741+00:00
-- url     : https://prove2.me/theorems/d3948ca4-ff8f-458b-a37f-e12e00058c64
-- title:
--   Binary encodings of instances, of the inputs of Theorem 1.1 and Lemma 2.2, and of solutions
-- statement:
--   All words are over the four symbols $\{0,1,2,3\}$: $0,1$ are bits, $2$ separates the numerator and denominator of a rational, and $3$ ends each word. Natural numbers are written in binary, rationals as a signed binary numerator, $2$, and a binary denominator (the published encoders `encNat`, `encRat`).
--
--   1. An **instance** is encoded as the words $m,n,q,|f|$, then the $f_i$, then $|u|$ and the $u_i$, then $|c|$ and the matrix entries.
--   2. The **input of Theorem 1.1** is the instance followed by the accuracy $\varepsilon\in\mathbb Q$.
--   3. A **solution** is encoded by one bit per facility (open or not), then for each client the number $0$ if rejected and $i+1$ if served by facility $i$.
--   4. The **input of Lemma 2.2** is the instance, $S^-$, $S^+$ and the rational bound $M$.
--
--   No number is written in unary, so the input length is the binary input length of the paper. Each encoder is injective.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Theorem 1.1, p.2; Lemma 2.2, p.5

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_CFLOutliers_RInst
import Definitions.Def_CFLOutliers_Sol

namespace CFLOutliers

open OnlineCRS.Combine (Sym bit encNat encRat)

/-- A list of words, each followed by the separator `3`. -/
def encWords (ws : List (List Sym)) : List Sym := ws.flatMap (fun w => w ++ [3])

/-- The words of an instance: `m, n, q`, then each list with its length first (`f`, `u`, `c`);
numbers in binary (`encNat`), rationals as `encRat`. -/
def instWords (I : RInst) : List (List Sym) :=
  [encNat I.m, encNat I.n, encNat I.q, encNat I.f.length] ++ I.f.map encRat ++
    [encNat I.u.length] ++ I.u.map encNat ++ [encNat I.c.length] ++ I.c.map encRat

/-- **Encoding of an instance** (binary; no unary numbers). -/
def encInst (I : RInst) : List Sym := encWords (instWords I)

/-- **The input of Theorem 1.1**: the instance followed by the accuracy `ε` (a rational). -/
def encGoalIn (I : RInst) (ε : ℚ) : List Sym := encWords (instWords I ++ [encRat ε])

/-- The words of a solution: one bit per facility (`1` iff open), then per client the number
`0` if rejected and `i + 1` if served by facility `i`. -/
def solWords {I : RInst} (S : Sol I.toInst) : List (List Sym) :=
  (List.finRange I.toInst.m).map (fun i => [bit (decide (i ∈ S.openSet))]) ++
    (List.finRange I.toInst.n).map (fun j => encNat ((S.σ j).elim 0 (fun i => i.val + 1)))

/-- **Encoding of a solution** (the output of Theorem 1.1 and Lemma 2.2). -/
def encSol {I : RInst} (S : Sol I.toInst) : List Sym := encWords (solWords S)

/-- **The input of Lemma 2.2**: the instance, `S⁻`, `S⁺` and the bound `M`. -/
def encMergeIn (I : RInst) (Sm Sp : Sol I.toInst) (M : ℚ) : List Sym :=
  encWords (instWords I ++ solWords Sm ++ solWords Sp ++ [encRat M])

end CFLOutliers


