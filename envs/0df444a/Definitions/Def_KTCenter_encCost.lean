-- Prove2me | Definitions.Def_KTCenter_encCost
-- name    : KTCenter_encCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:32.723927+00:00
-- url     : https://prove2.me/theorems/9f141793-b25e-4d8e-b4c0-fe0b143d550d
-- title:
--   Binary encoding of a cost instance and of an output assignment
-- statement:
--   A cost instance is written as a word over $\{0,1,2,3\}$ listing $n$, $|U|$, $W$, for each variable its block, $|P_v|$ and $\lambda_v$, then all keys, all $A_i$, all values $u_{iv}(a)$ and all values $q_i(u,a,v,b)$, every number in binary (a rational as numerator, the symbol $2$, denominator), separated by the symbol $3$. Its length is the "total binary encoding length of the instance" of Theorem 6.1. An output assignment is the list of the chosen key indices.
--
--   **Formalization Note** The encoding fixes the order of the tables; every table entry is written, so no part of the instance is hidden from the length.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 6.1, p.58 (PDF p.60); encoding chosen by the mission

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_KTCenter_CostInstance

namespace KTCenter

open OnlineCRS.Combine

variable {K : ℕ} {C₀ C₁ : ℚ}

/-- **Binary encoding of a cost instance**, for the clause "polynomial time in the total binary
encoding length of the instance" of Theorem 6.1, p.58 (PDF p.60).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** The tokens, separated by the symbol `3`, are `n`, `N`, `W`, and for each
`v` the block, `k v` and `λ_v`, then the keys, `Aᵢ`, `uᵢᵥ` and `qᵢ` in lexicographic order. Every
table of `CostData` is written out, in binary via `encNat`/`encRat`, so the length is the total
binary encoding length. -/
def encCost (I : CostInstance K C₀ C₁) : List Sym :=
  [3].intercalate
    ([encNat I.n, encNat I.N, encRat I.W] ++
      (List.ofFn fun v : Fin I.N => [encNat (I.blk v), encNat (I.k v), encRat (I.lam v)]).flatten ++
      (List.ofFn fun v : Fin I.N => List.ofFn fun a : Fin (I.k v) => encRat (I.key v a)).flatten ++
      (List.ofFn fun i : Fin I.n => encRat (I.A i)) ++
      (List.ofFn fun i : Fin I.n => (List.ofFn fun v : Fin I.N =>
        List.ofFn fun a : Fin (I.k v) => encRat (I.u i v a)).flatten).flatten ++
      (List.ofFn fun i : Fin I.n => (List.ofFn fun u : Fin I.N =>
        (List.ofFn fun a : Fin (I.k u) => (List.ofFn fun v : Fin I.N =>
          List.ofFn fun b : Fin (I.k v) => encRat (I.q i u a v b)).flatten).flatten).flatten).flatten)

/-- The output of Theorem 6.1: the key indices of `p`, in the order of the variables. -/
def idxList {D : CostData} (p : D.Assign) : List ℕ :=
  List.ofFn fun v : Fin D.N => ((p v : Fin (D.k v)) : ℕ)

/-- Encoding of an output list of key indices: binary, separated by the symbol `3`. -/
def encIdx (l : List ℕ) : List Sym := [3].intercalate (l.map encNat)

end KTCenter


