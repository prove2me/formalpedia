-- Prove2me | Definitions.Def_CentralStrQ_Supplement_PrefixQueries
-- name    : CentralStrQ_Supplement_PrefixQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:21:24.421067+00:00
-- url     : https://prove2.me/theorems/ecd211c4-39ba-43d5-a6b7-998f30680366
-- title:
--   Prefix select, prefix extension access, prefix extension mapping and prefix contraction mapping queries
-- statement:
--   Let $S\in(\Sigma^*)^m$ be a sequence of strings, $X\in\Sigma^*$ and $r\ge1$, and let $j=\text{prefix-select}_S(r,X)$ be the $r$-th smallest $i\in[1\,.\,.\,m]$ such that $X$ is a prefix of $S[i]$ ($\infty$ if there are fewer than $r$). Following Definition 3.30:
--
--   1. $\text{prefix-extension-access}_S(r,X)=S[j][|X|+1]$ if $j\ne\infty$ and $|X|<|S[j]|$, and $+\infty$ otherwise;
--   2. $\text{prefix-extension-mapping}_S(r,X)=(S[j][|X|+1],\ \text{prefix-special-rank}_S(j,|X|+1))$ under the same condition, and $+\infty$ otherwise;
--   3. for $X\ne\varepsilon$, $\text{prefix-contraction-mapping}_S(r,X)=\text{prefix-special-rank}_S(j,|X|-1)$ if $j\ne\infty$, and $+\infty$ otherwise,
--
--   where $\text{prefix-special-rank}_S(j,p)$ is the number of $i\in[1\,.\,.\,j]$ such that $S[j][1\,.\,.\,p]$ is a prefix of $S[i]$.
--
--   These are the prefix queries on sequences of strings that the paper shows equivalent to BWT, LF and $\mathrm{LF}^{-1}$ queries.
--
--   **Formalization Note** Prefix rank, prefix special rank and prefix select are the published `ConstTimeISA.Main` definitions (the latter encodes $\infty$ as $0$, never a valid index). Values that may be $\pm\infty$ are `Option` values, `none` standing for $\pm\infty$. Indices are $1$-based.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Definition 3.30, pp.18–19 (pdf pp.19–20)

import Mathlib
import Definitions.Def_ConstTimeISA_Main_Prefix

set_option autoImplicit false

namespace CentralStrQ.Supplement

open ConstTimeISA.Main

/-!
# Prefix select, prefix extension access, prefix extension mapping, prefix contraction mapping

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Definition 3.30, pp.18–19
(PDF pp.19–20). With `j = prefix-select_S(r, X)`:
* `prefix-extension-access_S(r, X) = S[j][|X| + 1]` if `j ≠ ∞` and `|X| < |S[j]|`, else `+∞`;
* `prefix-extension-mapping_S(r, X) = (S[j][|X| + 1], prefix-special-rank_S(j, |X| + 1))` under the
  same condition, else `+∞`;
* for `X ≠ ε`, `prefix-contraction-mapping_S(r, X) = prefix-special-rank_S(j, |X| − 1)` if `j ≠ ∞`,
  else `+∞`.

**Formalization Note.** Sequences of strings are `List (List ℕ)` with 1-based indices (`S[j]` is
entry `j − 1`). Prefix rank, prefix special rank and prefix select are the published
`ConstTimeISA.Main.prefixRank`, `prefixSpecialRank` and `prefixSelect` (the last encodes `∞` as `0`,
never a valid index). Here every query value that may be `±∞` is an `Option`: `none` is `±∞`.
-/

/-- `prefix-select_S(r, X)` with `none` for `∞` (Definition 3.30). -/
def prefixSelectOpt (S : List (List ℕ)) (r : ℕ) (X : List ℕ) : Option ℕ :=
  if prefixSelect S r X = 0 then none else some (prefixSelect S r X)

/-- `prefix-extension-access_S(r, X)`, `none` for `+∞` (Definition 3.30). -/
def prefixExtAccess (S : List (List ℕ)) (r : ℕ) (X : List ℕ) : Option ℕ :=
  match prefixSelectOpt S r X with
  | none => none
  | some j => (S.getD (j - 1) [])[X.length]?

/-- `prefix-extension-mapping_S(r, X)`, `none` for `+∞` (Definition 3.30). -/
def prefixExtMap (S : List (List ℕ)) (r : ℕ) (X : List ℕ) : Option (ℕ × ℕ) :=
  match prefixSelectOpt S r X with
  | none => none
  | some j => ((S.getD (j - 1) [])[X.length]?).map fun a => (a, prefixSpecialRank S j (X.length + 1))

/-- `prefix-contraction-mapping_S(r, X)` for `X ≠ ε`, `none` for `+∞` (Definition 3.30). -/
def prefixContrMap (S : List (List ℕ)) (r : ℕ) (X : List ℕ) : Option ℕ :=
  (prefixSelectOpt S r X).map fun j => prefixSpecialRank S j (X.length - 1)

end CentralStrQ.Supplement


