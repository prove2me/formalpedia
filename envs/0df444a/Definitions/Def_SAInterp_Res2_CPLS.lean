-- Prove2me | Definitions.Def_SAInterp_Res2_CPLS
-- name    : SAInterp_Res2_CPLS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:38:40.789699+00:00
-- url     : https://prove2.me/theorems/8fbc452e-a3a6-4bf0-93ed-5900694bce57
-- title:
--   The Coloured PLS formula CPLS_n (Definition 5.1) and its binary encoding CPLS^bool_n for n = 2^ℓ
-- statement:
--   Fix $n\ge1$ and the grid $[n]\times[n]$ of nodes $u=(i,j)$ (row $i$, column $j$), with distinguished source $(1,1)$. The multivalued variables of **$\mathrm{CPLS}_n$** (Definition 5.1) are the activity $a_u\in\{0,1\}$ ($u\in[n]^2$), the successor $s_u\in[n]$ ($u\in[n-1]\times[n]$), the colour $c_{u,\alpha}\in\{0,1\}$ ($u\in[n]^2,\alpha\in[n]$) and the selector $e_u\in[n]$ ($u\in[n]^2$). Its clauses are:
--   1. colourless source: $[\![c_{(1,1),\alpha}\neq1]\!]$ for all $\alpha$;
--   2. inactive sinks: $[\![a_u\neq1]\!]$ for $u\in\{n\}\times[n]$;
--   3. colour creation: $[\![a_u\neq0]\!]\vee[\![e_u\neq\alpha]\!]\vee[\![c_{u,\alpha}\neq0]\!]$ for all $u,\alpha$;
--   4. colour propagation: $[\![a_{ij}\neq1]\!]\vee[\![s_{ij}\neq k]\!]\vee[\![c_{(i+1,k),\alpha}\neq1]\!]\vee[\![c_{(i,j),\alpha}\neq0]\!]$ for $i<n$ and all $j,k,\alpha$.
--
--   For $n=2^\ell$, **$\mathrm{CPLS}^{\mathrm{bool}}_n$** is $\mathrm{CPLS}_n$ under the binary encoding of the indicator definitions: each $\{0,1\}$-valued variable is one bit, and each $[n]$-valued variable is $\ell$ bits.
--
--   **Formalization Note.** Indices are 0-based. The paper's row, column or colour $r\in[n]$ is $r-1$ in `Fin n`, so the source is $(0,0)$, the bottom row is $n-1$, and the value $j\in[n]$ of a successor or selector is $j-1$. Successor variables are indexed by `Fin (n - 1) × Fin n`. `cplsSize (2^ℓ) v = 2 ^ cplsBits ℓ v` holds for every variable.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 32, Definition 5.1; p. 44 (CPLS^bool_n, n = 2^ℓ); p. 21 (binary encoding)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams
import Definitions.Def_SAInterp_Res2_Indicator

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

open Classical

/-!
# The Coloured PLS formula `CPLS_n` and its binary encoding `CPLS^bool_n`

Acheampong, Davis, Robere, *Polynomial Interpolation for Sherali-Adams Lower Bounds*,
STOC 2027 submission (manuscript sha256 8de0a787…), Definition 5.1 (p. 32) and §8 (p. 44).

Indices are 0-based: the paper's row/column/colour `r ∈ [n]` is `r − 1 : Fin n`. Row `0` is the
top row, row `n − 1` the bottom row (the sinks), and `(0, 0)` is the distinguished source.
The ranges are `{0,1} = Fin 2` and `[n] = Fin n` (value `j ∈ [n]` is `j − 1 : Fin n`).
-/

/-- The variables of `CPLS_n`: activity `a_{(i,j)}` (`{0,1}`), successor `s_{(i,j)}` (`[n]`) for
the rows `i` above the bottom row, colour `c_{(i,j),α}` (`{0,1}`) and selector `e_{(i,j)}`
(`[n]`). -/
inductive CPLSVar (n : ℕ) : Type
  | act (i j : Fin n)
  | succ (i : Fin (n - 1)) (j : Fin n)
  | col (i j α : Fin n)
  | sel (i j : Fin n)
  deriving DecidableEq, Fintype

/-- The range sizes: `2` for activity and colour bits, `n` for successors and selectors. -/
def cplsSize (n : ℕ) : CPLSVar n → ℕ
  | .act _ _ => 2
  | .succ _ _ => n
  | .col _ _ _ => 2
  | .sel _ _ => n

/-- Row `i < n − 1` as a row of the grid. -/
def rowOf {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩

/-- The row below row `i < n − 1`. -/
def nextRow {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val + 1, by have := i.isLt; omega⟩

/-- The indicator `⟦a_{(i,j)} = b⟧`. -/
def indAct {n : ℕ} (i j : Fin n) (b : Fin 2) : Indicator (cplsSize n) := ⟨.act i j, b⟩

/-- The indicator `⟦s_{(i,j)} = k⟧`. -/
def indSucc {n : ℕ} (i : Fin (n - 1)) (j k : Fin n) : Indicator (cplsSize n) := ⟨.succ i j, k⟩

/-- The indicator `⟦c_{(i,j),α} = b⟧`. -/
def indCol {n : ℕ} (i j α : Fin n) (b : Fin 2) : Indicator (cplsSize n) := ⟨.col i j α, b⟩

/-- The indicator `⟦e_{(i,j)} = α⟧`. -/
def indSel {n : ℕ} (i j α : Fin n) : Indicator (cplsSize n) := ⟨.sel i j, α⟩

/-- The clauses of `CPLS_n` (Definition 5.1), each written as the set of indicators it negates:
1. colourless source `⟦c_{(1,1),α} ≠ 1⟧`;
2. inactive sinks `⟦a_u ≠ 1⟧` for `u` on the bottom row;
3. colour creation `⟦a_u ≠ 0⟧ ∨ ⟦e_u ≠ α⟧ ∨ ⟦c_{u,α} ≠ 0⟧`;
4. colour propagation `⟦a_{ij} ≠ 1⟧ ∨ ⟦s_{ij} ≠ k⟧ ∨ ⟦c_{(i+1,k),α} ≠ 1⟧ ∨ ⟦c_{(i,j),α} ≠ 0⟧`
   for `i < n`. -/
def IsCPLSClause (n : ℕ) (Cl : MVClause (cplsSize n)) : Prop :=
  (∃ i j α : Fin n, i.val = 0 ∧ j.val = 0 ∧ Cl = {indCol i j α 1}) ∨
  (∃ i j : Fin n, i.val + 1 = n ∧ Cl = {indAct i j 1}) ∨
  (∃ i j α : Fin n, Cl = {indAct i j 0, indSel i j α, indCol i j α 0}) ∨
  (∃ (i : Fin (n - 1)) (j k α : Fin n),
    Cl = {indAct (rowOf i) j 1, indSucc i j k, indCol (nextRow i) k α 1, indCol (rowOf i) j α 0})

/-- The multivalued formula `CPLS_n` (Definition 5.1). -/
noncomputable def CPLS (n : ℕ) : MVCNF (cplsSize n) :=
  (Finset.univ : Finset (MVClause (cplsSize n))).filter (IsCPLSClause n)

/-- The number of bits of each variable of `CPLS_{2^ℓ}` in the binary encoding: `1` for the
`{0,1}`-valued activity and colour variables, `ℓ` for the `[2^ℓ]`-valued successors and
selectors (so `cplsSize (2^ℓ) v = 2 ^ cplsBits ℓ v`). -/
def cplsBits (ℓ : ℕ) : CPLSVar (2 ^ ℓ) → ℕ
  | .act _ _ => 1
  | .succ _ _ => ℓ
  | .col _ _ _ => 1
  | .sel _ _ => ℓ

/-- `CPLS^bool_n` for `n = 2^ℓ`: `CPLS_n` with every variable encoded in binary (§2.3, §8). -/
noncomputable def CPLSbool (ℓ : ℕ) : CNF (BoolVar (cplsBits ℓ)) :=
  cnfBool (cplsBits ℓ) (CPLS (2 ^ ℓ))

end SAInterp.Res2


