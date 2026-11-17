-- Prove2me | Definitions.Def_CentralStrQ_Supplement_TextArrays
-- name    : CentralStrQ_Supplement_TextArrays
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:20:57.761062+00:00
-- url     : https://prove2.me/theorems/28acc8b3-4df8-4e6d-b669-429917305adb
-- title:
--   Rank queries, the BWT, LF, $\mathrm{LF}^{-1}$, $\Phi$, $\Phi^{-1}$ arrays and the (extended) alphabet mappings
-- statement:
--   Let $T\in\Sigma^n$, $n\ge1$, with suffix array $\mathrm{SA}_T$ and inverse suffix array $\mathrm{SA}^{-1}_T$ (positions $1$-based). For $i,j\in[1\,.\,.\,n]$:
--
--   1. **BWT** (Definition 3.15): $\mathrm{BWT}_T[i]=T[\mathrm{SA}_T[i]-1]$ if $\mathrm{SA}_T[i]>1$, and $T[n]$ otherwise.
--   2. **LF mapping** (Definition 3.16): $\mathrm{LF}_T[i]=\mathrm{SA}^{-1}_T[\mathrm{SA}_T[i]-1]$ if $\mathrm{SA}_T[i]>1$, and $\mathrm{SA}^{-1}_T[n]$ otherwise.
--   3. **Inverse LF** (Definition 3.17): the inverse permutation of $\mathrm{LF}_T$, i.e. $\mathrm{LF}^{-1}_T[\mathrm{SA}^{-1}_T[j]]=\mathrm{SA}^{-1}_T[j+1]$ for $j<n$ and $\mathrm{LF}^{-1}_T[\mathrm{SA}^{-1}_T[n]]=\mathrm{SA}^{-1}_T[1]$.
--   4. **Lexicographical predecessor** (Definition 3.18): $\Phi_T[\mathrm{SA}_T[1]]=\mathrm{SA}_T[n]$ and $\Phi_T[j]=\mathrm{SA}_T[\mathrm{SA}^{-1}_T[j]-1]$ otherwise.
--   5. **Inverse lexicographical predecessor** (Definition 3.19): $\Phi^{-1}_T[\mathrm{SA}_T[i]]=\mathrm{SA}_T[i+1]$ for $i<n$ and $\Phi^{-1}_T[\mathrm{SA}_T[n]]=\mathrm{SA}_T[1]$.
--
--   For a sequence $S$ of length $m$, a symbol $a$ and $j\in[0\,.\,.\,m]$, the **rank** is $\mathrm{rank}_S(j,a)=|\{i\in[1\,.\,.\,j]:S[i]=a\}|$ (Definition 3.27).
--
--   For $\sigma_1\ge\sigma_2\ge2$ and $k=\lceil\log_{\sigma_2}\sigma_1\rceil$, the **alphabet mapping** $\mathrm{map}_{\sigma_1,\sigma_2}(x)\in[0\,.\,.\,\sigma_2)^k$ of $x\in[0\,.\,.\,\sigma_1)$ is the base-$\sigma_2$ representation of $x$ with exactly $k$ digits, left-padded with zeros (Definition 4.10), and the **extended alphabet mapping** is
--   $$\mathrm{extmap}_{\sigma_1,\sigma_2}(x)=c^{k+1}\cdot0\cdot\mathrm{map}_{\sigma_1,\sigma_2}(x)\cdot0\in[0\,.\,.\,\sigma_2)^{2k+3},\qquad c=\sigma_2-1$$
--   (Definition 4.21); both extend to strings by concatenating the images of the symbols.
--
--   These are the query arrays whose indexing problems the paper characterizes, and the encodings its alphabet reductions use.
--
--   **Formalization Note** Strings are `List ℕ`; $\mathrm{SA}$ and $\mathrm{SA}^{-1}$ are the published `CentralStrQ.SA` and `CentralStrQ.ISA`. The inverse arrays are written in the explicit form the paper states as equivalent. Values at indices outside $[1\,.\,.\,n]$ are not used. $k$ is `Nat.clog σ₂ σ₁`.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Definitions 3.15–3.19, pp.16–17 (pdf pp.17–18); Definition 3.27, p.18 (pdf p.19); Definition 4.10, p.25 (pdf p.26); Definition 4.21, p.29 (pdf p.30)

import Mathlib
import Definitions.Def_CentralStrQ_Strings

set_option autoImplicit false

namespace CentralStrQ.Supplement

open CentralStrQ

/-!
# Rank queries, the BWT, LF, LF⁻¹, Φ and Φ⁻¹ arrays, and the alphabet mappings

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346): Definitions 3.15–3.19, pp.16–17
(PDF pp.17–18); Definition 3.27, p.18 (PDF p.19); Definition 4.10, p.25 (PDF p.26);
Definition 4.21, p.29 (PDF p.30).

**Formalization Note.** Strings are `List ℕ` and positions are **1-based** as in the paper
(`T[i]` is entry `i − 1`). `SA` and `ISA` are the published `CentralStrQ.SA` and
`CentralStrQ.ISA`. The arrays are written in the explicit form the paper gives for each:
`BWT_T[i] = T[SA_T[i] − 1]` if `SA_T[i] > 1` and `T[n]` otherwise; `LF_T[i] = SA⁻¹_T[SA_T[i] − 1]`
if `SA_T[i] > 1` and `SA⁻¹_T[n]` otherwise; `LF⁻¹_T[SA⁻¹_T[j]] = SA⁻¹_T[j + 1]` for `j < n` and
`LF⁻¹_T[SA⁻¹_T[n]] = SA⁻¹_T[1]` (the paper's equivalent description of the inverse permutation of
`LF_T`); `Φ_T[SA_T[1]] = SA_T[n]` and `Φ_T[j] = SA_T[SA⁻¹_T[j] − 1]` otherwise;
`Φ⁻¹_T[SA_T[i]] = SA_T[i + 1]` for `i < n` and `Φ⁻¹_T[SA_T[n]] = SA_T[1]`. Values at indices
outside `[1..n]` are junk and never used. `k = ⌈log_{σ₂} σ₁⌉` is `Nat.clog σ₂ σ₁`.
-/

/-- `rank_S(j, a) = |{i ∈ [1..j] : S[i] = a}|` (Definition 3.27). -/
def rank (S : List ℕ) (j a : ℕ) : ℕ :=
  ((Finset.Icc 1 j).filter fun i => S[i - 1]? = some a).card

/-- `BWT_T[i]` (Definition 3.15). -/
def BWT (T : List ℕ) (i : ℕ) : ℕ :=
  if 1 < SA T i then T.getD (SA T i - 2) 0 else T.getD (T.length - 1) 0

/-- `LF_T[i]` (Definition 3.16). -/
def LF (T : List ℕ) (i : ℕ) : ℕ :=
  if 1 < SA T i then ISA T (SA T i - 1) else ISA T T.length

/-- `LF⁻¹_T[i]` (Definition 3.17): with `j = SA_T[i]`, `SA⁻¹_T[j + 1]` if `j < n`, else `SA⁻¹_T[1]`. -/
def LFinv (T : List ℕ) (i : ℕ) : ℕ :=
  if SA T i < T.length then ISA T (SA T i + 1) else ISA T 1

/-- `Φ_T[j]` (Definition 3.18). -/
def Phi (T : List ℕ) (j : ℕ) : ℕ :=
  if j = SA T 1 then SA T T.length else SA T (ISA T j - 1)

/-- `Φ⁻¹_T[j]` (Definition 3.19): with `i = SA⁻¹_T[j]`, `SA_T[i + 1]` if `i < n`, else `SA_T[1]`. -/
def PhiInv (T : List ℕ) (j : ℕ) : ℕ :=
  if ISA T j < T.length then SA T (ISA T j + 1) else SA T 1

/-- `map_{σ₁,σ₂}(x)`: the base-`σ₂` representation of `x` with exactly `k = ⌈log_{σ₂} σ₁⌉` digits,
most significant first, padded with leading zeros (Definition 4.10). -/
def mapSym (σ₁ σ₂ x : ℕ) : List ℕ :=
  (List.range (Nat.clog σ₂ σ₁)).map fun i => x / σ₂ ^ (Nat.clog σ₂ σ₁ - 1 - i) % σ₂

/-- `map_{σ₁,σ₂}(S) = map(S[1]) ⋯ map(S[|S|])` (Definition 4.10). -/
def mapStr (σ₁ σ₂ : ℕ) (S : List ℕ) : List ℕ := S.flatMap (mapSym σ₁ σ₂)

/-- `extmap_{σ₁,σ₂}(x) = c^{k+1} · 0 · map_{σ₁,σ₂}(x) · 0` with `c = σ₂ − 1` (Definition 4.21). -/
def extmapSym (σ₁ σ₂ x : ℕ) : List ℕ :=
  List.replicate (Nat.clog σ₂ σ₁ + 1) (σ₂ - 1) ++ [0] ++ mapSym σ₁ σ₂ x ++ [0]

/-- `extmap_{σ₁,σ₂}(S)`, the concatenation of the blocks of the symbols (Definition 4.21). -/
def extmap (σ₁ σ₂ : ℕ) (S : List ℕ) : List ℕ := S.flatMap (extmapSym σ₁ σ₂)

end CentralStrQ.Supplement


