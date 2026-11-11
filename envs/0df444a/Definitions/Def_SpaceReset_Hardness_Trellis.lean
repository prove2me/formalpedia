-- Prove2me | Definitions.Def_SpaceReset_Hardness_Trellis
-- name    : SpaceReset_Hardness_Trellis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:33.239193+00:00
-- url     : https://prove2.me/theorems/e6fef7f4-5d19-4d2e-9701-33a0623635cc
-- title:
--   Cut invariants $c(G)$, $\Pi(G)$, output orders and minimal-span bases
-- statement:
--   A **binary specification** is a matrix $G\in\mathbb F_2^{k\times n}$ with independent rows (one for each of $k$ fair bits) and columns $g_1,\dots,g_n$ (one per output slot); zero columns and $k=0$ are allowed. For cuts $0\le u\le v\le n$ let $U_L$, $U_J$, $U_R$ be the spans of the columns in the prefix $[1,u]$, the middle $(u,v]$ and the suffix $(v,n]$, and write $L_u$, $R_u$ for the prefix and suffix spans at a single cut. The two invariants are
--
--   $$c(G)=\max_{0\le u\le n}\dim(L_u\cap R_u),\qquad \Pi(G)=\max_{0\le u\le v\le n}\Big[\dim(U_L\cap U_R)+\dim\big((U_L+U_J)\cap(U_J+U_R)\big)\Big].$$
--
--   An **output order** of a matrix whose columns are labelled by a finite set $\iota$ is a bijection $\pi:\{0,\dots,n-1\}\to\iota$; the reordered matrix $G^\pi$ has column $\pi(j)$ in position $j$. The order-optimized values are $c_*(G)=\min_\pi c(G^\pi)$ and $\Pi_*(G)=\min_\pi\Pi(G^\pi)$.
--
--   For a nonzero row $r\in\mathbb F_2^n$, $s(r)$ and $t(r)$ denote its first and last nonzero positions ($1$-based). A **minimal-span basis** of the row space of $G$ is a row basis with nonzero rows whose starts $s_i$ are pairwise distinct and whose ends $t_i$ are pairwise distinct. For such a basis and a family $R$ of its rows,
--
--   $$L_R(u)=\#\{i\in R:s_i\le u<t_i\},\qquad P_R(u,v)=L_R(u)+L_R(v)+\#\{i\in R:u<s_i\le t_i\le v\},$$
--
--   $\Pi_R=\max_{u\le v}P_R(u,v)$, and the span window count of (27) is $\#\{i:s_i\le v,\,t_i>u\}+\#\{i:s_i\le u,\,t_i>v\}$. At a memory budget $q$ the **forced singletons** are $F=\{i:s_i=t_i=p,\ L(p-1)=L(p)=q\}$, with $L$ the live count of all rows. A partition of $R$ into at most $q$ **weakly ordered chains** is a labelling with $q$ labels in which any two distinct equally labelled rows satisfy $t_i\le s_j$ or $t_j\le s_i$; its cost is $\sum_C(|C|-2)_+$.
--
--   A generator is **coordinate-duplicated** if every column occurs at least twice. The **direct-sum code** of sources $G_0,\dots,G_{m-1}$ in block order places the blocks diagonally, block $0$ first.
--
--   **Formalization Note** Columns are stored $0$-based (column $j$ is slot $j+1$) and cuts $u$ are natural numbers; spans of a minimal-span basis are kept $1$-based as on the page. Maxima over cuts are finite suprema over nonempty ranges; $c_*,\Pi_*$ are infima over the nonempty finite set of orders. $s,t$ are only used on nonzero rows. Natural subtraction gives the positive parts $(\cdot)_+$.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), eq. (1), p. 7; eqs. (11)–(12), p. 16; §2.4.2, p. 18; §3.2, p. 25 ($c_*$, $\Pi_*$); App. B.1, p. 38; App. D.1, p. 41

import Mathlib

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness

/-!
Rinka Miura, STOC 2027 submission #1715 (October 2026): binary specifications, output orders and
the two cut invariants `c(G)`, `Π(G)` (§1.5.1, p. 6; eq. (1), p. 7; eqs. (11)–(12), p. 16), the
minimal-span row bases of App. D.1 (p. 41) and the live/window counts and forced singletons of
§2.4.2 (p. 18).

Conventions. A specification is a binary matrix `G` with row index type `κ` (the `k = |κ|` fair
bits) and `n` columns `g₁, …, gₙ`, stored 0-based as `G i j`, `j : Fin n`; column `j` (0-based) is
the paper's slot `j + 1`. A cut `u ∈ {0,…,n}` separates the first `u` columns (prefix `[1,u]`)
from the rest. For `0 ≤ u ≤ v ≤ n` the prefix is `[1,u]`, the middle `(u,v]` and the suffix
`(v,n]`. Row spans of a minimal-span basis are written 1-based, `[sᵢ, tᵢ] ⊆ [1,n]`, as on the
page. An output order of a matrix whose columns are indexed by a finite type `ι` is a bijection
`π : Fin n ≃ ι` (`n = |ι|`); the reordered matrix `G^π` has `π j` as its column `j`.
-/

/-- The binary field `𝔽₂`. -/
abbrev F2 := ZMod 2

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The column span of a set `S` of column positions: `span{g_j : j ∈ S} ⊆ 𝔽₂^κ`. -/
def colSpan {n : ℕ} (G : Matrix κ (Fin n) F2) (S : Set (Fin n)) : Submodule F2 (κ → F2) :=
  Submodule.span F2 ((fun j : Fin n => fun i : κ => G i j) '' S)

/-- `L_u` = `U_L`: span of the prefix columns `[1,u]` (0-based positions `< u`). -/
def prefixSpan {n : ℕ} (G : Matrix κ (Fin n) F2) (u : ℕ) : Submodule F2 (κ → F2) :=
  colSpan G {j | j.val < u}

/-- `U_J`: span of the middle columns `(u,v]` (0-based positions `u ≤ j < v`). -/
def middleSpan {n : ℕ} (G : Matrix κ (Fin n) F2) (u v : ℕ) : Submodule F2 (κ → F2) :=
  colSpan G {j | u ≤ j.val ∧ j.val < v}

/-- `R_v` = `U_R`: span of the suffix columns `(v,n]` (0-based positions `≥ v`). -/
def suffixSpan {n : ℕ} (G : Matrix κ (Fin n) F2) (v : ℕ) : Submodule F2 (κ → F2) :=
  colSpan G {j | v ≤ j.val}

/-- The single-cut dimension `dim(L_u ∩ R_u)`. -/
def cutDim {n : ℕ} (G : Matrix κ (Fin n) F2) (u : ℕ) : ℕ :=
  Module.finrank F2 ↥(prefixSpan G u ⊓ suffixSpan G u)

/-- Eq. (11): the trellis width `c(G) = max_{0 ≤ u ≤ n} dim(L_u ∩ R_u)`. -/
def cInv {n : ℕ} (G : Matrix κ (Fin n) F2) : ℕ :=
  (Finset.range (n + 1)).sup (fun u => cutDim G u)

/-- The numerator of (12) at cuts `u ≤ v`:
`dim(U_L ∩ U_R) + dim((U_L + U_J) ∩ (U_J + U_R))`. -/
def windowDim {n : ℕ} (G : Matrix κ (Fin n) F2) (u v : ℕ) : ℕ :=
  Module.finrank F2 ↥(prefixSpan G u ⊓ suffixSpan G v) +
    Module.finrank F2 ↥((prefixSpan G u ⊔ middleSpan G u v) ⊓ (middleSpan G u v ⊔ suffixSpan G v))

/-- The pairs of cuts `0 ≤ u ≤ v ≤ n`. -/
def cutPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter (fun p => p.1 ≤ p.2)

/-- Eq. (12): the two-cut invariant `Π(G) = max_{0 ≤ u ≤ v ≤ n} windowDim G u v`. -/
def PiInv {n : ℕ} (G : Matrix κ (Fin n) F2) : ℕ :=
  (cutPairs n).sup (fun p => windowDim G p.1 p.2)

/-- `G` has full row rank `|κ|` ("its rows are independent", p. 6); columns indexed by any finite
type. -/
def FullRowRank {ι : Type} [Fintype ι] (G : Matrix κ ι F2) : Prop :=
  G.rank = Fintype.card κ

/-- The reordered specification `G^π` for an output order `π : Fin n ≃ ι` of the columns. -/
def reorder {ι : Type} {n : ℕ} (G : Matrix κ ι F2) (π : Fin n ≃ ι) : Matrix κ (Fin n) F2 :=
  G.submatrix id π

/-- `c_*(G) = min_π c(G^π)` over all output orders (p. 25). The index type of orders is
nonempty, so the infimum is a minimum. -/
def cStar {ι : Type} [Fintype ι] (G : Matrix κ ι F2) : ℕ :=
  ⨅ π : Fin (Fintype.card ι) ≃ ι, cInv (reorder G π)

/-- `Π_*(G) = min_π Π(G^π)` over all output orders (p. 25). -/
def PiStar {ι : Type} [Fintype ι] (G : Matrix κ ι F2) : ℕ :=
  ⨅ π : Fin (Fintype.card ι) ≃ ι, PiInv (reorder G π)

/-! ### Minimal-span row bases (App. D.1, p. 41) -/

/-- The set of 1-based positions `j + 1` at which a row `r ∈ 𝔽₂^n` is nonzero. -/
def supportPositions {n : ℕ} (r : Fin n → F2) : Set ℕ :=
  {p | ∃ j : Fin n, j.val + 1 = p ∧ r j ≠ 0}

/-- The 1-based first nonzero position `s` of a row (used only for nonzero rows). -/
def rowStart {n : ℕ} (r : Fin n → F2) : ℕ := sInf (supportPositions r)

/-- The 1-based last nonzero position `t` of a row (used only for nonzero rows). -/
def rowEnd {n : ℕ} (r : Fin n → F2) : ℕ := sSup (supportPositions r)

/-- `B` is a minimal-span basis of the row space of `G` (App. D.1, p. 41): a row basis of the same
row space whose rows are nonzero, with pairwise distinct first nonzero positions `sᵢ` and pairwise
distinct last nonzero positions `tᵢ`. -/
def IsMinimalSpanBasis {n : ℕ} (G B : Matrix κ (Fin n) F2) : Prop :=
  Submodule.span F2 (Set.range B) = Submodule.span F2 (Set.range G) ∧
  (∀ i, B i ≠ 0) ∧
  Function.Injective (fun i => rowStart (B i)) ∧
  Function.Injective (fun i => rowEnd (B i))

/-- Eq. (27), p. 41: `P(u,v) = #{i : sᵢ ≤ v, tᵢ > u} + #{i : sᵢ ≤ u, tᵢ > v}`. -/
def spanWindowCount {n : ℕ} (B : Matrix κ (Fin n) F2) (u v : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => rowStart (B i) ≤ v ∧ u < rowEnd (B i))).card +
    (Finset.univ.filter (fun i => rowStart (B i) ≤ u ∧ v < rowEnd (B i))).card

/-- The live count over a row family `R` (p. 18): `L_R(u) = #{i ∈ R : sᵢ ≤ u < tᵢ}`. -/
def liveCount {n : ℕ} (B : Matrix κ (Fin n) F2) (R : Finset κ) (u : ℕ) : ℕ :=
  (R.filter (fun i => rowStart (B i) ≤ u ∧ u < rowEnd (B i))).card

/-- The window count over a row family `R` (p. 18):
`P_R(u,v) = L_R(u) + L_R(v) + #{i ∈ R : u < sᵢ ≤ tᵢ ≤ v}`. -/
def windowCount {n : ℕ} (B : Matrix κ (Fin n) F2) (R : Finset κ) (u v : ℕ) : ℕ :=
  liveCount B R u + liveCount B R v +
    (R.filter (fun i => u < rowStart (B i) ∧ rowStart (B i) ≤ rowEnd (B i) ∧ rowEnd (B i) ≤ v)).card

/-- `Π_R = max_{0 ≤ u ≤ v ≤ n} P_R(u,v)`. -/
def windowMax {n : ℕ} (B : Matrix κ (Fin n) F2) (R : Finset κ) : ℕ :=
  (cutPairs n).sup (fun p => windowCount B R p.1 p.2)

/-- The forced singleton rows at memory budget `q` (p. 18):
`F = {i : sᵢ = tᵢ = p, L(p − 1) = L(p) = q}`, with `L` the live count of all rows. -/
def forcedSet {n : ℕ} (B : Matrix κ (Fin n) F2) (q : ℕ) : Finset κ :=
  Finset.univ.filter (fun i => rowStart (B i) = rowEnd (B i) ∧
    liveCount B Finset.univ (rowStart (B i) - 1) = q ∧
    liveCount B Finset.univ (rowStart (B i)) = q)

/-- A partition of the rows `R` into at most `q` weakly ordered chains (p. 18), given as a label
`col i ∈ {0,…,q−1}` for each row `i ∈ R` (empty classes are allowed; for `R = ∅` the empty
labelling is the partition into zero chains). Two distinct rows of `R` with the same label are
weakly separated: `tᵢ ≤ sⱼ` or `tⱼ ≤ sᵢ`; equivalently each class, sorted by start, has
`tᵢ ≤ sⱼ` for consecutive spans. -/
def IsChainPartition {n q : ℕ} (B : Matrix κ (Fin n) F2) (R : Finset κ) (col : R → Fin q) : Prop :=
  ∀ i j : R, i ≠ j → col i = col j →
    rowEnd (B i) ≤ rowStart (B j) ∨ rowEnd (B j) ≤ rowStart (B i)

/-- The chain cost `Σ_C (|C| − 2)_+` of a labelled partition of `R` (natural subtraction is the
positive part). -/
def chainCost {q : ℕ} {R : Finset κ} (col : R → Fin q) : ℕ :=
  ∑ a : Fin q, ((Finset.univ.filter (fun i : R => col i = a)).card - 2)

/-- Binary layout of a labelled partition of `R ⊆ Fin k`: for each row `i`, `col i + 1` if
`i ∈ R` and `0` otherwise. -/
def retainedLabelNats {k q : ℕ} {R : Finset (Fin k)} (col : R → Fin q) : List ℕ :=
  (List.finRange k).map (fun i => if h : i ∈ R then (col ⟨i, h⟩).val + 1 else 0)

/-- A coordinate-duplicated generator (p. 21): every column occurs at least twice. -/
def IsCoordDuplicated {n : ℕ} (G : Matrix κ (Fin n) F2) : Prop :=
  ∀ j : Fin n, ∃ j' : Fin n, j' ≠ j ∧ (fun i => G i j') = (fun i => G i j)

/-! ### Independent concatenation (App. B.1, p. 38) -/

/-- The direct-sum code of ordered sources `G₀, …, G_{m−1}` (`Gᵢ ∈ 𝔽₂^{kᵢ×nᵢ}`) in block order:
rows `(i, a)`, columns of block `0` first, then block `1`, and so on; the entry is `Gᵢ a j` on
block `i`'s own columns and `0` elsewhere. -/
def directSum {m : ℕ} {k n : Fin m → ℕ} (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) :
    Matrix ((i : Fin m) × Fin (k i)) (Fin (∑ i, n i)) F2 :=
  fun r c =>
    let p := finSigmaFinEquiv.symm c
    if h : p.1 = r.1 then G r.1 r.2 (Fin.cast (congrArg n h) p.2) else 0

end SpaceReset.Hardness


