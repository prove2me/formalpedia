-- Prove2me | Definitions.Def_MatMulDS_BlockSeq
-- name    : MatMulDS_BlockSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:07.518884+00:00
-- url     : https://prove2.me/theorems/28fa489f-7682-4ad4-a2e7-dfdc10ba6964
-- title:
--   Block sequences, the tile and its variable assignment
-- statement:
--   A **block sequence** is a sequence $(\beta_1,\dots,\beta_L)$ of blocks with each $\beta$ appearing exactly $L\pi(\beta)$ times. It has row set $I_{\boldsymbol\beta}=\prod_\ell I_{\beta_\ell}$, middle set $K_{\boldsymbol\beta}$ and column set $J_{\boldsymbol\beta}$. Also $K_{\mathrm{block}}(\pi)=L!/\prod_\beta(L\pi(\beta))!$ and $\mathrm{Row}(\pi)=\prod_\beta|I_\beta|^{L\pi(\beta)}$.
--
--   The rows of the **tile** are triples $(\boldsymbol\beta,i,c')$, and its columns are triples $(c,\boldsymbol\beta',i')$. Given labelings $\chi_{\mathrm{mid}},\chi_{\mathrm{col}}$ and representatives, the variables of $T_{\mathrm{big}}=T_{\mathrm{base}}^{\otimes L}\otimes T_{\mathrm{rev}}^{\otimes L}$ are assigned
--   $$x_{ik}\otimes y'_{j'k'}=A[(\boldsymbol\beta,i,\chi_{\mathrm{col}}(j')),(\chi_{\mathrm{mid}}(k),\chi_{\mathrm{mid}}(k'))]\text{ if }k=\mathrm{midrep}_{\boldsymbol\beta}(\chi_{\mathrm{mid}}(k)),$$
--   $$y_{kj}\otimes x'_{k'i'}=B[(\chi_{\mathrm{mid}}(k),\chi_{\mathrm{mid}}(k')),(\chi_{\mathrm{col}}(j),\boldsymbol\beta',i')]\text{ if }k'=\mathrm{midrep}_{\boldsymbol\beta'}(\chi_{\mathrm{mid}}(k')),$$
--   and $0$ otherwise. The output of $T_{\mathrm{big}}$ at $z_{ij}\otimes z'_{j'i'}$ is $\sum_{k\in K_{\boldsymbol\beta}}\sum_{k'\in K_{\boldsymbol\beta'}}(x_{ik}\otimes y'_{j'k'})(y_{kj}\otimes x'_{k'i'})$. This embeds a matrix product into the identity.
--
--   **Formalization Note** The assignments are functions of the variables alone, since a shared right variable receives one value; $i$ determines its block sequence because row sets are disjoint. `HoldsTables` fixes a word-memory layout for the labelings.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §A.2, pp.69–71 (PDF pp.71–73)

import Mathlib
import Definitions.Def_MatMulDS_IdentityData
import Definitions.Def_MatMulDS_wordRun

set_option autoImplicit false

namespace MatMulDS

variable {I K J B : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B]

/-- A **block sequence** (p.69): a sequence `(β_1, …, β_L)` of blocks in which each block `β` appears exactly
`Lπ(β)` times. -/
def BlockSeq (T : BlockTensor I K J B) (π : I × J → ℚ) (L : ℕ) : Type :=
  {s : Fin L → B // ∀ β, (((Finset.univ.filter fun ℓ => s ℓ = β).card : ℕ) : ℚ) = L * piBlock T π β}

noncomputable instance (T : BlockTensor I K J B) (π : I × J → ℚ) (L : ℕ) : Fintype (BlockSeq T π L) := by
  unfold BlockSeq; classical infer_instance

variable (T : BlockTensor I K J B)

/-- The row set `I_β = ∏_ℓ I_{β_ℓ}` of a sequence of blocks (p.69). -/
def rowSet {L : ℕ} (s : Fin L → B) : Finset (Fin L → I) := Fintype.piFinset fun ℓ => T.rows (s ℓ)

/-- The middle set `K_β = ∏_ℓ K_{β_ℓ}` of a sequence of blocks (p.69). -/
def midSet {L : ℕ} (s : Fin L → B) : Finset (Fin L → K) := Fintype.piFinset fun ℓ => T.mids (s ℓ)

/-- The column set `J_β = ∏_ℓ J_{β_ℓ}` of a sequence of blocks (p.69). -/
def colSet {L : ℕ} (s : Fin L → B) : Finset (Fin L → J) := Fintype.piFinset fun ℓ => T.cols (s ℓ)

/-- The integer `Lπ(β)`, for admissible `L`. -/
def countOf (π : I × J → ℚ) (L : ℕ) (β : B) : ℕ := ⌊(L : ℚ) * piBlock T π β⌋₊

/-- `Kblock(π) = L! / ∏_β (Lπ(β))!`, (A.8), p.69. -/
def Kblock (π : I × J → ℚ) (L : ℕ) : ℕ := L.factorial / ∏ β, (countOf T π L β).factorial

/-- `Row(π) = ∏_β |I_β|^{Lπ(β)}`, (A.9), p.70. -/
def rowCount (π : I × J → ℚ) (L : ℕ) : ℕ := ∏ β, (T.rows β).card ^ countOf T π L β

/-- The row index of the tile (Lemma A.4, p.71): a triple `(β, i, c′)`, with `β` a block sequence, `i ∈ I_β` and
`c′ ∈ [C̃ol(π)]`. -/
abbrev TileRow (π : I × J → ℚ) (L cc : ℕ) : Type :=
  Σ s : BlockSeq T π L, {i : Fin L → I // i ∈ rowSet T s.1} × Fin cc

/-- The column index of the tile (Lemma A.4, p.71): a triple `(c, β′, i′)`. -/
abbrev TileCol (π : I × J → ℚ) (L cc : ℕ) : Type :=
  Σ s : BlockSeq T π L, Fin cc × {i : Fin L → I // i ∈ rowSet T s.1}

variable {T} {F : Type} [Field F] {π : I × J → ℚ} {L m cc : ℕ}

/-- The assignment of Lemma A.4, p.71, to the left variable `x_ik ⊗ y′_j′k′` of `T_big`: it is
`A[(β, i, χcol(j′)), (χmid(k), χmid(k′))]` if `k = midrep_β(χmid(k))`, where `β` is the block sequence of `i`, and
`0` otherwise, and `0` if `i` has no block sequence.

**Formalization Note** The row sets of different block sequences are disjoint, so `β` is determined by `i`. -/
noncomputable def tileLeft (A : Matrix (TileRow T π L cc) (Fin m × Fin m) F)
    (χmid : (Fin L → K) → Fin m) (χcol : (Fin L → J) → Fin cc)
    (midrep : BlockSeq T π L → Fin m → (Fin L → K))
    (i : Fin L → I) (k : Fin L → K) (j' : Fin L → J) (k' : Fin L → K) : F :=
  open Classical in
  if h : ∃ s : BlockSeq T π L, i ∈ rowSet T s.1 then
    if k = midrep h.choose (χmid k) then
      A ⟨h.choose, ⟨i, h.choose_spec⟩, χcol j'⟩ (χmid k, χmid k')
    else 0
  else 0

/-- The assignment of Lemma A.4, p.71, to the right variable `y_kj ⊗ x′_k′i′` of `T_big`: it is
`B[(χmid(k), χmid(k′)), (χcol(j), β′, i′)]` if `k′ = midrep_β′(χmid(k′))`, where `β′` is the block sequence of `i′`,
and `0` otherwise, and `0` if `i′` has no block sequence. -/
noncomputable def tileRight (B' : Matrix (Fin m × Fin m) (TileCol T π L cc) F)
    (χmid : (Fin L → K) → Fin m) (χcol : (Fin L → J) → Fin cc)
    (midrep : BlockSeq T π L → Fin m → (Fin L → K))
    (k : Fin L → K) (j : Fin L → J) (k' : Fin L → K) (i' : Fin L → I) : F :=
  open Classical in
  if h : ∃ s : BlockSeq T π L, i' ∈ rowSet T s.1 then
    if k' = midrep h.choose (χmid k') then
      B' (χmid k, χmid k') ⟨h.choose, χcol j, ⟨i', h.choose_spec⟩⟩
    else 0
  else 0

/-- The output of `T_big = T_base^{⊗L} ⊗ T_rev^{⊗L}` at `z_ij ⊗ z′_j′i′`, on an assignment `X` to its left variables
`x_ik ⊗ y′_j′k′` and `Y` to its right variables `y_kj ⊗ x′_k′i′`, for `i ∈ I_β`, `j ∈ J_β`, `i′ ∈ I_β′`, `j′ ∈ J_β′`
(proof of Lemma A.4, p.71): `Σ_{k∈K_β} Σ_{k′∈K_β′} (x_ik ⊗ y′_j′k′)(y_kj ⊗ x′_k′i′)`. -/
def bigOutput (T : BlockTensor I K J B) {L : ℕ} (s s' : Fin L → B)
    (X : (Fin L → I) → (Fin L → K) → (Fin L → J) → (Fin L → K) → F)
    (Y : (Fin L → K) → (Fin L → J) → (Fin L → K) → (Fin L → I) → F)
    (i : Fin L → I) (j j' : Fin L → J) (i' : Fin L → I) : F :=
  ∑ k ∈ midSet T s, ∑ k' ∈ midSet T s', X i k j' k' * Y k j k' i'

/-- The tables of the labelings in a word memory: cells `0` and `1` hold `M̃id(π)` and `C̃ol(π)`, cells `2, 3, 4, 5`
point to the tables of `χmid`, `χcol`, `midrep`, `colrep`, which are indexed by the codes `encStr` of the strings
and of the block sequences. -/
def HoldsTables {w : ℕ} (mem : ℤ → BitVec w) (χmid : (Fin L → K) → Fin m) (χcol : (Fin L → J) → Fin cc)
    (midrep : BlockSeq T π L → Fin m → (Fin L → K)) (colrep : BlockSeq T π L → Fin cc → (Fin L → J)) :
    Prop :=
  (mem 0).toNat = m ∧ (mem 1).toNat = cc ∧
  (∀ k, (mem ((mem 2).toInt + encStr k)).toNat = χmid k) ∧
  (∀ j, (mem ((mem 3).toInt + encStr j)).toNat = χcol j) ∧
  (∀ (s : BlockSeq T π L) (l : Fin m),
    (mem ((mem 4).toInt + encStr s.1 * m + (l : ℕ))).toNat = encStr (midrep s l)) ∧
  (∀ (s : BlockSeq T π L) (l : Fin cc),
    (mem ((mem 5).toInt + encStr s.1 * cc + (l : ℕ))).toNat = encStr (colrep s l))

end MatMulDS


