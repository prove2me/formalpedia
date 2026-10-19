-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
-- name    : OAI_RepresentationTheory_Saxl_ColumnContraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:04:27.154994+00:00
-- url     : https://prove2.me/theorems/e57b8515-c0df-4d0e-895e-c2ed7c3695f4
-- title:
--   Column-reading tableaux and the column factorization of signed $2\times 2$ matrix chains
-- statement:
--   These definitions describe the cells of a diagram column by column, identify the column group of the resulting tableau with a product of symmetric groups, and introduce ordered products of $2\times 2$ matrices indexed by the cells.
--
--   Write $[n]=\{0,1,\dots,n-1\}$. A list $r=(r_0,\dots,r_{k-1})$ of natural numbers is read as $k$ consecutive columns, column $j$ having $r_j$ cells (no monotonicity is assumed); put $N=r_0+\dots+r_{k-1}$ and $R_j=r_0+\dots+r_{j-1}$. Let $\mathrm{Mat}=\mathbb{C}^{2\times 2}$ and, for $q\in\mathbb{N}$ and $X\in\mathrm{Mat}$, let $D_q(X)=\operatorname{adj}(X)$ if $q$ is even and $D_q(X)=X$ if $q$ is odd, where $\operatorname{adj}\begin{pmatrix}a&b\\ c&d\end{pmatrix}=\begin{pmatrix}d&-b\\ -c&a\end{pmatrix}$. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) closed under moving up or to the left; $|\mu|$ is its number of cells. A tableau of shape $\mu$ on the positions $[n]$ is a bijection $t:[n]\to\mu$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(q))$ and $t(q)$ lie in the same column for every position $q$.
--
--   1. **Cells and coordinates.** $\mathrm{Cells}(r)=[r_0]\sqcup[r_1]\sqcup\dots\sqcup[r_{k-1}]$ (empty when $k=0$). The element $i$ of the $j$-th summand is the cell with $\mathrm{row}=i$ and $\mathrm{col}=j$. The coordinate map $c\mapsto(\mathrm{row}(c),\mathrm{col}(c))$ is injective, with image $\{(i,j): j<k,\ i<r_j\}$.
--
--   2. **Column-major enumeration.** $\mathrm{enum}_r:[N]\to\mathrm{Cells}(r)$ is the bijection that lists the cells of column $0$ from top to bottom, then those of column $1$, and so on: a position $q$ with $R_j\le q<R_j+r_j$ goes to the cell $(q-R_j,\,j)$.
--
--   3. **Column permutations and signs.** $\mathrm{Perms}(r)=\mathfrak S_{r_0}\times\dots\times\mathfrak S_{r_{k-1}}$. A tuple $\pi=(\pi_0,\dots,\pi_{k-1})$ acts on $\mathrm{Cells}(r)$ by $\pi_j$ inside column $j$; this permutation is $\mathrm{perm}(\pi)$, and $\mathrm{sg}(\pi)=\prod_j\operatorname{sgn}(\pi_j)\in\mathbb{C}$. The map $\pi\mapsto\mathrm{perm}(\pi)$ is injective, each $\mathrm{perm}(\pi)$ preserves columns, and every column-preserving permutation of $\mathrm{Cells}(r)$ is of this form.
--
--   4. **Ordered chain.** For an offset $p\in\mathbb{N}$, a family $N_\bullet=(N_i)_{i\in\mathbb{N}}$ of matrices indexed by row numbers, and $\pi\in\mathrm{Perms}(r)$,
--   $$
--   \mathrm{chain}_r(p,N_\bullet,\pi)=\prod_{q=0}^{N-1}D_{p+q}\Big(N_{\mathrm{row}(\mathrm{perm}(\pi)(\mathrm{enum}_r(q)))}\Big),
--   $$
--   the factors being multiplied from left to right in increasing order of $q$.
--
--   5. **Alternating column segments.** $\mathrm{seg}(p,r,N_\bullet)$ is defined by recursion on the list: it is the identity matrix for the empty list, and
--   $$
--   \mathrm{seg}\big(p,(r_0,r_1,\dots),N_\bullet\big)=\Big(\sum_{\sigma\in\mathfrak S_{r_0}}\operatorname{sgn}(\sigma)\,D_{p}(N_{\sigma(0)})\,D_{p+1}(N_{\sigma(1)})\cdots D_{p+r_0-1}(N_{\sigma(r_0-1)})\Big)\,\mathrm{seg}\big(p+r_0,(r_1,\dots),N_\bullet\big).
--   $$
--   Thus it is the ordered product, over the columns, of the signed alternating sum of each column, with the global position parities kept.
--
--   6. **Column-reading tableau.** For a Young diagram $\mu$ with column lengths $\mu'=(\mu'_0,\mu'_1,\dots)$ (the row lengths of the transposed diagram), the coordinate map is a bijection from $\mathrm{Cells}(\mu')$ onto the cells of $\mu$, and the column tableau $T_\mu:[\mu'_0+\mu'_1+\cdots]\to\mu$ is its composite with $\mathrm{enum}_{\mu'}$: it numbers the cells of $\mu$ column by column, each column from top to bottom.
--
--   7. **Column group of the column tableau.** For $\pi\in\mathrm{Perms}(\mu')$, the position permutation $q\mapsto\mathrm{enum}_{\mu'}^{-1}\big(\mathrm{perm}(\pi)(\mathrm{enum}_{\mu'}(q))\big)$ lies in $C_{T_\mu}$, and the resulting map $\mathrm{Perms}(\mu')\to C_{T_\mu}$ is a bijection.
--
--   With the column tableau, the polytabloid of $\mu$ becomes an explicit signed sum over $\mathrm{Perms}(\mu')$, and the segment product is the closed form of $\sum_{\pi}\mathrm{sg}(\pi)\,\mathrm{chain}_{\mu'}(p,N_\bullet,\pi)$ in which the column sums are multiplied in their original order, so no two non-commuting matrix factors are ever exchanged. This is how matrix-valued contractions of polytabloids are evaluated when checking that such contractions do not vanish for Young diagrams with at most four rows.
--
--   **Formalization Note** `Cells` is built recursively as `Fin r ⊕ Cells rs` ending in `Empty`, and `Perms` as an iterated product ending in `Unit`; the properties quoted above are the lemmas `coords_injective`, `coords_range`, `enumerate_left`, `enumerate_right`, `perm_col`, `perm_injective`, `perm_surjective`, `toYoung_val`, `columnTableau_val` and `columnPerm_bijective`. The column tableau `columnTableau μ` has position type `Fin μ.transpose.rowLens.sum` (the sum of the column lengths, i.e. $|\mu|$), and `columnEquiv μ` is the bijection of item 7. Matrices are `Band.Mat` and $D_q$ is `Band.D q`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/ColumnContraction.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/ColumnContraction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/
@[reducible] def Cells : List ℕ → Type
  | [] => Empty
  | r :: rs => Fin r ⊕ Cells rs

instance cellsFintype : (rs : List ℕ) → Fintype (Cells rs)
  | [] => inferInstanceAs (Fintype Empty)
  | r :: rs => @instFintypeSum (Fin r) (Cells rs) inferInstance (cellsFintype rs)

instance cellsDecEq : (rs : List ℕ) → DecidableEq (Cells rs)
  | [] => inferInstanceAs (DecidableEq Empty)
  | r :: rs => @instDecidableEqSum (Fin r) (Cells rs) inferInstance (cellsDecEq rs)

def row : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl i => i.val
  | _ :: _, .inr c => row c

def col : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl _ => 0
  | _ :: _, .inr c => col c + 1

def enumerate : (rs : List ℕ) → Fin rs.sum ≃ Cells rs
  | [] => (Equiv.equivOfIsEmpty (Fin 0) Empty)
  | r :: rs => finSumFinEquiv.symm.trans ((Equiv.refl (Fin r)).sumCongr (enumerate rs))

@[simp] lemma enumerate_left (r : ℕ) (rs : List ℕ) (i : Fin r) :
    enumerate (r :: rs) (Fin.castAdd rs.sum i) = Sum.inl i := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_castAdd i)

@[simp] lemma enumerate_right (r : ℕ) (rs : List ℕ) (i : Fin rs.sum) :
    enumerate (r :: rs) (Fin.natAdd r i) = Sum.inr (enumerate rs i) := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_natAdd i)

@[reducible] def Perms : List ℕ → Type
  | [] => Unit
  | r :: rs => Equiv.Perm (Fin r) × Perms rs

instance permsFintype : (rs : List ℕ) → Fintype (Perms rs)
  | [] => inferInstanceAs (Fintype Unit)
  | r :: rs => @instFintypeProd (Equiv.Perm (Fin r)) (Perms rs) inferInstance (permsFintype rs)

def perm : {rs : List ℕ} → Perms rs → Equiv.Perm (Cells rs)
  | [], _ => Equiv.refl _
  | _ :: _, (π, σ) => Equiv.sumCongr π (perm σ)

def sg : {rs : List ℕ} → Perms rs → ℂ
  | [], _ => 1
  | _ :: _, (π, σ) => (((Equiv.Perm.sign π : ℤ) : ℂ)) * sg σ

lemma perm_col {rs : List ℕ} (π : Perms rs) (c : Cells rs) : col (perm π c) = col c := by
  induction rs with
  | nil => exact isEmptyElim c
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    cases c with
    | inl i => rfl
    | inr c => exact congrArg (· + 1) (ih σ c)

lemma coords_injective (rs : List ℕ) :
    Function.Injective (fun c : Cells rs => (row c, col c)) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext (congrArg Prod.fst h))
      | inr b => have := congrArg Prod.snd h; simp [col] at this
    | inr a =>
      cases b with
      | inl b => have := congrArg Prod.snd h; simp [col] at this
      | inr b =>
        apply congrArg Sum.inr
        apply ih
        dsimp only [row, col] at h
        have hr := congrArg Prod.fst h
        have hc := congrArg Prod.snd h
        exact Prod.ext hr (Nat.add_right_cancel hc)

lemma coords_range (rs : List ℕ) (i j : ℕ) :
    (∃ c : Cells rs, row c = i ∧ col c = j) ↔ ∃ h : j < rs.length, i < rs[j] := by
  induction rs generalizing j with
  | nil => simp [Cells]
  | cons r rs ih =>
    cases j with
    | zero =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => exact ⟨by simp, by simpa [row] using hr ▸ a.isLt⟩
        | inr a => simp [col] at hc
      · rintro ⟨h, hi⟩
        exact ⟨Sum.inl ⟨i, hi⟩, rfl, rfl⟩
    | succ j =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => simp [col] at hc
        | inr a =>
          have hj : col a = j := Nat.add_right_cancel hc
          obtain ⟨hj, hi⟩ := (ih j).mp ⟨a, hr, hj⟩
          exact ⟨Nat.succ_lt_succ hj, hi⟩
      · rintro ⟨h, hi⟩
        obtain ⟨a, ha, hc⟩ := (ih j).mpr ⟨Nat.lt_of_succ_lt_succ h, hi⟩
        exact ⟨Sum.inr a, ha, congrArg (· + 1) hc⟩

/- The matrix product indexed by the actual consecutive position order. -/
def chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) (π : Perms rs) : Band.Mat :=
  (List.ofFn fun q : Fin rs.sum => Band.D (p + q.val) (N (row (perm π (enumerate rs q))))).prod

/- Ordered product of independent alternating column segments. -/
def segments : ℕ → List ℕ → (ℕ → Band.Mat) → Band.Mat
  | _, [], _ => 1
  | p, r :: rs, N =>
      (∑ π : Equiv.Perm (Fin r), (((Equiv.Perm.sign π : ℤ) : ℂ)) •
        (List.ofFn fun i : Fin r => Band.D (p + i.val) (N (π i).val)).prod) *
      segments (p+r) rs N

/- Factorization over independent column permutations, without commuting factors. -/
lemma perm_injective (rs : List ℕ) : Function.Injective (@perm rs) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    rintro ⟨π, σ⟩ ⟨π', σ'⟩ h
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact Sum.inl.inj (Equiv.congr_fun h (Sum.inl i))
    · apply ih
      apply Equiv.ext
      intro c
      exact Sum.inr.inj (Equiv.congr_fun h (Sum.inr c))

lemma perm_surjective (rs : List ℕ) (g : Equiv.Perm (Cells rs))
    (hg : ∀ c, col (g c) = col c) : ∃ π : Perms rs, perm π = g := by
  induction rs with
  | nil => exact ⟨(), Subsingleton.elim _ _⟩
  | cons r rs ih =>
    have hm : Set.MapsTo g (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro c ⟨i, rfl⟩
      have hh := hg (Sum.inl i)
      cases h : g (Sum.inl i) with
      | inl j => exact ⟨j, rfl⟩
      | inr c => simp [h, col] at hh
    obtain ⟨⟨π, σ⟩, he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    have hs : ∀ c : Cells rs, col (σ c) = col c := by
      intro c
      have hh := hg (Sum.inr c)
      rw [← he] at hh
      exact Nat.add_right_cancel hh
    obtain ⟨τ, hτ⟩ := ih σ hs
    exact ⟨(π, τ), by simp only [perm, hτ]; exact he⟩

/- The column-recursive coordinates enumerate the actual Ferrers cells. -/
def toYoung (μ : YoungDiagram) : Cells μ.transpose.rowLens ≃ μ.cells := by
  let f : Cells μ.transpose.rowLens → μ.cells := fun c =>
    ⟨(row c, col c), by
      obtain ⟨hj, hi⟩ := (coords_range μ.transpose.rowLens (row c) (col c)).mp ⟨c, rfl, rfl⟩
      simpa only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen,
        YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose] using hi⟩
  exact Equiv.ofBijective f ⟨fun _ _ h => coords_injective _ (congrArg Subtype.val h), by
    intro c
    have hmem : c.val.1 < μ.colLen c.val.2 := YoungDiagram.mem_iff_lt_colLen.mp c.property
    have hj : c.val.2 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
      (μ.up_left_mem (Nat.zero_le _) le_rfl c.property)
    have hj' : c.val.2 < μ.transpose.rowLens.length := by simpa using hj
    obtain ⟨a, ha, hb⟩ := (coords_range μ.transpose.rowLens c.val.1 c.val.2).mpr
      ⟨hj', by simpa using hmem⟩
    exact ⟨a, Subtype.ext (Prod.ext ha hb)⟩⟩

@[simp] lemma toYoung_val (μ : YoungDiagram) (c : Cells μ.transpose.rowLens) :
    (toYoung μ c).val = (row c, col c) := rfl

def columnTableau (μ : YoungDiagram) : Tableau μ.transpose.rowLens.sum μ :=
  (enumerate μ.transpose.rowLens).trans (toYoung μ)

@[simp] lemma columnTableau_val (μ : YoungDiagram) (i : Fin μ.transpose.rowLens.sum) :
    (columnTableau μ i).val = (row (enumerate μ.transpose.rowLens i),
      col (enumerate μ.transpose.rowLens i)) := rfl

def columnPerm (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    columnGroup (columnTableau μ) :=
  ⟨(enumerate μ.transpose.rowLens).symm.permCongr (perm π), by
    intro i
    simp only [columnTableau_val, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
    exact perm_col π _⟩

lemma columnPerm_bijective (μ : YoungDiagram) : Function.Bijective (columnPerm μ) := by
  constructor
  · intro π σ h
    apply perm_injective μ.transpose.rowLens
    apply (enumerate μ.transpose.rowLens).symm.permCongr.injective
    exact congrArg Subtype.val h
  · intro g
    let e := enumerate μ.transpose.rowLens
    obtain ⟨π, hπ⟩ := perm_surjective μ.transpose.rowLens (e.permCongr g.val) (by
      intro c
      have hh := g.property (e.symm c)
      simpa only [columnTableau_val, Equiv.permCongr_apply, e, Equiv.apply_symm_apply] using hh)
    refine ⟨π, ?_⟩
    apply Subtype.ext
    change e.symm.permCongr (perm π) = g.val
    rw [hπ]
    apply Equiv.ext
    intro i
    simp [Equiv.permCongr_apply]

def columnEquiv (μ : YoungDiagram) : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
  Equiv.ofBijective (columnPerm μ) (columnPerm_bijective μ)

end Saxl.Columns

end

end OAI


