-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
-- name    : OAI_RepresentationTheory_Saxl_BandFactorization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:56:05.448001+00:00
-- url     : https://prove2.me/theorems/1c54a273-b77e-45fb-a079-946897352e0a
-- title:
--   Cutting the staircase $\delta_{h+s}$ into the sub-staircase $\delta_h$ and an outer band
-- statement:
--   For $n\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the symmetric group on $[n]$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}=\mathbb{C}^{[d]^n}$ is the space of complex functions on words, with standard basis vectors $e_a$ (the indicator function of the word $a$), so that $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$. The group $S_n$ acts on $W_{n,d}$ by permuting positions, $(\rho_{n,d}(g)x)(a)=x(a\circ g)$; equivalently $\rho_{n,d}(g)e_a=e_{a\circ g^{-1}}$. For a subgroup $G\le S_n$ and a word $a$, $\operatorname{alt}_G(a)=\sum_{g\in G}\operatorname{sgn}(g)\,\rho_{n,d}(g)\,e_a$ is the signed alternation of $e_a$ over $G$, and for a map $f$ from $[n]$ to any set, $\operatorname{Fib}(f)=\{g\in S_n: f\circ g=f\}$ is its fiber group.
--
--   A tableau of a Young diagram $\mu$ is a bijection $t$ from positions to the cells $(i,j)$ of $\mu$ (row $i$, column $j$); its row word $r_t$ records the row index of each cell and its polytabloid is $e_t=\operatorname{alt}_{C_t}(r_t)$, where $C_t$ is the group of column-preserving position permutations. For $m\in\mathbb{N}$ the staircase diagram is $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$, with $N_m=m(m+1)/2$ cells and $m$ rows, and $T_m:[N_m]\to\delta_m$ is its canonical tableau (the fixed enumeration used in the target statement), with transpose $T'_m=\tau\circ T_m$, $\tau(i,j)=(j,i)$. Fix $h,s\in\mathbb{N}$, put $N=N_{h+s}$, $T=T_{h+s}$, and let $H_{h,s}=\{i\in[N]: T(i)\in\delta_h\}$ be the high positions. As in the rotation construction for the staircase, $p_R=T^{-1}\circ R_{h,s}\circ T$ and $p_K=T^{-1}\circ K_{h,s}\circ T$, where $R_{h,s}$ fixes the rows $i\ge h$ of $\delta_{h+s}$ and rotates each row $i<h$ cyclically by $s$ places, and $K_{h,s}=\tau\circ R_{h,s}\circ\tau$ does the same to columns. The file introduces:
--
--   1. **High positions.** The bijection $H_{h,s}\to[N_h]$, $i\mapsto T_h^{-1}(T(i))$: a cell of $\delta_{h+s}$ with $i+j<h$ is a cell of $\delta_h$.
--   2. **Band size and the cut.** $b_{h,s}=|[N]\setminus H_{h,s}|$, the number of band cells, and the bijection $\varepsilon_{h,s}:[N]\to[N_h]\sqcup[b_{h,s}]$ sending high positions to the left summand by item 1 and the remaining positions to the right summand by a fixed enumeration. A position is sent to the left summand exactly when it is high.
--   3. **Band tableau.** $\beta_{h,s}:[b_{h,s}]\to\delta_{h+s}$, $k\mapsto T(\varepsilon_{h,s}^{-1}(k))$. Every band cell $(i,j)$ satisfies $h\le i+j<h+s$, and $\beta_{h,s}$ is a bijection
--   $$
--   [b_{h,s}]\ \cong\ \{(i,j)\in\mathbb{N}^2:\ h\le i+j<h+s\}.
--   $$
--   The band row group and band column group are $\operatorname{Fib}(\mathrm{row}\circ\beta_{h,s})$ and $\operatorname{Fib}(\mathrm{col}\circ\beta_{h,s})$ in $S_{b_{h,s}}$.
--   4. **Letter shift and letter lifts.** The shift $\sigma_{h,s}:[h]\to[h+s]$, $a\mapsto a+s$; and for a map $f:[d]\to[e]$ the intertwiner $\Lambda_f:W_{n,d}\to W_{n,e}$ with $\Lambda_f\,e_a=e_{f\circ a}$, that is, the tensor power of the $0/1$ matrix $L(a,b)=[f(a)=b]$.
--   5. **Band words.** With $(\cdot)^{(2)}$ denoting restriction of a word on $[N]$ to the band positions (read through $\varepsilon_{h,s}$),
--   $$
--   u^{\mathrm{row}}_{h,s}=\operatorname{alt}_{\operatorname{Fib}(\mathrm{row}\circ\beta_{h,s})}\big((r_{T'}\circ p_R)^{(2)}\big),\qquad
--   u^{\mathrm{col}}_{h,s}=\operatorname{alt}_{\operatorname{Fib}(\mathrm{col}\circ\beta_{h,s})}\big((r_{T}\circ p_K)^{(2)}\big),
--   $$
--   both in $W_{b_{h,s},\,h+s}$; here $r_{T'}\circ p_R$ gives the column index of $R_{h,s}(T(i))$ and $r_T\circ p_K$ the row index of $K_{h,s}(T(i))$.
--   6. **The width-two band as a lattice path.** For $s=2$, the bijection
--   $$
--   \{0,1,\dots,2h+2\}\ \to\ \{(i,j):\ h\le i+j<h+2\},\qquad k\mapsto\Big(h+1-\big\lfloor\tfrac{k+1}{2}\big\rfloor,\ \big\lfloor\tfrac{k}{2}\big\rfloor\Big),
--   $$
--   with inverse $(i,j)\mapsto h+1-i+j$. It lists the $2h+3$ band cells as the path $(h+1,0),(h,0),(h,1),(h-1,1),(h-1,2),\dots,(0,h+1)$, from the single cell of the bottom row to the single cell of the last column; composing with $\beta_{h,2}^{-1}$ gives a bijection $\{0,\dots,2h+2\}\cong[b_{h,2}]$.
--
--   In the surrounding development these objects factor the two layers of the cut staircase word, namely
--   $$
--   \kappa^{\mathrm{row}}_{h,s}=\operatorname{alt}_{C_{T'}\cap\operatorname{Stab}(H_{h,s})}\big(r_{T'}\circ p_R\big),\qquad \kappa^{\mathrm{col}}_{h,s}=\operatorname{alt}_{C_{T}\cap\operatorname{Stab}(H_{h,s})}\big(r_{T}\circ p_K\big),
--   $$
--   where $\operatorname{Stab}(H_{h,s})$ is the setwise stabilizer of the high positions (the position-wise tensor product of these two layers is the projection of the staircase generator onto pair words whose two components are high, i.e. $\ge s$, at exactly the same positions). The factorizations read $\kappa^{\mathrm{row}}_{h,s}=\Lambda_{\sigma_{h,s}}(e_{T'_h})\boxtimes u^{\mathrm{row}}_{h,s}$ and $\kappa^{\mathrm{col}}_{h,s}=\Lambda_{\sigma_{h,s}}(e_{T_h})\boxtimes u^{\mathrm{col}}_{h,s}$, where $(x\boxtimes y)(w)=x(w^{(1)})\,y(w^{(2)})$ multiplies the values on the high and band restrictions of $w$ (both read through $\varepsilon_{h,s}$). Thus, after projection, the staircase generator for $\delta_{h+s}$ splits into a letter-shifted copy of the generator for $\delta_h$ and an explicit band factor, which is the engine of an induction on the staircase size; the path enumeration of item 6 makes the width-two band factor computable.
--
--   **Formalization Note** The objects are `highPositionsEquiv`, `bandSize` (a `Nat.card`), `cutPositions` (with `cutPositions_high`), `bandTableau` (with `bandTableau_bounds`), `bandRowGroup`, `bandColumnGroup`, `highLetter`, `letterLift` (defined through the tensor-power map `wordMap`), `bandRowWord`, `bandColumnWord`, `bandCellsEquiv`, `pathCellsEquiv` and `bandPathEquiv`. The enumeration of band positions in `cutPositions` is a noncanonical choice made with `Fintype.equivFinOfCardEq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandFactorization.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandFactorization.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def highPositionsEquiv (h s : ℕ) :
    {i : Fin (staircase (h+s)).card // stairHigh h s i} ≃ Fin (staircase h).card where
  toFun i := (stairTableau h).symm ⟨(stairTableau (h+s) i.val).val, mem_staircase.mpr i.property⟩
  invFun j := ⟨(stairTableau (h+s)).symm ⟨(stairTableau h j).val, by
    apply mem_staircase.mpr
    have := mem_staircase.mp (stairTableau h j).property
    omega⟩, by
      change ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.1 +
        ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.2 < h
      simp only [Equiv.apply_symm_apply]
      exact mem_staircase.mp (stairTableau h j).property⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by simp

abbrev bandSize (h s : ℕ) := Nat.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i}

def cutPositions (h s : ℕ) :
    Fin (staircase (h+s)).card ≃ Fin (staircase h).card ⊕ Fin (bandSize h s) := by
  classical
  exact (Equiv.sumCompl (stairHigh h s)).symm.trans
    (Equiv.sumCongr (highPositionsEquiv h s) (Fintype.equivFinOfCardEq (show Fintype.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i} = bandSize h s from Fintype.card_eq_nat_card)))

lemma cutPositions_high (h s : ℕ) (i : Fin (staircase (h+s)).card) :
    (cutPositions h s i).isLeft = true ↔ stairHigh h s i := by
  classical
  by_cases hi : stairHigh h s i <;> simp [cutPositions, Equiv.sumCompl, Equiv.sumCongr, hi]

def bandTableau (h s : ℕ) (j : Fin (bandSize h s)) : (staircase (h+s)).cells :=
  stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))

def bandRowGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.1)
def bandColumnGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.2)

def highLetter (h s : ℕ) : Fin ((staircase h).colLen 0) → Fin ((staircase (h+s)).colLen 0) :=
  fun a => ⟨a.val+s, by have := a.isLt; simp only [staircase_colLen, Nat.sub_zero] at *; omega⟩

def letterLift {n d e : ℕ} (f : Fin d → Fin e) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) :=
  wordMap (fun a b => if f a = b then 1 else 0)

def bandRowWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandRowGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)))

def bandColumnWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandColumnGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)))

/- The first-layer exact band factorization, including the high-letter shift. -/
/- The second-layer exact band factorization. -/
lemma bandTableau_bounds (h s : ℕ) (j : Fin (bandSize h s)) :
    h ≤ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 ∧
      (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h+s := by
  refine ⟨?_,mem_staircase.mp (bandTableau h s j).property⟩
  have hh := cutPositions_high h s ((cutPositions h s).symm (Sum.inr j))
  simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, false_iff] at hh
  change ¬ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h at hh
  omega

def bandCellsEquiv (h s : ℕ) : Fin (bandSize h s) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} :=
  Equiv.ofBijective (fun j => ⟨(bandTableau h s j).val,bandTableau_bounds h s j⟩) (by
    constructor
    · intro i j hij
      have hh : bandTableau h s i = bandTableau h s j := Subtype.ext (congrArg (fun c : {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} => c.val) hij)
      exact Sum.inr.inj ((cutPositions h s).symm.injective ((stairTableau (h+s)).injective hh))
    · intro c
      let x : (staircase (h+s)).cells := ⟨c.val,mem_staircase.mpr c.property.2⟩
      let i := (stairTableau (h+s)).symm x
      have hi : ¬ stairHigh h s i := by
        change ¬ (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.1 +
          (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.2 < h
        simp only [Equiv.apply_symm_apply]
        exact Nat.not_lt.mpr c.property.1
      have he := cutPositions_high h s i
      cases hp : cutPositions h s i with
      | inl j => simp only [hp, Sum.isLeft_inl, true_iff] at he; exact False.elim (hi he)
      | inr j =>
        refine ⟨j, ?_⟩
        apply Subtype.ext
        have hj : (cutPositions h s).symm (Sum.inr j) = i := by rw [← hp,Equiv.symm_apply_apply]
        change (stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))).val = c.val
        rw [hj]
        exact congrArg Subtype.val ((stairTableau (h+s)).apply_symm_apply x))

def pathCellsEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+2} where
  toFun k := ⟨(h+1-(k.val+1)/2,k.val/2), by have := k.isLt; omega⟩
  invFun c := ⟨h+1-c.val.1+c.val.2, by have := c.property; omega⟩
  left_inv k := by apply Fin.ext; dsimp; have := k.isLt; omega
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> have := c.property <;> omega

/- The exact path order, starting at the bottom row singleton and ending
at the rightmost column singleton. -/
def bandPathEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃ Fin (bandSize h 2) :=
  (pathCellsEquiv h).trans (bandCellsEquiv h 2).symm

end Saxl

end

end OAI


