-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
-- name    : OAI_Probability_ThorpShuffle_Irreducibility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:54:31.459861+00:00
-- url     : https://prove2.me/theorems/ffedafda-45f1-46e8-962a-02183d82f4bb
-- title:
--   Standard Young tableaux and linear independence of standard polytabloids
-- statement:
--   This module shows that the polytabloids of standard Young tableaux are linearly independent, so that the dimension of a Specht module is at least the number of standard tableaux of its shape.
--
--   **Setting.** Let $n\in\mathbb{N}$, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ the permutation group of $[n]$. A Young diagram $D$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) such that $(i,j)\in D$, $i'\le i$ and $j'\le j$ imply $(i',j')\in D$; its cells are ordered componentwise, $(i',j')\le(i,j)$ iff $i'\le i$ and $j'\le j$. A bijection $t:[n]\to D$ is *standard* if $t^{-1}:D\to[n]$ is strictly increasing, i.e. the labels increase strictly along each row and down each column. Write $r_t(x)$ and $c_t(x)$ for the row and the column of $t(x)$.
--
--   As in the construction of Specht modules: a tabloid of $r_t$ is a rearrangement $r_t\circ g$ with $g\in S_n$, and $S_n$ acts on tabloids by $(g\cdot f)(x)=f(g^{-1}x)$; $M_t$ is the complex vector space with basis $\delta_f$ indexed by tabloids, with $(\rho(g)v)(f)=v(g^{-1}\cdot f)$; $C_t$ is the group of permutations preserving every column of $t$; $\{t\}=r_t$ is the base tabloid; the polytabloid is $e_t=\sum_{h\in C_t}\operatorname{sgn}(h)\,\delta_{h\cdot\{t\}}$; and the Specht module is $S^D_t=\operatorname{span}_{\mathbb{C}}\{\rho(g)e_t: g\in S_n\}$. For $g\in S_n$ let $g\cdot t$ be the bijection $x\mapsto t(g^{-1}x)$, obtained from $t$ by replacing each entry $x$ by $g(x)$; its tabloid is $g\cdot\{t\}=r_t\circ g^{-1}$. Functions $[n]\to\mathbb{N}$ are compared lexicographically, $\le_{\mathrm{lex}}$, at the first position where they differ.
--
--   The module proves:
--
--   1. *Standard tableaux.* Let $t$ be standard. If $x,y$ lie in the same row of $t$, then $x<y$ iff $c_t(x)<c_t(y)$; if they lie in the same column, then $x<y$ iff $r_t(x)<r_t(y)$. The column of $t(x)$ equals the number of $y<x$ in the same row as $x$. Consequently, two standard bijections $t,u:[n]\to D$ with $r_t=r_u$ are equal.
--   2. *Triangularity criterion.* Let $I,X$ be finite sets, $K$ a linearly ordered set, $e_i\in\mathbb{C}^X$ for $i\in I$, and $b:I\to X$, $k:X\to K$ with $k\circ b$ injective. If $e_i(b_i)\ne 0$ for every $i$, and $e_i(x)\ne 0$ implies $k(b_i)\le k(x)$, then $(e_i)_{i\in I}$ is linearly independent over $\mathbb{C}$.
--   3. *Leading words.* If $t$ is standard, then $r_t\le_{\mathrm{lex}}r_t\circ h^{-1}$ for every $h\in C_t$.
--   4. *Translated polytabloids.* Let $\mathrm{SP}(D,t)=\{g\in S_n:\ g\cdot t\text{ is standard}\}$. For every $g\in S_n$, $(\rho(g)e_t)(g\cdot\{t\})=1$. For $g\in\mathrm{SP}(D,t)$, $(\rho(g)e_t)(f)\ne 0$ implies $g\cdot\{t\}\le_{\mathrm{lex}}f$. The map $g\mapsto g\cdot\{t\}$ is injective on $\mathrm{SP}(D,t)$.
--   5. *Independence and the dimension bound.* The vectors $\rho(g)e_t$, $g\in\mathrm{SP}(D,t)$, are linearly independent in $M_t$. They lie in $S^D_t$, and therefore
--   $$
--   \#\{g\in S_n:\ g\cdot t\text{ is standard}\}\le\dim_{\mathbb{C}}S^D_t .
--   $$
--
--   Since $g\mapsto g\cdot t$ is a bijection from $S_n$ onto the set of all bijections $[n]\to D$, the left-hand side is the number of standard Young tableaux of shape $D$. This inequality converts combinatorial lower bounds on the number of standard tableaux into lower bounds on Specht dimensions, which is how the degrees $\deg(p)$ are estimated in this project.
--
--   **Formalization Note** `Standard t` is `StrictMono t.symm` for `t : Fin n ≃ Cells D`. `movedTableau D t g` is `g⁻¹.trans t`, `StandardPerm D t` is the subtype of permutations `g` with `Standard (movedTableau D t g)`, `movedWord D t g` is the tabloid `g • baseTabloid (tableauRow D t)`, and `orbitVector D t g` is $\rho(g)e_t$ regarded as an element of the Specht submodule. Lexicographic comparison uses `toLex` on `Fin n → ℕ`. The general criterion of item 2 is `independent_of_leading`; the main results are `standard_polytabloids_independent` and `standardPerm_card_le_degree`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Irreducibility.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Irreducibility.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids

namespace OAI

universe uI uX uK

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable {n : ℕ} {D : YoungDiagram}

def Standard (t : Fin n ≃ Cells D) : Prop := StrictMono t.symm

lemma standard_row_lt_iff (t : Fin n ≃ Cells D) (ht : Standard t) (x y : Fin n)
    (hr : (t x).val.1 = (t y).val.1) : x < y ↔ (t x).val.2 < (t y).val.2 := by
  constructor
  · intro hxy
    by_contra hn
    have hc : (t y).val.2 ≤ (t x).val.2 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨by omega, hc⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hc
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨by omega, hc.le⟩, ?_⟩
      intro hh
      exact not_le_of_gt hc hh.2
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma standard_col_lt_iff (t : Fin n ≃ Cells D) (ht : Standard t) (x y : Fin n)
    (hc : (t x).val.2 = (t y).val.2) : x < y ↔ (t x).val.1 < (t y).val.1 := by
  constructor
  · intro hxy
    by_contra hn
    have hr : (t y).val.1 ≤ (t x).val.1 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨hr, by omega⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hr
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨hr.le, by omega⟩, ?_⟩
      intro hh
      exact not_le_of_gt hr hh.1
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma column_eq_rowRank (t : Fin n ≃ Cells D) (ht : Standard t) (x : Fin n) :
    Fintype.card {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} = (t x).val.2 := by
  let e : {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} ≃ Fin ((t x).val.2) := {
    toFun := fun y => ⟨(t y.val).val.2, (standard_row_lt_iff t ht y.val x y.property.2).mp y.property.1⟩
    invFun := fun j => ⟨t.symm ⟨((t x).val.1, j), D.up_left_mem le_rfl j.isLt.le (t x).property⟩, by
      constructor
      · apply (standard_row_lt_iff t ht _ x (by simp)).mpr
        simpa only [Equiv.apply_symm_apply] using j.isLt
      · simp⟩
    left_inv := by
      intro y
      apply Subtype.ext
      apply t.injective
      simp only [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact Prod.ext y.property.2.symm rfl
    right_inv := by intro j; apply Fin.ext; simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma standard_eq_of_rows (t u : Fin n ≃ Cells D) (ht : Standard t) (hu : Standard u)
    (hr : ∀ x, (t x).val.1 = (u x).val.1) : t = u := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext (hr x)
  rw [← column_eq_rowRank t ht x, ← column_eq_rowRank u hu x]
  exact Fintype.card_congr ((Equiv.refl (Fin n)).subtypeEquiv (fun y => by simp only [Equiv.refl_apply, hr]))

end Thorp.Young

namespace Thorp.Specht
open scoped Classical

theorem independent_of_leading {I : Type uI} {X : Type uX} {K : Type uK} [Fintype I] [Fintype X] [LinearOrder K]
    (e : I → EuclideanSpace ℂ X) (b : I → X) (key : X → K)
    (hinj : Function.Injective (key ∘ b)) (hdiag : ∀ i, e i (b i) ≠ 0)
    (htri : ∀ i x, e i x ≠ 0 → key (b i) ≤ key x) : LinearIndependent ℂ e := by
  let : LinearOrder I := LinearOrder.lift' (key ∘ b) hinj
  rw [linearIndependent_iff']
  intro s a ha i hi
  by_contra hai
  let S := s.filter fun j => a j ≠ 0
  have hs : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  let j := S.min' hs
  have hj : j ∈ S := S.min'_mem hs
  have hj' : j ∈ s := (Finset.mem_filter.mp hj).1
  have haz : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hval := congrArg (fun v : EuclideanSpace ℂ X => v (b j)) ha
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hval
  rw [Finset.sum_eq_single_of_mem j hj'] at hval
  · exact (mul_ne_zero haz (hdiag j)) hval
  · intro k hk hkj
    by_cases hak : a k = 0
    · simp [hak]
    have hks : k ∈ S := Finset.mem_filter.mpr ⟨hk, hak⟩
    have hjk : j ≤ k := S.min'_le k hks
    have hjk' : j < k := lt_of_le_of_ne hjk (Ne.symm hkj)
    have hzero : e k (b j) = 0 := by
      by_contra hn
      have hh := htri k (b j) hn
      exact not_le_of_gt hjk' hh
    simp [hzero]

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical

variable {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Thorp.Young.Cells D)

lemma column_word_le (ht : Thorp.Young.Standard t) (c : fiberGroup (tableauCol D t)) :
    toLex (tableauRow D t) ≤ toLex (fun x => tableauRow D t (c.val⁻¹ x)) := by
  by_cases hc : c.val = 1
  · simp [hc]
  let S := Finset.univ.filter fun x : Fin n => c.val⁻¹ x ≠ x
  have hs : S.Nonempty := by
    by_contra hn
    apply hc
    have he : c.val⁻¹ = 1 := by
      apply Equiv.ext
      intro x
      by_contra hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    exact inv_eq_one.mp he
  let x := S.min' hs
  have hx : c.val⁻¹ x ≠ x := (Finset.mem_filter.mp (S.min'_mem hs)).2
  have hbefore (y : Fin n) (hy : y < x) : c.val⁻¹ y = y := by
    by_contra hn
    have hm : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hn⟩
    exact not_le_of_gt hy (S.min'_le y hm)
  have hlt : x < c.val⁻¹ x := by
    apply lt_of_le_of_ne
    · by_contra hn
      have hh := hbefore (c.val⁻¹ x) (lt_of_not_ge hn)
      exact hx (c.val.symm.injective hh)
    · exact Ne.symm hx
  have hcol : (t x).val.2 = (t (c.val⁻¹ x)).val.2 := by
    have hh := c.property (c.val⁻¹ x)
    simpa only [tableauCol, perm_apply_inv] using hh
  have hrow := (Thorp.Young.standard_col_lt_iff t ht x (c.val⁻¹ x) hcol).mp hlt
  apply le_of_lt
  change Pi.Lex (· < ·) (· < ·) (tableauRow D t) (fun y => tableauRow D t (c.val⁻¹ y))
  exact ⟨x, fun y hy => congrArg (tableauRow D t) (hbefore y hy).symm, hrow⟩

def movedTableau (g : Equiv.Perm (Fin n)) : Fin n ≃ Thorp.Young.Cells D := (g⁻¹).trans t

def StandardPerm := {g : Equiv.Perm (Fin n) // Thorp.Young.Standard (movedTableau D t g)}

instance : Fintype (StandardPerm D t) := inferInstanceAs (Fintype {g : Equiv.Perm (Fin n) // Thorp.Young.Standard (movedTableau D t g)})

def movedWord (g : Equiv.Perm (Fin n)) : Tabloid (tableauRow D t) := g • baseTabloid (tableauRow D t)

lemma moved_diag (g : Equiv.Perm (Fin n)) :
    tabloidRep D t g (polytabloid D t) (movedWord D t g) = 1 := by
  change polytabloid D t (g⁻¹ • (g • baseTabloid (tableauRow D t))) = 1
  rw [inv_smul_smul]
  exact polytabloid_diag D t

lemma moved_leading (g : Equiv.Perm (Fin n)) (hg : Thorp.Young.Standard (movedTableau D t g))
    (f : Tabloid (tableauRow D t)) (hf : tabloidRep D t g (polytabloid D t) f ≠ 0) :
    toLex (movedWord D t g).val ≤ toLex f.val := by
  obtain ⟨h, hh⟩ := polytabloid_support D t (g⁻¹ • f) hf
  have he : f = (g * h.val) • baseTabloid (tableauRow D t) := by
    rw [mul_smul]
    exact inv_smul_eq_iff.mp hh
  let c : Equiv.Perm (Fin n) := g * h.val * g⁻¹
  have hc : c ∈ fiberGroup (tableauCol D (movedTableau D t g)) := by
    intro x
    change (t (g⁻¹ (g (h.val (g⁻¹ x))))).val.2 = (t (g⁻¹ x)).val.2
    rw [perm_inv_apply]
    exact h.property (g⁻¹ x)
  have hcword : c • movedWord D t g = f := by
    rw [he]
    change (g * h.val * g⁻¹) • (g • baseTabloid _) = (g * h.val) • baseTabloid _
    simp only [← mul_smul, inv_mul_cancel_right]
  have hw := column_word_le D (movedTableau D t g) hg ⟨c, hc⟩
  change toLex (movedWord D t g).val ≤ toLex (c • movedWord D t g).val at hw
  rw [hcword] at hw
  exact hw

lemma standardWord_injective : Function.Injective (fun g : StandardPerm D t => toLex (movedWord D t g.val).val) := by
  intro g h he
  have hr : ∀ x, (movedTableau D t g.val x).val.1 = (movedTableau D t h.val x).val.1 :=
    fun x => congrFun he x
  have ht := Thorp.Young.standard_eq_of_rows _ _ g.property h.property hr
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro x
  apply t.injective
  exact congrArg (fun z : Fin n ≃ Thorp.Young.Cells D => z x) ht

theorem standard_polytabloids_independent :
    LinearIndependent ℂ (fun g : StandardPerm D t => tabloidRep D t g.val (polytabloid D t)) := by
  apply independent_of_leading _ (fun g => movedWord D t g.val) (fun f => toLex f.val)
    (standardWord_injective D t)
  · intro i
    rw [moved_diag]
    exact one_ne_zero
  · intro i f hf
    exact moved_leading D t i.val i.property f hf

def orbitVector (g : Equiv.Perm (Fin n)) : (module D t).toSubmodule :=
  ⟨tabloidRep D t g (polytabloid D t),
    (module D t).apply_mem_toSubmodule g (self_mem_cyclic _ _)⟩

theorem standardPerm_card_le_degree :
    Fintype.card (StandardPerm D t) ≤ Module.finrank ℂ (module D t).toSubmodule := by
  have hi : LinearIndependent ℂ (fun g : StandardPerm D t => orbitVector D t g.val) :=
    LinearIndependent.of_comp (module D t).toSubmodule.subtype (standard_polytabloids_independent D t)
  exact hi.fintype_card_le_finrank

end Thorp.Specht

end

end OAI


