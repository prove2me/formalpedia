-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
-- name    : OAI_Analysis_DiamondDistortion_CoordinateDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:15:30.9285+00:00
-- url     : https://prove2.me/theorems/1619a63a-24ef-4067-a7d1-1d3bd5b41452
-- title:
--   Duals of coordinate completions: Hilbertian blocks and density of the coordinate functionals
-- statement:
--   This file studies the full dual of a Banach space obtained by completing a coordinate norm, and gives a block condition under which finite combinations of the coordinate functionals are dense in that dual.
--
--   **Setting.** Let $\iota$ be an index set and $c_{00}(\iota)$ the space of finitely supported functions $\iota\to\mathbb{R}$, with point masses $\delta_i$. A *coordinate norm datum* $A$ is a seminorm $\|\cdot\|_A$ on $c_{00}(\iota)$ such that for each $i\in\iota$ there is a constant $C_i$ with $|v_i|\le C_i\|v\|_A$ for all $v$. Then $\|\cdot\|_A$ is a norm; $X_A$ denotes the completion of $(c_{00}(\iota),\|\cdot\|_A)$, vectors $p\in c_{00}(\iota)$ are identified with their images in $X_A$, $e_i\in X_A$ is the image of $\delta_i$, and $e_i^*$ is the continuous extension of the coordinate functional $v\mapsto v_i$ to $X_A$.
--
--   1. **The dual.** $X_A^*$ is the space of all continuous linear functionals on $X_A$, with the operator norm.
--   2. **Coordinate dual embedding.** A vector $a\in c_{00}(\iota)$ is sent to the functional $\sum_i a_i e_i^*\in X_A^*$, so that $\bigl(\sum_ia_ie_i^*\bigr)(v)=\sum_ia_iv_i$ for $v\in c_{00}(\iota)$.
--   3. **Hilbertian blocks.** Let $c:\iota\to\kappa$ assign a block (colour) to each index. For $p\in c_{00}(\iota)$ write $c(\operatorname{supp}p)$ for the set of colours of its support and $p|_C$ for its restriction to $\{i:c(i)\in C\}$. The datum $A$ has *Hilbertian blocks* along $c$ if the following four conditions hold:
--      - (orthogonality) $\|p+q\|_A^2\le\|p\|_A^2+\|q\|_A^2$ whenever $c(\operatorname{supp}p)\cap c(\operatorname{supp}q)=\emptyset$;
--      - (contractive restrictions) $\|p|_C\|_A\le\|p\|_A$ for every $p$ and every set $C\subseteq\kappa$;
--      - (upper estimate) for every finite $C\subseteq\kappa$ there is $B>0$ with $\|p\|_A^2\le B\sum_ip_i^2$ for all $p$ with $c(\operatorname{supp}p)\subseteq C$;
--      - (lower estimate) for every finite $C\subseteq\kappa$ there is $L>0$ with $\sum_ip_i^2\le L\|p\|_A^2$ for all $p$ with $c(\operatorname{supp}p)\subseteq C$.
--
--      The constants $B$ and $L$ may depend on $C$; no uniform bound is required.
--   4. **Finite arrays and block coefficients.** For a finite set $S\subseteq\iota$ and $a:\iota\to\mathbb{R}$, the array $a|_S=\sum_{i\in S}a_i\delta_i\in c_{00}(\iota)$ agrees with $a$ on $S$ and vanishes elsewhere. For $x\in X_A^*$ and a finite set of colours $C$, the block coefficients of $x$ are $x^C_i=x(e_i)$ if $c(i)\in C$ and $x^C_i=0$ otherwise.
--
--   The file proves the following facts. Using only the orthogonality condition: for every $x\in X_A^*$ and $\varepsilon>0$ there is a finite set of colours $C$ such that $|x(p)|\le\varepsilon\|p\|_A$ for every $p\in c_{00}(\iota)$ none of whose support colours lies in $C$. If $A$ has Hilbertian blocks along $c$, then for every $x$ and finite $C$ the block coefficients have bounded energy, i.e. there is $M$ with $\sum_{i\in S}(x^C_i)^2\le M$ for all finite $S\subseteq\iota$; and every functional is approximated by finite coordinate combinations: for every $x\in X_A^*$ and $\varepsilon>0$ there is $a\in c_{00}(\iota)$ with
--   $$\Bigl\|x-\sum_{i}a_i\,e_i^*\Bigr\|_{X_A^*}<\varepsilon.$$
--   Consequently, if $A$ has Hilbertian blocks along some $c$ and $\iota$ is countable, then $X_A^*$ is separable. An elementary lemma used along the way states that if $a:\iota\to\mathbb{R}$ satisfies $\sum_{i\in S}a_i^2\le M$ for all finite $S$, then for each $\delta>0$ there is a finite $S$ with $\sum_{i\in U}a_i^2<\delta$ for every finite $U$ disjoint from $S$.
--
--   The criterion is designed for norms on a forest that are outer $\ell^2$ sums over the components: distinct components are orthogonal blocks, and on finitely many components the norm is equivalent to the Euclidean norm. It identifies the dual of such a completion with the closure of the span of the coordinate functionals and yields its separability.
--
--   **Formalization Note** `CoordinateCompletion.Data.Dual` is `StrongDual ℝ A.Space`; the embedding is `dualEmbedding = Finsupp.linearCombination ℝ A.coordinate`; the block condition is the structure `HilbertBlocks c` with fields `orthogonal`, `contractive`, `upper` and `lower` (restriction is `Finsupp.filter`). Arrays are `FiniteCoordinates.array` and block coefficients are `coefficients c C x`. The results are `small_color_tail` (with its one-sided form `small_color_tail_upper`), `coefficients_bounded`, `dual_approximation`, `dual_separable` (assuming `Countable ι`) and `FiniteCoordinates.square_tails`; `pairing` and `pairing_array` expand $x(p)=\sum_i p_i\,x(e_i)$. The private lemmas `ite_eq_left` and `ite_eq_right` are local aliases.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/CoordinateDual.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/CoordinateDual.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace CoordinateCompletion.Data
variable {ι κ : Type*} (A : CoordinateCompletion.Data ι)
abbrev Dual := StrongDual ℝ A.Space

def dualEmbedding : (ι →₀ ℝ) →ₗ[ℝ] A.Dual :=
  Finsupp.linearCombination ℝ A.coordinate
lemma embedding_sum (v : ι →₀ ℝ) : A.embedding v=∑ i ∈ v.support,v i • A.unit i := by
  simp only [unit,← map_smul,← map_sum]
  congr 1
  ext i
  simp [Finsupp.single_apply,Finset.sum_ite_eq']
lemma pairing (x : A.Dual) (v : ι →₀ ℝ) :
    x (A.embedding v)=∑ i ∈ v.support,v i*x (A.unit i) := by
  rw [embedding_sum,map_sum]
  simp only [map_smul,smul_eq_mul]

lemma small_color_tail_upper (c : ι → κ)
    (hblock : ∀ p q : ι →₀ ℝ,Disjoint (p.support.image c) (q.support.image c) →
      (A.seminorm (p+q))^2 ≤ (A.seminorm p)^2+(A.seminorm q)^2)
    (x : A.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      x (A.embedding p) ≤ ε*A.seminorm p := by
  classical
  by_contra hn
  push Not at hn
  have hchoose (C : Finset κ) : ∃ q : ι →₀ ℝ,
      (∀ v ∈ q.support,c v ∉ C) ∧ A.seminorm q=1 ∧ ε < x (A.embedding q) := by
    obtain ⟨p,hout,hval⟩ := hn C
    have hpn0 : A.seminorm p ≠ 0 := by
      intro he
      have hp0 := A.separates p he
      simp only [hp0,map_zero,mul_zero,lt_self_iff_false] at hval
    have hpn : 0 < A.seminorm p := lt_of_le_of_ne (apply_nonneg _ _) hpn0.symm
    let q := (A.seminorm p)⁻¹ • p
    refine ⟨q, ?_, ?_, ?_⟩
    · intro v hv
      apply hout v
      apply Finsupp.mem_support_iff.mpr
      intro hpv
      have hqv : q v=0 := by simp [q,Finsupp.smul_apply,hpv]
      exact (Finsupp.mem_support_iff.mp hv) hqv
    · simp only [q,map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpn)]
      exact inv_mul_cancel₀ hpn0
    · simp only [q,map_smul,smul_eq_mul]
      rw [inv_mul_eq_div]
      exact (lt_div_iff₀ hpn).mpr hval
  have hblocks : ∀ n : ℕ, ∃ p : ι →₀ ℝ,
      (A.seminorm p)^2 ≤ (n : ℝ) ∧ (n : ℝ)*ε ≤ x (A.embedding p) := by
    intro n
    induction n with
    | zero => exact ⟨0,by simp only [map_zero,zero_pow (by decide : 2 ≠ 0),Nat.cast_zero,le_refl],
        by simp only [map_zero,Nat.cast_zero,zero_mul,le_refl]⟩
    | succ n ih =>
      obtain ⟨p,hpn,hpx⟩ := ih
      obtain ⟨q,hqout,hqn,hqx⟩ := hchoose (p.support.image c)
      have hd : Disjoint (p.support.image c) (q.support.image c) := by
        apply Finset.disjoint_left.mpr
        intro a hap haq
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp haq
        exact hqout v hv hap
      refine ⟨p+q, ?_, ?_⟩
      · have h := hblock p q hd
        rw [hqn] at h
        push_cast
        nlinarith
      · simp only [map_add,Nat.cast_add,Nat.cast_one]
        nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt (‖x‖^2/ε^2)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg (sq_nonneg _) (sq_nonneg _)) hn
  have hnε : ‖x‖^2 < (n:ℝ)*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hn
  obtain ⟨p,hpn,hpx⟩ := hblocks n
  have hxb : x (A.embedding p) ≤ ‖x‖*A.seminorm p := by
    calc
      _ ≤ ‖x (A.embedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖*‖A.embedding p‖ := x.le_opNorm _
      _ = _ := by rw [A.norm_embedding]
  have hprod : (n:ℝ)*ε ≤ ‖x‖*A.seminorm p := hpx.trans hxb
  have hsquare := (sq_le_sq₀ (mul_nonneg hn0.le hε.le)
    (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2 hprod
  have hmul := mul_le_mul_of_nonneg_left hpn (sq_nonneg ‖x‖)
  have hcontra := mul_pos hn0 (sub_pos.mpr hnε)
  nlinarith

lemma small_color_tail (c : ι → κ)
    (hblock : ∀ p q : ι →₀ ℝ,Disjoint (p.support.image c) (q.support.image c) →
      (A.seminorm (p+q))^2 ≤ (A.seminorm p)^2+(A.seminorm q)^2)
    (x : A.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      |x (A.embedding p)| ≤ ε*A.seminorm p := by
  obtain ⟨C,hC⟩ := A.small_color_tail_upper c hblock x hε
  refine ⟨C,?_⟩
  intro p hp
  apply abs_le.mpr
  refine ⟨?_,hC p hp⟩
  have h := hC (-p) (by simpa only [Finsupp.support_neg] using hp)
  simp only [map_neg,map_neg_eq_map] at h
  linarith

/-- Orthogonal outer blocks whose finite unions have their actual norm equivalent
    to coordinate ℓ². Constants may depend on the finite union, not globally. -/
structure HilbertBlocks (c : ι → κ) : Prop where
  orthogonal : ∀ p q : ι →₀ ℝ,Disjoint (p.support.image c) (q.support.image c) →
    (A.seminorm (p+q))^2 ≤ (A.seminorm p)^2+(A.seminorm q)^2
  contractive : ∀ p : ι →₀ ℝ,∀ C : Set κ,
    A.seminorm (p.filter (fun i => c i ∈ C)) ≤ A.seminorm p
  upper : ∀ C : Finset κ,∃ B : ℝ,0 < B ∧ ∀ p : ι →₀ ℝ,
    (∀ i ∈ p.support,c i ∈ C) →
    (A.seminorm p)^2 ≤ B*(∑ i ∈ p.support,p i^2)
  lower : ∀ C : Finset κ,∃ L : ℝ,0 < L ∧ ∀ p : ι →₀ ℝ,
    (∀ i ∈ p.support,c i ∈ C) →
    (∑ i ∈ p.support,p i^2) ≤ L*(A.seminorm p)^2

end CoordinateCompletion.Data

namespace FiniteCoordinates
variable {ι : Type*}
def array (S : Finset ι) (a : ι → ℝ) : ι →₀ ℝ := ∑ i ∈ S,a i • Finsupp.single i 1
lemma array_apply (S : Finset ι) (a : ι → ℝ) (i : ι) :
    array S a i=if i ∈ S then a i else 0 := by
  simp [array,Finsupp.single_apply,Finset.sum_ite_eq']
lemma array_support (S : Finset ι) (a : ι → ℝ) : (array S a).support ⊆ S := by
  intro i hi
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hi) (by rw [array_apply,ite_eq_right hn])
lemma array_energy (S : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ (array S a).support,array S a i^2)=∑ i ∈ S,a i^2 := by
  calc
    _ = ∑ i ∈ S,array S a i^2 := by
      apply Finset.sum_subset (array_support S a)
      intro i _ hi
      rw [Finsupp.notMem_support_iff.mp hi]
      norm_num
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [array_apply,ite_eq_left hi]
lemma filter_energy_le (p : ι →₀ ℝ) (Q : ι → Prop) [DecidablePred Q] :
    (∑ i ∈ (p.filter Q).support,(p.filter Q) i^2) ≤ ∑ i ∈ p.support,p i^2 := by
  rw [Finsupp.support_filter]
  calc
    _ = ∑ i ∈ p.support.filter Q,p i^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finsupp.filter_apply,ite_eq_left (Finset.mem_filter.mp hi).2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
lemma square_tails (a : ι → ℝ) {M : ℝ}
    (hM : ∀ S : Finset ι,(∑ i ∈ S,a i^2) ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset ι,∀ U : Finset ι,Disjoint S U → (∑ i ∈ U,a i^2) < δ := by
  let E : Set ℝ := Set.range (fun S : Finset ι => ∑ i ∈ S,a i^2)
  have hEb : BddAbove E := ⟨M,by rintro _ ⟨S,rfl⟩; exact hM S⟩
  have hEn : E.Nonempty := ⟨0,∅,by simp⟩
  obtain ⟨b,⟨S,rfl⟩,hS⟩ := exists_lt_of_lt_csSup hEn (sub_lt_self (sSup E) hδ)
  refine ⟨S,?_⟩
  intro U hU
  have h := le_csSup hEb (show (∑ i ∈ S ∪ U,a i^2) ∈ E from ⟨S ∪ U,rfl⟩)
  rw [Finset.sum_union hU] at h
  linarith
end FiniteCoordinates

namespace CoordinateCompletion.Data
variable {ι κ : Type*} (A : CoordinateCompletion.Data ι)
lemma pairing_array (S : Finset ι) (a : ι → ℝ) (x : A.Dual) :
    x (A.embedding (FiniteCoordinates.array S a))=∑ i ∈ S,a i*x (A.unit i) := by
  simp only [FiniteCoordinates.array,map_sum,map_smul,smul_eq_mul,unit]
lemma dualEmbedding_array (S : Finset ι) (a : ι → ℝ) (p : ι →₀ ℝ) :
    A.dualEmbedding (FiniteCoordinates.array S a) (A.embedding p)=∑ i ∈ S,a i*p i := by
  simp only [FiniteCoordinates.array,map_sum,map_smul]
  change (∑ i ∈ S,a i • A.dualEmbedding (Finsupp.single i 1)) (A.embedding p)=_
  simp only [dualEmbedding,Finsupp.linearCombination_single,one_smul,
    sum_apply,smul_apply,smul_eq_mul,coordinate_embedding]

def coefficients (c : ι → κ) (C : Finset κ) (x : A.Dual) (i : ι) : ℝ :=
  if c i ∈ C then x (A.unit i) else 0
lemma coefficients_bounded (c : ι → κ) (hblocks : A.HilbertBlocks c) (C : Finset κ) (x : A.Dual) :
    ∃ M : ℝ,∀ S : Finset ι,(∑ i ∈ S,A.coefficients c C x i^2) ≤ M := by
  obtain ⟨B,hB,hupper⟩ := hblocks.upper C
  refine ⟨B*‖x‖^2,?_⟩
  intro S
  let a := A.coefficients c C x
  let p := FiniteCoordinates.array S a
  let E := ∑ i ∈ S,a i^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : ∀ i ∈ p.support,c i ∈ C := by
    intro i hi
    by_contra hn
    have he : a i=0 := ite_eq_right hn
    have hh : p i=0 := by rw [FiniteCoordinates.array_apply,he]; split_ifs <;> rfl
    exact (Finsupp.mem_support_iff.mp hi) hh
  have hpn := hupper p hp
  rw [FiniteCoordinates.array_energy] at hpn
  have he : x (A.embedding p)=E := by
    rw [pairing_array]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a,coefficients]
    split_ifs <;> ring
  have hval : E ≤ ‖x‖*A.seminorm p := by
    rw [← he]
    exact (Real.le_norm_self _).trans (by simpa only [norm_embedding] using x.le_opNorm (A.embedding p))
  have hs := (sq_le_sq₀ hE (by positivity : 0 ≤ ‖x‖*A.seminorm p)).mpr hval
  have hm := mul_le_mul_of_nonneg_left hpn (sq_nonneg ‖x‖)
  change E ≤ B*‖x‖^2
  by_contra hn
  have hpos : 0 < E := lt_of_le_of_lt (by positivity) (lt_of_not_ge hn)
  have hc := mul_pos hpos (sub_pos.mpr (lt_of_not_ge hn))
  change (A.seminorm p)^2 ≤ B*E at hpn
  change ‖x‖^2*(A.seminorm p)^2 ≤ ‖x‖^2*(B*E) at hm
  nlinarith only [hs,hm,hc]

lemma dual_approximation (c : ι → κ) (hblocks : A.HilbertBlocks c)
    (x : A.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ι →₀ ℝ,‖x-A.dualEmbedding v‖ < ε := by
  have hε4 : 0 < ε/4 := by positivity
  obtain ⟨C,hC⟩ := A.small_color_tail c hblocks.orthogonal x hε4
  obtain ⟨L,hL,hlower⟩ := hblocks.lower C
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  let t := ε/(4*Real.sqrt L)
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨M,hM⟩ := A.coefficients_bounded c hblocks C x
  obtain ⟨S,hS⟩ := FiniteCoordinates.square_tails (A.coefficients c C x) hM (sq_pos_of_pos ht)
  let H := S.filter (fun i => c i ∈ C)
  let v := FiniteCoordinates.array H (fun i => x (A.unit i))
  refine ⟨v,?_⟩
  have hbound : ‖x-A.dualEmbedding v‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih z =>
      let p := A.array z
      let pc := p.filter (fun i => c i ∈ C)
      let qi := pc.filter (fun i => i ∉ S)
      let qo := p.filter (fun i => c i ∉ C)
      let qh := p.filter (fun i => i ∈ H)
      have hiC : ∀ i ∈ qi.support,c i ∈ C := by
        intro i hi
        rw [Finsupp.support_filter] at hi
        have hh := (Finset.mem_filter.mp hi).1
        rw [Finsupp.support_filter] at hh
        exact (Finset.mem_filter.mp hh).2
      have hiS : Disjoint S qi.support := by
        apply Finset.disjoint_left.mpr
        intro i hi hqi
        rw [Finsupp.support_filter] at hqi
        exact (Finset.mem_filter.mp hqi).2 hi
      have hout : ∀ i ∈ qo.support,c i ∉ C := by
        intro i hi
        rw [Finsupp.support_filter] at hi
        exact (Finset.mem_filter.mp hi).2
      have hpc : A.seminorm pc ≤ A.seminorm p := by
        simpa only [pc,Finset.mem_coe] using hblocks.contractive p (C : Set κ)
      have hpn : 0 ≤ A.seminorm p := apply_nonneg _ _
      have hpcl := hlower pc (by
        intro i hi
        rw [Finsupp.support_filter] at hi
        exact (Finset.mem_filter.mp hi).2)
      have henergy : (∑ i ∈ qi.support,qi i^2) ≤ L*(A.seminorm p)^2 := by
        simpa only [qi] using (FiniteCoordinates.filter_energy_le pc (fun i => i ∉ S)).trans
          (hpcl.trans (mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (apply_nonneg _ _) hpn).mpr hpc) hL.le))
      have hroot : Real.sqrt (∑ i ∈ qi.support,qi i^2) ≤ Real.sqrt L*A.seminorm p := by
        apply (Real.sqrt_le_iff).mpr
        refine ⟨by positivity,?_⟩
        rw [mul_pow,Real.sq_sqrt hL.le]
        exact henergy
      have htail : Real.sqrt (∑ i ∈ qi.support,A.coefficients c C x i^2) ≤ t :=
        (Real.sqrt_le_left ht.le).mpr (hS qi.support hiS).le
      have hei : x (A.embedding qi)=∑ i ∈ qi.support,qi i*A.coefficients c C x i := by
        rw [pairing]
        apply Finset.sum_congr rfl
        intro i hi
        rw [coefficients,ite_eq_left (hiC i hi)]
      have hival : |x (A.embedding qi)| ≤ (ε/4)*A.seminorm p := by
        rw [hei]
        calc
          _ ≤ ∑ i ∈ qi.support,|qi i| * |A.coefficients c C x i| := by
            simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
              (fun i => qi i*A.coefficients c C x i) qi.support
          _ ≤ Real.sqrt (∑ i ∈ qi.support,qi i^2)*Real.sqrt (∑ i ∈ qi.support,A.coefficients c C x i^2) := by
            simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt qi.support
              (fun i => |qi i|) (fun i => |A.coefficients c C x i|)
          _ ≤ (Real.sqrt L*A.seminorm p)*t := mul_le_mul hroot htail (Real.sqrt_nonneg _) (by positivity)
          _ = _ := by dsimp [t]; field_simp [ne_of_gt hsL]
      have hoval : |x (A.embedding qo)| ≤ (ε/4)*A.seminorm p := by
        have hh : A.seminorm qo ≤ A.seminorm p := by
          convert hblocks.contractive p {a | a ∉ C} using 1
          congr 1
          ext i
          simp [qo,Finsupp.filter_apply]
        exact (hC qo hout).trans (mul_le_mul_of_nonneg_left hh hε4.le)
      have hsum : qh+qi+qo=p := by
        ext i
        by_cases hc : c i ∈ C <;> by_cases hs : i ∈ S <;>
          simp [qh,qi,qo,pc,H,hc,hs]
      have hv : A.dualEmbedding v (A.embedding p)=x (A.embedding qh) := by
        rw [dualEmbedding_array]
        have hqh : qh=FiniteCoordinates.array H (fun i => p i) := by
          ext i
          simp [qh,Finsupp.filter_apply,FiniteCoordinates.array_apply]
        rw [hqh,pairing_array]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hd : (x-A.dualEmbedding v) (A.embedding p)=x (A.embedding qi)+x (A.embedding qo) := by
        change x (A.embedding p)-A.dualEmbedding v (A.embedding p)=_
        rw [hv,← hsum,map_add,map_add,map_add,map_add]
        ring
      rw [UniformSpace.Completion.norm_coe]
      change ‖(x-A.dualEmbedding v) (A.embedding p)‖ ≤ (ε/2)*A.seminorm p
      rw [hd,Real.norm_eq_abs]
      exact (abs_add_le _ _).trans ((add_le_add hival hoval).trans_eq (by ring))
  exact hbound.trans_lt (by linarith)

lemma dual_separable [Countable ι] (c : ι → κ) (hblocks : A.HilbertBlocks c) :
    TopologicalSpace.SeparableSpace A.Dual := by
  let V := Submodule.span ℝ (Set.range A.coordinate)
  have hdense : Dense (V : Set A.Dual) := by
    intro x
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨v,hv⟩ := A.dual_approximation c hblocks x hε
    refine ⟨A.dualEmbedding v,?_,?_⟩
    · change (∑ i ∈ v.support,v i • A.coordinate i) ∈ V
      exact Submodule.sum_mem V (fun i _ => V.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩))
    · simpa only [dist_eq_norm] using hv
  apply hdense.isSeparable_iff.mp
  exact (Set.countable_range A.coordinate).isSeparable.span

end CoordinateCompletion.Data

end DiamondDistortion

end

end OAI


