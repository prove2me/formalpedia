-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionBasics
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionBasics
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:10.425871+00:00
-- url     : https://prove2.me/theorems/82cdfd1c-7e26-4124-bd7e-28748b51e887
-- title:
--   Isaacs Ch. 6: Frobenius action basics
-- statement:
--   Formalizes the basics of Frobenius actions from Isaacs, *Finite Group Theory*, Chapter 6 (pp. 177–183): an action of $A$ on $N$ by automorphisms is Frobenius if no nonidentity element of $A$ fixes a nonidentity element of $N$. The file covers stabilizers, fixed points, restriction to subgroups and quotients, the congruence $|N|\equiv1\pmod{|A|}$ with coprimality, and the even-order complement facts of Thm 6.3 (unique involution, inversion $n\mapsto n^{-1}$).
--
--   Main definitions: `IsFrobeniusAction` and the induced actions on invariant subgroups and invariant quotients (`invariantSubgroupMulDistribMulAction`, `invariantQuotientMulAut`, `invariantQuotientMulAutHom`, `invariantQuotientMulDistribMulAction`).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusActionBasics.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusActionBasics.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_SemiDihedral
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.SetTheory.Cardinal.Finite

namespace OddOrder.Isaacs.Ch06

section

/-- An action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity element of `A`
fixes any nonidentity element of `N`.

Isaacs p. 177: "the action of `A` on `N` is said to be Frobenius if `n^a ≠ n` whenever `n ∈ N`
and `a ∈ A` are nonidentity elements." -/
def IsFrobeniusAction (A N : Type*) [Group A] [Group N] [MulDistribMulAction A N] : Prop :=
  ∀ a : A, a ≠ 1 → ∀ n : N, n ≠ 1 → a • n ≠ n

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

namespace IsFrobeniusAction

/-- **Frobenius action: `fixedBy N a = {1}` for `a ≠ 1`.** -/
theorem fixedBy_eq_singleton_one (h : IsFrobeniusAction A N) {a : A} (ha : a ≠ 1) :
    MulAction.fixedBy N a = {1} := by
  ext n
  simp only [MulAction.mem_fixedBy, Set.mem_singleton_iff]
  refine ⟨fun hn => ?_, ?_⟩
  · by_contra hne; exact h a ha n hne hn
  · rintro rfl; exact smul_one a

@[reducible] def invariantSubgroupMulDistribMulAction (M : Subgroup N)
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : MulDistribMulAction A M := by
  letI : SMul A M := ⟨fun a m => ⟨a • (m : N), hM a m m.2⟩⟩
  exact Subtype.coe_injective.mulDistribMulAction M.subtype (fun _ _ => rfl)

/-- A Frobenius action restricts to every invariant subgroup. -/
theorem subgroup (h : IsFrobeniusAction A N) (M : Subgroup N)
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) :
    @IsFrobeniusAction A M _ _ (invariantSubgroupMulDistribMulAction M hM) := by
  let : MulDistribMulAction A M := invariantSubgroupMulDistribMulAction M hM
  intro a ha m hm hfix
  have hmN : (m : N) ≠ 1 := fun hmN => hm (Subtype.ext hmN)
  exact h a ha (m : N) hmN (Subtype.ext_iff.mp hfix)

/-- A Frobenius action remains Frobenius after restricting the acting group to a subgroup. -/
theorem actorSubgroup (h : IsFrobeniusAction A N) (B : Subgroup A) :
    IsFrobeniusAction B N := by
  intro b hb n hn hfix
  have hbA : (b : A) ≠ 1 := fun hbA => hb (Subtype.ext hbA)
  exact h (b : A) hbA n hn ((Subgroup.smul_def b n).symm.trans hfix)

@[reducible] def invariantQuotientMulAut (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) (a : A) : MulAut (N ⧸ M) := by
  let f : N ⧸ M →* N ⧸ M :=
    QuotientGroup.map M M (MulDistribMulAction.toMulAut A N a).toMonoidHom
      (by
        intro m hm
        exact hM a m hm)
  let g : N ⧸ M →* N ⧸ M :=
    QuotientGroup.map M M (MulDistribMulAction.toMulAut A N a⁻¹).toMonoidHom
      (by
        intro m hm
        exact hM a⁻¹ m hm)
  exact MonoidHom.toMulEquiv f g
    (by
      ext n
      simp [f, g])
    (by
      ext n
      simp [f, g])

@[reducible] def invariantQuotientMulAutHom (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : A →* MulAut (N ⧸ M) where
  toFun := invariantQuotientMulAut M hM
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro n
    simp [invariantQuotientMulAut]
  map_mul' := by
    intro a b
    ext q
    refine QuotientGroup.induction_on q ?_
    intro n
    simp [invariantQuotientMulAut, mul_smul]

@[reducible] def invariantQuotientMulDistribMulAction (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : MulDistribMulAction A (N ⧸ M) :=
  MulDistribMulAction.compHom (N ⧸ M) (invariantQuotientMulAutHom M hM)

/-- **Isaacs Lemma 6.1**: a Frobenius action gives `|N| ≡ 1 (mod |A|)`.

Proof via Burnside's lemma:
`∑_{a ∈ A} |fixedBy N a| = (#orbits) * |A|`. For `a = 1` the fixed-set is all of `N` (size `|N|`),
and for `a ≠ 1` it is `{1}` (size 1). So `|N| + (|A| - 1) = (#orbits) * |A|`, hence
`|A| ∣ |N| - 1`. -/
theorem card_modEq_one [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Fintype.card N ≡ 1 [MOD Fintype.card A] := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient A N) := Quotient.fintype _
  -- Burnside.
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group A N
  -- Compute LHS: split `a = 1` from `a ≠ 1`.
  have h_one : Fintype.card (MulAction.fixedBy N (1 : A)) = Fintype.card N := by
    have h_eq : MulAction.fixedBy N (1 : A) = Set.univ := by
      ext n; simp
    calc Fintype.card (MulAction.fixedBy N (1 : A))
        = Fintype.card ((Set.univ : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = Fintype.card N := Fintype.card_congr (Equiv.Set.univ N)
  have h_other : ∀ a ∈ Finset.univ.erase (1 : A),
      Fintype.card (MulAction.fixedBy N a) = 1 := by
    intro a ha
    have ha_ne : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have h_eq := fixedBy_eq_singleton_one h ha_ne
    calc Fintype.card (MulAction.fixedBy N a)
        = Fintype.card (({1} : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = 1 := by simp
  have hLHS : ∑ a : A, Fintype.card (MulAction.fixedBy N a)
            = Fintype.card N + (Fintype.card A - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : A)), h_one,
        Finset.sum_congr rfl h_other, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, add_comm]
  rw [hLHS] at hburn
  -- Now: |N| + (|A| - 1) = (#orbits) * |A|, so |A| ∣ |N| - 1.
  have : Nonempty (MulAction.orbitRel.Quotient A N) := ⟨⟦1⟧⟩
  set k := Fintype.card (MulAction.orbitRel.Quotient A N)
  set a := Fintype.card A
  set n := Fintype.card N
  have ha_pos : 0 < a := Fintype.card_pos
  have hn_pos : 0 < n := Fintype.card_pos
  have hk_pos : 0 < k := Fintype.card_pos
  -- |N| - 1 = a * (k - 1).
  have hdvd : a ∣ n - 1 := by
    refine ⟨k - 1, ?_⟩
    rw [mul_comm a (k - 1), tsub_mul, one_mul]
    omega
  exact ((Nat.modEq_iff_dvd' hn_pos).mpr hdvd).symm

/-- Corollary of Lemma 6.1: a Frobenius action implies `|N|` and `|A|` are coprime. -/
theorem coprime_card [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Nat.Coprime (Fintype.card N) (Fintype.card A) := by
  unfold Nat.Coprime
  rw [(card_modEq_one h).gcd_eq, Nat.gcd_one_left]

/-- **Isaacs Corollary 6.2**: a Frobenius action descends to every invariant normal quotient. -/
theorem quotient [Finite A] [Finite N] (h : IsFrobeniusAction A N) (M : Subgroup N)
    [M.Normal] (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) :
    @IsFrobeniusAction A (N ⧸ M) _ _ (invariantQuotientMulDistribMulAction M hM) := by
  classical
  let : MulDistribMulAction A (N ⧸ M) := invariantQuotientMulDistribMulAction M hM
  intro a ha q hq_ne hfix
  revert hq_ne hfix
  refine QuotientGroup.induction_on q ?_
  intro n hq_ne hfix
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let P : Subgroup A :=
    { carrier := {b | ∃ m ∈ M, φ b n = n * m}
      one_mem' := by
        refine ⟨1, M.one_mem, ?_⟩
        simp [φ]
      mul_mem' := by
        intro b c hb hc
        rcases hb with ⟨mb, hmb, hb⟩
        rcases hc with ⟨mc, hmc, hc⟩
        refine ⟨mb * (φ b) mc, M.mul_mem hmb (hM b mc hmc), ?_⟩
        calc
          φ (b * c) n = φ b (φ c n) := by
            change (b * c) • n = b • c • n
            rw [mul_smul]
          _ = φ b (n * mc) := by rw [hc]
          _ = φ b n * φ b mc := by simp
          _ = n * (mb * φ b mc) := by rw [hb]; group
      inv_mem' := by
        intro b hb
        rcases hb with ⟨m, hm, hb⟩
        refine ⟨((φ b⁻¹) m)⁻¹, M.inv_mem (hM b⁻¹ m hm), ?_⟩
        have hb' : n = φ b⁻¹ n * φ b⁻¹ m := by
          calc
            n = φ b⁻¹ (φ b n) := by simp [φ]
            _ = φ b⁻¹ (n * m) := by rw [hb]
            _ = φ b⁻¹ n * φ b⁻¹ m := by simp
        calc
          φ b⁻¹ n = (φ b⁻¹ n * φ b⁻¹ m) * (φ b⁻¹ m)⁻¹ := by group
          _ = n * (φ b⁻¹ m)⁻¹ := by rw [← hb'] }
  have haP : a ∈ P := by
    have hfix' : ((a • n : N) : N ⧸ M) = (n : N ⧸ M) := hfix
    have hdiv : (a • n) / n ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hfix'
    have hMN : M.Normal := inferInstance
    have hm : n⁻¹ * (a • n) ∈ M := by
      rw [← hMN.mem_comm_iff]
      simpa [div_eq_mul_inv] using hdiv
    refine ⟨n⁻¹ * (a • n), hm, ?_⟩
    simp [φ]
  let C : Subgroup A := Subgroup.zpowers a
  let φC : C →* MulAut N := φ.comp C.subtype
  have hC_le_P : C ≤ P := Subgroup.zpowers_le.mpr haP
  have hM_inv_C : OddOrder.Isaacs.Ch03.IsAInvariant φC M := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro c m hm
    exact hM (c : A) m hm
  have : Fintype A := Fintype.ofFinite A
  have : Fintype N := Fintype.ofFinite N
  have hCopAN : Nat.Coprime (Nat.card A) (Nat.card N) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact (coprime_card h).symm
  have hCopCN : Nat.Coprime (Nat.card C) (Nat.card N) :=
    hCopAN.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  have : IsCyclic C := Subgroup.isCyclic_zpowers a
  let : CommGroup C := IsCyclic.commGroup
  have hSolvC : Group.IsSolvable C ∨ Group.IsSolvable N := Or.inl inferInstance
  have hg_fix_C : ∀ c : C, ∃ m ∈ M, φC c n = n * m := by
    intro c
    simpa [φC, P] using hC_le_P c.2
  obtain ⟨x, hx_fixed, hx_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
      (A := C) (G := N) (φ := φC) hCopCN hSolvC hM_inv_C hg_fix_C
  have hx_ne : x ≠ 1 := by
    intro hx_one
    rcases hx_coset with ⟨m, hm, hx_eq⟩
    have hn_eq : n = m⁻¹ := by
      calc
        n = n * m * m⁻¹ := by group
        _ = x * m⁻¹ := by rw [hx_eq]
        _ = m⁻¹ := by rw [hx_one, one_mul]
    have hnM : n ∈ M := by
      rw [hn_eq]
      exact M.inv_mem hm
    exact hq_ne ((QuotientGroup.eq_one_iff n).mpr hnM)
  have hax : a • x = x := by
    have := hx_fixed ⟨a, Subgroup.mem_zpowers a⟩
    simpa [φC, φ] using this
  exact h a ha x hx_ne hax

/-- **Fixed-point-free action on a quotient from a "fixed points lie in `M`" condition.**
A variant of `IsFrobeniusAction.quotient` that does *not* require the action on `N` to be Frobenius:
if a finite group `A` acts on a finite group `N` with `(|A|, |N|) = 1`, and for every nonidentity
`a ∈ A` the `a`-fixed points of `N` lie in the `A`-invariant normal subgroup `M`, then the induced
action of `A` on `N ⧸ M` is Frobenius (fixed-point-free).

This is Peterfalvi's (6.5)/(6.8)(c2) mechanism: in the certain-type case `A = W₁` does *not* act
fixed-point-freely on the kernel `N = H` (the fixed points are `C_H(x) = W₂ ≠ 1`), but since
`W₂ ⊆ ⁅H,H⁆ = M`, it acts fixed-point-freely on the abelianization `H / ⁅H,H⁆`.  The proof is the
coprime fixed-point lifting (Isaacs Cor 3.28): an `a`-fixed coset of `N / M` lifts to an `a`-fixed
`c ∈ N` (cyclic `⟨a⟩` acting coprimely), and `c` lies in `M` by hypothesis, so the coset is
trivial. -/
theorem quotient_of_fixedPoints_le [Finite A] [Finite N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (M : Subgroup N) [M.Normal] (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M)
    (hfixle : ∀ a : A, a ≠ 1 → ∀ x : N, a • x = x → x ∈ M) :
    @IsFrobeniusAction A (N ⧸ M) _ _ (invariantQuotientMulDistribMulAction M hM) := by
  classical
  let : MulDistribMulAction A (N ⧸ M) := invariantQuotientMulDistribMulAction M hM
  intro a ha q hq_ne hfix_q
  revert hq_ne hfix_q
  refine QuotientGroup.induction_on q ?_
  intro n hq_ne hfix_q
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let P : Subgroup A :=
    { carrier := {b | ∃ m ∈ M, φ b n = n * m}
      one_mem' := by
        refine ⟨1, M.one_mem, ?_⟩
        simp [φ]
      mul_mem' := by
        intro b c hb hc
        rcases hb with ⟨mb, hmb, hb⟩
        rcases hc with ⟨mc, hmc, hc⟩
        refine ⟨mb * (φ b) mc, M.mul_mem hmb (hM b mc hmc), ?_⟩
        calc
          φ (b * c) n = φ b (φ c n) := by
            change (b * c) • n = b • c • n
            rw [mul_smul]
          _ = φ b (n * mc) := by rw [hc]
          _ = φ b n * φ b mc := by simp
          _ = n * (mb * φ b mc) := by rw [hb]; group
      inv_mem' := by
        intro b hb
        rcases hb with ⟨m, hm, hb⟩
        refine ⟨((φ b⁻¹) m)⁻¹, M.inv_mem (hM b⁻¹ m hm), ?_⟩
        have hb' : n = φ b⁻¹ n * φ b⁻¹ m := by
          calc
            n = φ b⁻¹ (φ b n) := by simp [φ]
            _ = φ b⁻¹ (n * m) := by rw [hb]
            _ = φ b⁻¹ n * φ b⁻¹ m := by simp
        calc
          φ b⁻¹ n = (φ b⁻¹ n * φ b⁻¹ m) * (φ b⁻¹ m)⁻¹ := by group
          _ = n * (φ b⁻¹ m)⁻¹ := by rw [← hb'] }
  have haP : a ∈ P := by
    have hfix' : ((a • n : N) : N ⧸ M) = (n : N ⧸ M) := hfix_q
    have hdiv : (a • n) / n ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hfix'
    have hMN : M.Normal := inferInstance
    have hm : n⁻¹ * (a • n) ∈ M := by
      rw [← hMN.mem_comm_iff]
      simpa [div_eq_mul_inv] using hdiv
    refine ⟨n⁻¹ * (a • n), hm, ?_⟩
    simp [φ]
  let C : Subgroup A := Subgroup.zpowers a
  let φC : C →* MulAut N := φ.comp C.subtype
  have hC_le_P : C ≤ P := Subgroup.zpowers_le.mpr haP
  have hM_inv_C : OddOrder.Isaacs.Ch03.IsAInvariant φC M := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro c m hm
    exact hM (c : A) m hm
  have : Fintype A := Fintype.ofFinite A
  have : Fintype N := Fintype.ofFinite N
  have hCopCN : Nat.Coprime (Nat.card C) (Nat.card N) :=
    hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  have : IsCyclic C := Subgroup.isCyclic_zpowers a
  let : CommGroup C := IsCyclic.commGroup
  have hSolvC : Group.IsSolvable C ∨ Group.IsSolvable N := Or.inl inferInstance
  have hg_fix_C : ∀ c : C, ∃ m ∈ M, φC c n = n * m := by
    intro c
    simpa [φC, P] using hC_le_P c.2
  obtain ⟨x, hx_fixed, hx_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
      (A := C) (G := N) (φ := φC) hCopCN hSolvC hM_inv_C hg_fix_C
  have hax : a • x = x := by
    have := hx_fixed ⟨a, Subgroup.mem_zpowers a⟩
    simpa [φC, φ] using this
  have hxM : x ∈ M := hfixle a ha x hax
  rcases hx_coset with ⟨m, hm, hx_eq⟩
  have hnM : n ∈ M := by
    have hne : n = x * m⁻¹ := by rw [hx_eq]; group
    rw [hne]; exact M.mul_mem hxM (M.inv_mem hm)
  exact hq_ne ((QuotientGroup.eq_one_iff n).mpr hnM)

end IsFrobeniusAction

end

end OddOrder.Isaacs.Ch06


