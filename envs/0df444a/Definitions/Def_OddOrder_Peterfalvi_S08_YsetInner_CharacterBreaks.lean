-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_YsetInner_CharacterBreaks
-- name    : OddOrder_Peterfalvi_S08_YsetInner_CharacterBreaks
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:40.26192+00:00
-- url     : https://prove2.me/theorems/402e4d51-bc73-41f5-8707-6c0b0721e0ad
-- title:
--   Peterfalvi §8: character expansions and coherence breaks
-- statement:
--   Part of Peterfalvi §8 (pp. 30–37): Fourier expansion, induction and kernel estimates, finite conjugate-pair covers, and the first coherent-break construction used by the §8 descent.
--
--   Declarations include `classFunction_eq_sum_inner_smul` (Fourier expansion of a class function in the orthonormal basis of irreducibles), `sum_filter_degree_mul_charValue_sub_eq` (regular-character difference value over the non-inflated irreducibles), `sum_sq_le_inner_self_re` (Bessel's inequality in integer-coefficient form), `adjointAverageFun_eq_of_H_eq_bot` (the TI Dade situation $H(a)=\bot$), `inner_isCharacter_nonneg` (the inner product of two genuine characters is nonnegative) and `induce_exists_natFinsupp_eq_sum` ((H2): an induced genuine character decomposes with natural coefficients).
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_YsetInner/CharacterBreaks.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_YsetInner/CharacterBreaks.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainHypothesis46
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_GroupTheory_SubgroupInAmbient
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SylowTICongruence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03_FrobeniusActions
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace OddOrder.RepresentationTheory

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

open scoped Classical in
/-- **Fourier expansion of a class function** in the orthonormal basis of irreducible characters:
`φ = ∑_{χ ∈ Irr Γ} ⟨φ, χ⟩ • χ`.  From completeness (`classFunction_eq_zero_of_orthogonal`): the
difference `φ − ∑ ⟨φ,χ⟩•χ` is orthogonal to every irreducible (orthonormality
`irreducibleCharacter_inner_eq_ite`), hence `0`.  Used in (6.8.1) to expand `Res^G_L(η₁^{τ₁})` and
split its `X`-part (whose coefficients `⟨·,χᵢ⟩` are governed by Res-orthogonality) from the
`Z ⊆ ker` part (constant on `Z`). -/
theorem classFunction_eq_sum_inner_smul (φ : ClassFunction Γ ℂ) :
    φ = ∑ a : IrreducibleCharacter Γ,
      ClassFunction.inner φ (a : ClassFunction Γ ℂ) • (a : ClassFunction Γ ℂ) := by
  refine eq_of_sub_eq_zero (classFunction_eq_zero_of_orthogonal _ (fun b => ?_))
  rw [ClassFunction.inner_sub_left, inner_sum_left]
  have hstep : (∑ a : IrreducibleCharacter Γ,
      ClassFunction.inner
        (ClassFunction.inner φ (a : ClassFunction Γ ℂ) • (a : ClassFunction Γ ℂ))
        (b : ClassFunction Γ ℂ)) = ClassFunction.inner φ (b : ClassFunction Γ ℂ) := by
    rw [Finset.sum_eq_single b]
    · rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite b b, if_pos rfl, mul_one]
    · intro a _ hab
      rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite a b, if_neg hab,
          mul_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [hstep, sub_self]

open scoped Classical in
omit [Invertible (Nat.card Γ : ℂ)] in
omit [Fintype Γ] in
/-- **Regular-character difference value over the non-inflated irreducibles** (mmd 04.8 L168,
combined `(ρ_Γ − ρ_{Γ/N})(z) − (…)(1)` value).  For `N ⊴ Γ` and `z ∈ N^#`,
`∑_{χ ∈ Irr Γ, N ⊄ ker χ} χ(1)·(χ(z) − χ(1)) = -|Γ|`.  This is
`(-|Γ⧸N|) − (|Γ| − |Γ⧸N|) = -|Γ|`, from `sumNonInflatedDegreeMulChar_of_mem` (the `χ(z)` part) and
`sumNonInflatedDegreeSq` (the `χ(1)` part). -/
theorem sum_filter_degree_mul_charValue_sub_eq [Finite Γ] (N : Subgroup Γ) [N.Normal]
    {z : Γ} (hz : z ∈ N) (hz1 : z ≠ 1) :
    ∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * ((a : ClassFunction Γ ℂ) z - (a : ClassFunction Γ ℂ) 1)
      = -(Nat.card Γ : ℂ) := by
  have hsplit : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * ((a : ClassFunction Γ ℂ) z - (a : ClassFunction Γ ℂ) 1))
      = (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) z)
        - (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
            ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
            (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun a _ => by ring)
  have h2 : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1)
      = (Nat.card Γ : ℂ) - (Nat.card (Γ ⧸ N) : ℂ) := by
    rw [show (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1)
        = ∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          ((a : ClassFunction Γ ℂ) 1) ^ 2 from
        Finset.sum_congr rfl (fun a _ => by rw [pow_two])]
    exact sumNonInflatedDegreeSq (N := N)
  rw [hsplit, sumNonInflatedDegreeMulChar_of_mem (N := N) hz hz1, h2]; ring

open scoped Classical in
/-- **Bessel's inequality (integer-coefficient form).**  For an orthonormal family `s` of class
functions (`⟨a,b⟩ = δ_{a,b}` on `s`) and any `v` whose Fourier coefficients on `s` are integers
(`⟨v,a⟩ = β a`), the sum of squared coefficients is bounded by the squared norm:
`∑_{a∈s} (β a)² ≤ (⟨v,v⟩).re`.

Pythagoras on `v = (v − p) + p` with `p = ∑_{a∈s} (β a)•a` the orthogonal projection:
`⟨v,p⟩ = ⟨p,v⟩ = ⟨p,p⟩ = ∑(β a)²` (Parseval `inner_self_orthonormalSum_eq_sum_sq` + conjugate
symmetry), so `⟨v−p,v−p⟩ = ⟨v,v⟩ − ∑(β a)²`; non-negativity of `‖v−p‖²`
(`inner_self_re_nonneg`) gives the bound. -/
theorem sum_sq_le_inner_self_re {s : Finset (ClassFunction Γ ℂ)}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (v : ClassFunction Γ ℂ) {β : ClassFunction Γ ℂ → ℤ}
    (hβ : ∀ a ∈ s, ClassFunction.inner v a = (β a : ℂ)) :
    ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℝ) ≤ (ClassFunction.inner v v).re := by
  classical
  set p : ClassFunction Γ ℂ := ∑ a ∈ s, (β a : ℂ) • a with hp
  have hsumcast : ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) = ∑ a ∈ s, ((β a : ℂ)) ^ 2 := by
    push_cast; ring
  have hvp : ClassFunction.inner v p = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [hp, inner_sum_right, hsumcast]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_smul_right, hβ a ha, star_intCast]; ring
  have hpp : ClassFunction.inner p p = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [hp, inner_self_orthonormalSum_eq_sum_sq horth, hsumcast]
  have hpv : ClassFunction.inner p v = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [inner_conj_symm v p, hvp, star_intCast]
  have hkey : ClassFunction.inner (v - p) (v - p)
      = ClassFunction.inner v v - ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hvp, hpv, hpp]; ring
  have hnn := inner_self_re_nonneg (v - p)
  rw [hkey, Complex.sub_re] at hnn
  have hcast : (((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ)).re = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℝ) :=
    Complex.intCast_re _
  rw [hcast] at hnn
  linarith

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-- **(H0)** the restriction `Res^Γ_H φ` of a genuine character is genuine. -/
theorem isCharacter_restrict {Γ : Type*} [Group Γ] [Finite Γ] {φ : ClassFunction Γ ℂ}
    (hφ : IsCharacter φ) (H : Subgroup Γ) :
    IsCharacter (ClassFunction.restrict H φ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  have hφeq : φ = repCharacterClassFunction ρ :=
    ClassFunction.ext fun g => by rw [repCharacterClassFunction_apply]; exact congrFun hρ g
  rw [hφeq, ClassFunction.restrict_repCharacterClassFunction H ρ]
  exact repCharacterClassFunction_isCharacter (ρ.comp H.subtype)

/-- **(H1, decomposition form)** an irreducible constituent inherits a kernel containment of a
non-negative integer combination.  If `ψ = ∑_{a ∈ supp m} (m a) • a` is a finite `ℕ`-combination
of irreducible characters (`m : ClassFunction Γ ℂ →₀ ℕ` supported on `Irr Γ`) and `χ` is a
summand with `m χ ≠ 0`, then `g ∈ Ker ψ` forces `g ∈ Ker χ`.

This repackages the (6.6) G2.2 keystone
`OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq` from a
`Finsupp` decomposition: the family of summands is totalized to an `IrreducibleCharacter`-valued
function off the support, and the kernel hypothesis `ψ(g) = ψ(1)` is read as the keystone's
value-equality hypothesis. -/
theorem characterKernel_subset_of_natFinsupp_eq_sum {Γ : Type*} [Group Γ] [Finite Γ]
    {ψ : ClassFunction Γ ℂ} {m : ClassFunction Γ ℂ →₀ ℕ}
    (hsupp : (↑m.support : Set (ClassFunction Γ ℂ)) ⊆ irreducibleCharacters Γ)
    (hsum : ψ = ∑ a ∈ m.support, (m a : ℂ) • a)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ) (hmχ : m χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel ψ) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  classical
  set χfam : ClassFunction Γ ℂ → IrreducibleCharacter Γ :=
    fun a => if h : IsIrreducibleCharacter a then (⟨a, h⟩ : IrreducibleCharacter Γ)
      else trivialIrreducibleCharacter Γ with hχfam_def
  have hfam : ∀ a, IsIrreducibleCharacter a →
      ((χfam a : IrreducibleCharacter Γ) : ClassFunction Γ ℂ) = a := by
    intro a h; simp only [hχfam_def, dif_pos h]
  have hirr : ∀ a ∈ m.support, IsIrreducibleCharacter a := fun a ha =>
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  set d : ClassFunction Γ ℂ → ℕ :=
    fun a => if h : IsIrreducibleCharacter a then
      (h.exists_natDegree_charValue_one_dvd_card).choose else 0 with hd_def
  have hdeg : ∀ a ∈ m.support, ((χfam a : ClassFunction Γ ℂ)) 1 = (d a : ℂ) := by
    intro a ha
    have h := hirr a ha
    rw [hfam a h]
    simp only [hd_def, dif_pos h]
    exact (h.exists_natDegree_charValue_one_dvd_card).choose_spec.2.1
  have hsumapp : ∀ x : Γ, ψ x = ∑ a ∈ m.support, (m a : ℂ) * a x := by
    intro x
    rw [hsum]
    simp only [ClassFunction.finset_sum_apply, ClassFunction.smul_apply]
  have hgg : ψ g = ψ 1 := by
    have h := hg
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at h
    exact h
  have hval : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) g
      = ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) 1 := by
    have eL : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) g = ψ g := by
      rw [hsumapp g]; exact Finset.sum_congr rfl fun a ha => by rw [hfam a (hirr a ha)]
    have eR : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) 1 = ψ 1 := by
      rw [hsumapp 1]; exact Finset.sum_congr rfl fun a ha => by rw [hfam a (hirr a ha)]
    rw [eL, eR, hgg]
  have hkey :=
    OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq
      (g := g) m.support (fun a => m a) χfam d hdeg hval χ
      (Finsupp.mem_support_iff.mpr hmχ) hmχ
  rwa [hfam χ hχ] at hkey

/-- **(H1, genuine form)** an irreducible constituent of a genuine character inherits a kernel
containment.  If `ψ` is a genuine character, `χ` is irreducible with `⟨ψ, χ⟩ ≠ 0` (a constituent),
then `g ∈ Ker ψ` forces `g ∈ Ker χ`.  This is `characterKernel_subset_of_natFinsupp_eq_sum`
applied to the `ℕ`-decomposition `IsCharacter.exists_natFinsupp_eq_sum` of `ψ`, whose
`χ`-coefficient is the nonzero Fourier multiplicity `⟨ψ, χ⟩`. -/
theorem characterKernel_subset_of_isCharacter_of_inner_ne_zero {Γ : Type*} [Group Γ]
    [Fintype Γ] [Invertible (Nat.card Γ : ℂ)] {ψ : ClassFunction Γ ℂ} (hψ : IsCharacter ψ)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ)
    (hχψ : ClassFunction.inner ψ χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel ψ) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hψ.exists_natFinsupp_eq_sum
  have hmχ : m χ ≠ 0 := fun h0 => hχψ (by rw [← hcoeff χ hχ, h0, Nat.cast_zero])
  exact characterKernel_subset_of_natFinsupp_eq_sum hsupp hsum hχ hmχ hg

section DadeCoherenceUnion

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **Difference-orthogonality (Peterfalvi (4.1) input).**  For two coherences `hX`, `hY` w.r.t. the
**same** §4 Dade base map and supported lattice elements `x ∈ ℤ[X, A]`, `y ∈ ℤ[Y, A]`, the cross
inner product of the extensions equals the source inner product:
`⟨hX.extension x, hY.extension y⟩ = ⟨x, y⟩`.  Both extensions agree with the Dade map on the
supported lattice (`extends_on_supported`), reducing to the Dade isometry
`dadeIntegralCharacterMap_inner_eq_on_supported_span` (applied on the pair `{x, y}`). -/
theorem inner_extension_eq_inner_of_supported
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {X Y : Set (ClassFunction ↥L ℂ)}
    (hX : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hY : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) Y
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {x y : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hy : y ∈ OddOrder.Peterfalvi.S07.zSupportedSpan Y
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    ClassFunction.inner (hX.extension x) (hY.extension y) = ClassFunction.inner x y := by
  rw [hX.extends_on_supported x hx, hY.extends_on_supported y hy]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
    (S := ({x, y} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hx.2
        · exact hy.2)
    (Submodule.subset_span (Set.mem_insert x _))
    (Submodule.subset_span (Set.mem_insert_of_mem x rfl))

/-- A coherent Dade extension sends a supported lattice element to a function vanishing at `1`:
`(hX.extension x)(1) = 0` for `x ∈ ℤ[X, A]`.  (`extends_on_supported` to the Dade map, then
`dadeIntegralCharacterMap_apply_one_eq_zero`.)  Supplies the degree-`0` hypotheses of (4.1). -/
theorem extension_apply_one_eq_zero_of_supported
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {X : Set (ClassFunction ↥L ℂ)}
    (hX : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    (hX.extension x) (1 : G) = 0 := by
  rw [hX.extends_on_supported x hx]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero hyp hx.2

end DadeCoherenceUnion

/-- **Peterfalvi (6.8.1) norm-bound forcing** (mmd 04.8 L176).  In the (6.8.1) `b ≡ c ≡ 0 mod a`
argument, after `(6.7)` gives `a ∣ b` (write `b = a·x`), the norm identity
`1 + a² = ‖(χ₁ − aη₁)^τ‖² = ‖X‖² + (b − a)² + (m − 1)·b²` with `‖X‖² ≥ 0` gives the bound
`(b − a)² + (m − 1)·b² ≤ 1 + a²`; with `a ≥ 2` and `m ≥ 2` (`m = |Y|`) this forces `b = 0` — or the
edge case `b = a`, `m = 2`, which the textbook reduces to `b = 0` by relabelling
`η₁^{τ₁} ↔ −η₂^{τ₁}`.  (`b = ±2a` and `b = −a` are excluded since `4a² > 1 + a²` for `a ≥ 2`.) -/
theorem eq_zero_or_edge_of_dvd_of_normBound {a b m : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hdvd : a ∣ b)
    (hnorm : (b - a) ^ 2 + (m - 1) * b ^ 2 ≤ 1 + a ^ 2) :
    b = 0 ∨ (b = a ∧ m = 2) := by
  obtain ⟨x, rfl⟩ := hdvd
  have ha0 : (0 : ℤ) < a := by linarith
  -- `b² = (a·x)² ≤ 1 + a²` (drop `(b−a)² ≥ 0` and the `(m−2)·b² ≥ 0` slack).
  have hb2 : (a * x) ^ 2 ≤ 1 + a ^ 2 := by
    nlinarith [sq_nonneg (a * x - a), mul_nonneg (by linarith : (0 : ℤ) ≤ m - 2) (sq_nonneg (a *
        x))]
  -- Hence `x² ≤ 1`: otherwise `x² ≥ 2` gives `2a² ≤ a²x² ≤ 1 + a²`, i.e. `a² ≤ 1`, contradicting
  -- `a ≥ 2`.
  have hx2 : x ^ 2 ≤ 1 := by
    by_contra h
    push Not at h
    have hx2' : 2 ≤ x ^ 2 := h
    nlinarith [hb2, mul_pos ha0 ha0, mul_le_mul_of_nonneg_left hx2' (le_of_lt (mul_pos ha0 ha0))]
  have hxlo : -1 ≤ x := by nlinarith [hx2, sq_nonneg (x + 1)]
  have hxhi : x ≤ 1 := by nlinarith [hx2, sq_nonneg (x - 1)]
  interval_cases x
  · -- `x = -1` (`b = -a`): `4a² + (m−1)a² ≤ 1 + a²` is impossible.
    exfalso; nlinarith [hnorm, ha, hm]
  · -- `x = 0`: `b = 0`.
    left; ring
  · -- `x = 1` (`b = a`): `(m−1)a² ≤ 1 + a²` forces `m = 2`.
    right
    refine ⟨by ring, ?_⟩
    nlinarith [hnorm, ha, hm]

section DadeReciprocity

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

omit [Invertible (Nat.card G : ℂ)] in
omit [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] in
/-- In the **TI Dade situation** (`hyp.H a = ⊥`, e.g. `H^#` a TI-subset with normalizer `L`), the
(2.7) adjoint averaging map collapses to plain evaluation: `adjointAverageFun hyp χ a = χ(a)`.  The
average `|H(a)|⁻¹ ∑_{x ∈ H(a)} χ(ax)` over the trivial group `H(a) = ⊥` is the single term
`χ(a·1) = χ(a)`. -/
theorem adjointAverageFun_eq_of_H_eq_bot
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (χ : ClassFunction G ℂ)
    (a : {a : G // a ∈ A}) (hH : hyp.H a = ⊥) :
    OddOrder.Peterfalvi.S04.adjointAverageFun hyp χ ⟨a.1, hyp.subset_L a.2⟩ = χ a.1 := by
  classical
  simp only [OddOrder.Peterfalvi.S04.adjointAverageFun]
  rw [dif_pos a.2]
  have hHa : hyp.H ⟨a.1, a.2⟩ = ⊥ := hH
  have hconst : ∀ x : ↥(hyp.H ⟨a.1, a.2⟩), χ (a.1 * (x : G)) = χ a.1 := by
    intro x
    have hx1 : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hHa]; exact x.2
    rw [Subgroup.mem_bot.mp hx1, mul_one]
  have hHne : (Nat.card (hyp.H ⟨a.1, a.2⟩) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (hyp.H ⟨a.1, a.2⟩) := Nat.card_pos
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hHne, one_mul]

/-- **Dade reciprocity (TI case).**  For the §4 Dade base map of a TI Hypothesis (`hyp.H a = ⊥`),
a *supported* `α ∈ CF(L, A)` and any `ψ ∈ CF(G)`:

`⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L`.

This is the (2.7) `adjoint_formula` specialized to the TI situation, where the adjoint average of
`ψ` is `Res_L^G ψ` (`adjointAverageFun_eq_of_H_eq_bot`).  It is the gateway to the (6.8.1)
`Res_L(η₁^{τ₁})` decomposition: it converts the `G`-side pairing of a Dade image with `ψ` into the
`L`-side pairing of the supported source with `Res_L ψ`. -/
theorem inner_dadeIntegralCharacterMap_eq_inner_restrict
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) α) ψ
      = ClassFunction.inner α (ClassFunction.restrict L ψ) := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp _ hαsupp]
  refine OddOrder.Peterfalvi.S04.adjoint_formula hyp (hyp.dadeMap (k := ℂ))
    (hyp.isDadeMap_dadeMap (k := ℂ))
    ⟨α, (ClassFunction.mem_supportedSubmodule).mpr hαsupp⟩ ψ (ClassFunction.restrict L ψ)
    (fun a => ?_)
  rw [adjointAverageFun_eq_of_H_eq_bot hyp ψ a (hH a), ClassFunction.restrict_apply]

end DadeReciprocity

open scoped ComplexOrder in
/-- The inner product of two genuine characters is `≥ 0`.  Decompose the right argument into a
non-negative integer combination of irreducibles (`exists_natFinsupp_eq_sum`); each summand
`⟨χ, a⟩` is `≥ 0` by `inner_irreducible_nonneg`, and the multiplicities are non-negative. -/
theorem inner_isCharacter_nonneg {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {χ ψ : ClassFunction Γ ℂ}
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    0 ≤ ClassFunction.inner χ ψ := by
  obtain ⟨m, hsupp, hsum, _⟩ := hψ.exists_natFinsupp_eq_sum
  rw [hsum, inner_sum_right]
  refine Finset.sum_nonneg fun a ha => ?_
  have ha' : IsIrreducibleCharacter a :=
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  rw [OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  exact mul_nonneg (Nat.cast_nonneg _) (hχ.inner_irreducible_nonneg ha')

set_option linter.unusedFintypeInType false in
open scoped ComplexOrder in
/-- **(H2)** the induced character `Ind_H^Γ θ` of a genuine character `θ` decomposes as a
non-negative integer combination of irreducibles, with multiplicity `⟨Ind θ, ψ⟩` at `ψ ∈ Irr Γ`.
Since `induce` lives only at the class-function level (`IsCharacter (Ind θ)` is not directly
available), the decomposition is reconstructed from `Ind θ ∈ ZIrr Γ` (`induce_mem_ZIrr`) plus the
non-negativity of `⟨Ind θ, ψ⟩ = ⟨θ, Res ψ⟩` (Frobenius reciprocity and `inner_isCharacter_nonneg`),
pushed through `Int.toNat`. -/
theorem induce_exists_natFinsupp_eq_sum {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    ∃ m : ClassFunction Γ ℂ →₀ ℕ, (↑m.support ⊆ irreducibleCharacters Γ) ∧
      ClassFunction.induce H θ = ∑ a ∈ m.support, (m a : ℂ) • a ∧
      ∀ ψ : ClassFunction Γ ℂ, IsIrreducibleCharacter ψ →
        (m ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
  classical
  obtain ⟨c, hsupp, hsum⟩ := mem_ZIrr_repr (ClassFunction.induce_mem_ZIrr H hθ.mem_ZIrr)
  have hcoeff : ∀ ψ : ClassFunction Γ ℂ, ψ ∈ irreducibleCharacters Γ →
      (c ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
    intro ψ hψ
    have h := inner_eq_coeff_of_repr (⟨ψ, hψ⟩ : IrreducibleCharacter Γ) hsupp
    rw [show ((⟨ψ, hψ⟩ : IrreducibleCharacter Γ) : ClassFunction Γ ℂ) = ψ from rfl] at h
    rw [← h, hsum]
  have hcnn : ∀ ψ : ClassFunction Γ ℂ, ψ ∈ c.support → 0 ≤ c ψ := by
    intro ψ hψsupp
    have hψ : ψ ∈ irreducibleCharacters Γ := hsupp (Finset.mem_coe.mpr hψsupp)
    have hψirr : IsIrreducibleCharacter ψ := mem_irreducibleCharacters.mp hψ
    have hnn : (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce H θ) ψ := by
      rw [ClassFunction.inner_induce_eq_inner_restrict]
      exact inner_isCharacter_nonneg hθ (isCharacter_restrict hψirr.isCharacter H)
    have : (0 : ℂ) ≤ (c ψ : ℂ) := by rw [hcoeff ψ hψ]; exact hnn
    exact_mod_cast this
  refine ⟨Finsupp.mapRange Int.toNat Int.toNat_zero c, ?_, ?_, ?_⟩
  · refine subset_trans ?_ hsupp
    intro ψ hψ
    exact Finset.mem_coe.mpr (Finsupp.support_mapRange (Finset.mem_coe.mp hψ))
  · have hsupp_eq : (Finsupp.mapRange Int.toNat Int.toNat_zero c).support = c.support := by
      apply Finset.Subset.antisymm Finsupp.support_mapRange
      intro a ha
      rw [Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
      omega
    rw [hsum, hsupp_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finsupp.mapRange_apply]
    have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c a)), Int.toNat_of_nonneg (le_of_lt this)]
  · intro ψ hψ
    rw [Finsupp.mapRange_apply, ← hcoeff ψ hψ]
    have hnn : 0 ≤ c ψ := by
      by_cases hsupp_mem : ψ ∈ c.support
      · exact hcnn ψ hsupp_mem
      · rw [Finsupp.notMem_support_iff.mp hsupp_mem]
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c ψ)), Int.toNat_of_nonneg hnn]

set_option linter.unusedFintypeInType false in
/-- **(H2, character form)** the induced character `Ind_H^Γ θ` of a genuine character `θ` is
itself a genuine character.  Combines the non-negative-integer decomposition
`induce_exists_natFinsupp_eq_sum` (`Ind θ = ∑ mₐ·a` with `mₐ ∈ ℕ`, `a ∈ Irr Γ`) with its
converse `isCharacter_of_natFinsupp_eq_sum` (a `ℕ`-combination of irreducible characters is a
genuine character).  This is **brick 2** of the Frobenius-reciprocity route to the Peterfalvi
`(6.2)` `θ`-bound a-half. -/
theorem isCharacter_induce {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    IsCharacter (ClassFunction.induce H θ) := by
  obtain ⟨m, hsupp, hsum, _⟩ := induce_exists_natFinsupp_eq_sum hθ
  exact isCharacter_of_natFinsupp_eq_sum m hsupp hsum

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (6.2) `θ`-bound, a-half** (the Clifford/induction half).  For an irreducible
character `θ` of a finite group `K` and a subgroup `C ≤ K`, there is an irreducible character
`φ` of `C` of which `θ` is a constituent of `Ind_C^K φ` (`⟨Ind_C^K φ, θ⟩ ≠ 0`), and whose
degree controls `θ`'s: `θ(1) ≤ |K : C|·φ(1)`.

By Frobenius reciprocity `θ` is a constituent of `Ind_C^K φ` for some `φ ∈ Irr C`
(`exists_inner_induce_ne_zero`, equivalently `φ` is a constituent of `Res^K_C θ`).  Since `φ` is
a genuine character, so is `Ind_C^K φ` (`isCharacter_induce`, brick 2), so the
constituent-degree bound `IsCharacter.apply_one_re_le_of_inner_ne_zero` (brick 1) gives
`θ(1) ≤ (Ind_C^K φ)(1) = |K : C|·φ(1)` (`induce_apply_one`).  Combined with the section degree
bound `degree_sq_le_index_of_central_quotient` (`φ(1)² ≤ |C : D|`, the b-half) this yields the
full `(6.2)` degree bound `θ(1) ≤ |K : C|·√|C : D|`. -/
theorem theta_degree_le_index_mul_constituent {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (C : Subgroup K) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] (θ : IrreducibleCharacter K) :
    ∃ φ : IrreducibleCharacter C,
      ClassFunction.inner (ClassFunction.induce C (φ : ClassFunction ↥C ℂ))
          (θ : ClassFunction K ℂ) ≠ 0 ∧
      ((θ : ClassFunction K ℂ) 1).re ≤ (C.index : ℝ) * ((φ : ClassFunction ↥C ℂ) 1).re := by
  obtain ⟨φ, hφ⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := C) θ
  refine ⟨φ, hφ, ?_⟩
  have hind : IsCharacter (ClassFunction.induce C (φ : ClassFunction ↥C ℂ)) :=
    isCharacter_induce φ.isIrreducible.isCharacter
  have hbound := hind.apply_one_re_le_of_inner_ne_zero θ.isIrreducible hφ
  rw [ClassFunction.induce_apply_one] at hbound
  rwa [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hbound

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (1.8)** (book p. 8), used here as the (6.2) `θ`-bound.  For an irreducible
character `θ` of a finite group `K`, a subgroup `C ≤ K`, and a section `N ◁ C` with `N ≤ D ≤ C`,
`θ` trivial on `N` (after restriction to `C`) and `D ⧸ N` central in `C ⧸ N`, the degree of `θ` is
bounded: `θ(1) ≤ |K : C|·√|C : D|`.

This is the book's (1.8) verbatim, in index form: with the book's `ψ, G, B, C, D` matching
`θ, K, N, C, D` here, `|K:C|·√|C:D| = |K|/√(|C|·|D|)` (as `|D| = |C|/|C:D|`), which is the book's
right-hand side.  The book states it in §1 as a general degree bound; the repository reached it
from its §8 consumer, hence the (6.2) naming in the surrounding section.

Assembled from the two halves: the a-half `theta_degree_le_index_mul_constituent`
(`θ(1) ≤ |K:C|·φ(1)` for an `Ind`-constituent `φ ∈ Irr C` of `θ`) and the section b-half
`degree_sq_le_index_of_central_quotient` (`φ(1)² ≤ |C:D|`).  The `φ` produced by the a-half is a
constituent of `Res^K_C θ` (Frobenius reciprocity `inner_induce_eq_inner_restrict` +
`inner_conj_symm`), so `N ⊆ Ker(Res^K_C θ)` forces `N ⊆ Ker φ` (constituent kernel inheritance
`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), discharging the b-half's kernel
hypothesis.  Then `φ(1) = d` with `d² ≤ |C:D|` gives `φ(1) ≤ √|C:D|` (`Real.le_sqrt_of_sq_le`),
and multiplying by `|K:C| ≥ 0` closes the bound. -/
theorem theta_degree_le_index_mul_sqrt_index {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (θ : IrreducibleCharacter K) (C : Subgroup K) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] {N : Subgroup ↥C} [N.Normal] (D : Subgroup ↥C) (hND : N ≤ D)
    (hθN : (↑N : Set ↥C) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict C (θ : ClassFunction K ℂ)))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥C ⧸ N)) :
    ((θ : ClassFunction K ℂ) 1).re ≤ (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  obtain ⟨φ, hφne, hφbound⟩ := theta_degree_le_index_mul_constituent C θ
  -- `φ` is a constituent of `Res^K_C θ`: reciprocity turns `⟨Ind φ, θ⟩ ≠ 0` into `⟨φ, Res θ⟩ ≠ 0`,
  -- and conjugate symmetry flips it to `⟨Res θ, φ⟩ ≠ 0`.
  have hφRes : ClassFunction.inner (φ : ClassFunction ↥C ℂ)
      (ClassFunction.restrict C (θ : ClassFunction K ℂ)) ≠ 0 := by
    rw [← ClassFunction.inner_induce_eq_inner_restrict]; exact hφne
  have hres_inner : ClassFunction.inner (ClassFunction.restrict C (θ : ClassFunction K ℂ))
      (φ : ClassFunction ↥C ℂ) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]; exact star_ne_zero.mpr hφRes
  -- constituent kernel inheritance: `N ⊆ Ker(Res θ) ⟹ N ⊆ Ker φ`.
  have hkerφ : (↑N : Set ↥C) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥C ℂ) := fun n hn =>
    characterKernel_subset_of_isCharacter_of_inner_ne_zero
      (isCharacter_restrict θ.isIrreducible.isCharacter C) φ.isIrreducible hres_inner (hθN hn)
  -- the b-half: `φ(1) = d` with `d² ≤ |C:D|`.
  obtain ⟨d, hd1, hd2⟩ :=
    degree_sq_le_index_of_central_quotient (N := N) φ D hND hkerφ hcentral
  have hφ1re : ((φ : ClassFunction ↥C ℂ) 1).re = (d : ℝ) := by
    rw [hd1]; exact Complex.natCast_re d
  have hd_le : (d : ℝ) ≤ Real.sqrt (D.index : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hd2)
  calc ((θ : ClassFunction K ℂ) 1).re
      ≤ (C.index : ℝ) * ((φ : ClassFunction ↥C ℂ) 1).re := hφbound
    _ = (C.index : ℝ) * (d : ℝ) := by rw [hφ1re]
    _ ≤ (C.index : ℝ) * Real.sqrt (D.index : ℝ) :=
        mul_le_mul_of_nonneg_left hd_le (Nat.cast_nonneg _)

/-- **Restriction kernel inheritance.**  If `θ` is trivial on a subgroup `M ≤ K` (i.e.
`M ⊆ characterKernel θ`), then its restriction `Res_C θ` to a subgroup `C ≤ K` is trivial on
`M.subgroupOf C = M ∩ C` (viewed in `C`).  Used by (6.2): a member `ψ = Ind_H^L θ ∈ S(B)` has
source `θ` trivial on `B`, so `Res_C θ` is trivial on `B.subgroupOf C`, discharging the `θ`-bound's
kernel hypothesis. -/
theorem characterKernel_restrict_subgroupOf {K : Type*} [Group K] {θ : ClassFunction K ℂ}
    (C : Subgroup K) {M : Subgroup K}
    (hM : (M : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel θ) :
    ((M.subgroupOf C : Subgroup ↥C) : Set ↥C) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.restrict C θ) := by
  intro c hc
  have hker : (θ : ClassFunction K ℂ) (↑c : K) = (θ : ClassFunction K ℂ) 1 :=
    hM (Subgroup.mem_subgroupOf.mp hc)
  simp only [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def, ClassFunction.restrict_apply,
    OneMemClass.coe_one]
  exact hker

set_option linter.unusedFintypeInType false in
/-- **(H2, kernel form)** an irreducible constituent `χ` of an induced character `Ind_H^Γ θ`
(`θ` genuine, `⟨Ind θ, χ⟩ ≠ 0`) inherits a kernel containment of `Ind θ`.  The `ℕ`-decomposition
`induce_exists_natFinsupp_eq_sum` feeds `characterKernel_subset_of_natFinsupp_eq_sum`. -/
theorem characterKernel_subset_of_inner_induce_ne_zero {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ)
    (hχψ : ClassFunction.inner (ClassFunction.induce H θ) χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce H θ)) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := induce_exists_natFinsupp_eq_sum hθ
  have hmχ : m χ ≠ 0 := fun h0 => hχψ (by rw [← hcoeff χ hχ, h0, Nat.cast_zero])
  exact characterKernel_subset_of_natFinsupp_eq_sum hsupp hsum hχ hmχ hg

/-- **Finite set of irreducible characters → injective `Fin k` enumeration.**  A finite set `T` of
class functions all of which are irreducible characters is enumerated by an injective family
`χ : Fin k → IrreducibleCharacter Γ` whose underlying-class-function range is exactly `T`.  This is
the bridge to the `Fin n`-indexed family interface of `coherentEqualDegree_fromDade` (the base
block `S₀`). -/
theorem exists_finEnum_irreducible {Γ : Type*} [Group Γ] {T : Set (ClassFunction Γ ℂ)}
    (hTfin : T.Finite) (hTirr : ∀ χ ∈ T, IsIrreducibleCharacter χ) :
    ∃ (k : ℕ) (χ : Fin k → IrreducibleCharacter Γ),
      Function.Injective χ ∧ Set.range (fun j => (χ j : ClassFunction Γ ℂ)) = T := by
  classical
  have : Fintype T := hTfin.fintype
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun j => ⟨(e.symm j : ClassFunction Γ ℂ), hTirr _ (e.symm j).2⟩, ?_, ?_⟩
  · intro i j hij
    have h : (e.symm i : ClassFunction Γ ℂ) = (e.symm j : ClassFunction Γ ℂ) :=
      congrArg (fun c : IrreducibleCharacter Γ => (c : ClassFunction Γ ℂ)) hij
    exact e.symm.injective (Subtype.ext h)
  · ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).2
    · intro hφ
      exact ⟨e ⟨φ, hφ⟩, by simp⟩

/-- Reindex a sum over the `Finset` of a range by the indexing family: for an injective `f` over a
finite domain, `∑_{x ∈ (Set.range f).toFinset} g x = ∑ j, g (f j)`.  Used to turn the `S₁`-set
degree-square sum of the (6.2) bound into the `Fin k` member-family sum produced by B1. -/
theorem sum_toFinset_range_eq {α β M : Type*} [Fintype α] [DecidableEq β] [AddCommMonoid M]
    {f : α → β} (hinj : Function.Injective f) (g : β → M) :
    ∑ x ∈ (Set.range f).toFinset, g x = ∑ j, g (f j) := by
  rw [Set.toFinset_range, Finset.sum_image (fun a _ b _ h => hinj h)]

/-- **Degree-square partition (the (6.6) `hsum` core).**  For a finite character set `Xfin` whose
real degree-square sum is a natural number `totalN`, and an injective member subfamily `memb`
contained in `Xfin`, the natural degree-square sum splits as members `+` tail (`Xfin ∖ members`)
`= totalN`.  Pure `Finset.sum_image` + `Finset.sum_sdiff` + an ℝ→ℕ cast; no character theory.  The
producer supplies `deg φ = |L:K|·p^(eφ)` and `totalN = |L:K|·(|K|−|K:Z|)` (via
`sum_re_sq_xSet_eq`, or `sum_re_sq_Xset_eq` on the Sibley side). -/
theorem natSum_partition_of_realSum {α : Type*} [DecidableEq α]
    (Xfin : Finset α) (deg : α → ℕ) (totalN : ℕ)
    (hXsum : (∑ φ ∈ Xfin, ((deg φ : ℝ)) ^ 2) = (totalN : ℝ))
    {k : ℕ} {memb : Fin k → α} (hinj : Function.Injective memb)
    (hsub : ∀ j, memb j ∈ Xfin) :
    (∑ j : Fin k, deg (memb j) * deg (memb j))
      + (∑ φ ∈ Xfin \ Finset.univ.image memb, deg φ * deg φ) = totalN := by
  classical
  have hmembers : Finset.univ.image memb ⊆ Xfin := by
    intro φ hφ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hφ
    exact hsub j
  have hreindex : ∑ φ ∈ Finset.univ.image memb, deg φ * deg φ
      = ∑ j : Fin k, deg (memb j) * deg (memb j) :=
    Finset.sum_image (fun a _ b _ h => hinj h)
  have hXsumN : ∑ φ ∈ Xfin, deg φ * deg φ = totalN := by
    have h : ((∑ φ ∈ Xfin, deg φ * deg φ : ℕ) : ℝ) = (totalN : ℝ) := by
      rw [← hXsum, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun φ _ => by push_cast; ring)
    exact_mod_cast h
  rw [← hreindex, add_comm, Finset.sum_sdiff hmembers]
  exact hXsumN

/-- **(T8 leaf 10, combinatorial core) the conjugate-pair cover of `X` over a base `S₀`.**

Given a finite set `X` of irreducible characters of `Γ`, closed under conjugation and with no real
characters (Peterfalvi (1.1): for `|Γ|` odd a nontrivial irreducible is non-self-conjugate), and a
conjugation-closed base `S₀ ⊆ X`, the complement `X ∖ S₀` is a disjoint union of conjugate pairs
`{χ, χ̄}`.  This packages the data and facts consumed by `peterfalvi_66_coherence_of_X_from_dade`:
the degree-monotone enumeration `e` (`exists_monotoneDegreeEnum`), the pair list `pair`/`N` with its
irreducible first components `hpairχ`, the inclusions and index-level cover, plus the two facts the
per-step (5.6) `DadeChainStep` needs — each adjoined pair is **disjoint from the prefix**
`pairUnion S₀ pair j` (so `χⱼ, χ̄ⱼ ⊥ S₁`) and **degree-monotone** (so the (5.6) degree gap
can hold).

Construction: the conjugate-index involution `cidx i` (`e (cidx i) = (e i).conj`, fixed-point-free
by no-real, preserving `∉ S₀`), the index transversal `T = {i | e i ∉ S₀ ∧ i < cidx i}` sorted by
`Finset.orderEmbOfFin`, and `pair j = (e tⱼ, (e tⱼ).conj)` for the `j`-th transversal index `tⱼ`. -/
theorem exists_conjugatePairCover {Γ : Type*} [Group Γ]
    {X S₀ : Set (ClassFunction Γ ℂ)}
    (hXfin : X.Finite)
    (hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate X)
    (hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters X)
    (hXirr : ∀ χ ∈ X, IsIrreducibleCharacter χ)
    (hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₀) :
    ∃ (e : Fin X.ncard → ClassFunction Γ ℂ)
      (pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ) (N : ℕ)
      (hpairχ : ∀ i, i < N → IrreducibleCharacter Γ),
      (∀ χ ∈ X, ∃ i, e i = χ) ∧
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X) ∧
      (∀ i : Fin X.ncard, e i ∈ S₀ ∨
        ∃ j, j < N ∧ e i ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j) ∧
      (∀ (i : ℕ) (hi : i < N),
        (pair i).1 = ((hpairχ i hi : IrreducibleCharacter Γ) : ClassFunction Γ ℂ)) ∧
      (∀ (i : ℕ) (hi : i < N),
        (pair i).2 = ((hpairχ i hi : IrreducibleCharacter Γ) : ClassFunction Γ ℂ).conj) ∧
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair j)) ∧
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) := by
  classical
  obtain ⟨e, he_inj, he_mem, he_surj, he_mono⟩ :=
    OddOrder.Peterfalvi.S07.exists_monotoneDegreeEnum (L := Γ) hXfin
  -- conjugate-index involution `cidx`
  have hconjX : ∀ i, (e i).conj ∈ X := fun i => hXconj (he_mem i)
  let cidx : Fin X.ncard → Fin X.ncard := fun i => (he_surj _ (hconjX i)).choose
  have hcidx : ∀ i, e (cidx i) = (e i).conj := fun i => (he_surj _ (hconjX i)).choose_spec
  have hcidx_invol : ∀ i, cidx (cidx i) = i := fun i =>
    he_inj (by rw [hcidx (cidx i), hcidx i, ClassFunction.conj_conj])
  have hcidx_inj : Function.Injective cidx := fun a b h => by
    rw [← hcidx_invol a, h, hcidx_invol b]
  have hcidx_ne : ∀ i, cidx i ≠ i := by
    intro i hfix
    apply hXreal (he_mem i)
    change (e i).conj = e i
    rw [← hcidx i, hfix]
  have hcidx_notS₀ : ∀ {i}, e i ∉ S₀ → e (cidx i) ∉ S₀ := by
    intro i hi hc
    rw [hcidx i] at hc
    exact hi (by simpa using hS₀conj hc)
  -- index transversal `T`, enumerated by `orderEmbOfFin`
  let T : Finset (Fin X.ncard) := Finset.univ.filter (fun i => e i ∉ S₀ ∧ i < cidx i)
  let t : Fin T.card → Fin X.ncard := fun j => T.orderEmbOfFin rfl j
  have htmono : StrictMono t := (T.orderEmbOfFin rfl).strictMono
  have ht_mem : ∀ j, t j ∈ T := fun j => T.orderEmbOfFin_mem rfl j
  have ht_spec : ∀ j, e (t j) ∉ S₀ ∧ t j < cidx (t j) := fun j =>
    (Finset.mem_filter.mp (ht_mem j)).2
  have ht_range : ∀ i ∈ T, ∃ j, t j = i := by
    intro i hi
    have hmem : i ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hi
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩
  -- the pair list
  let pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ := fun j =>
    if hj : j < T.card then (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) else (0, 0)
  have hpair_eq : ∀ (j : ℕ) (hj : j < T.card),
      pair j = (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) := fun j hj => dif_pos hj
  have hfst : ∀ (j : ℕ) (hj : j < T.card), (pair j).1 = e (t ⟨j, hj⟩) := by
    intro j hj; rw [hpair_eq j hj]
  have hsnd : ∀ (j : ℕ) (hj : j < T.card), (pair j).2 = e (cidx (t ⟨j, hj⟩)) := by
    intro j hj; rw [hpair_eq j hj]; exact (hcidx _).symm
  refine ⟨e, pair, T.card, fun i hi => ⟨e (t ⟨i, hi⟩), hXirr _ (he_mem _)⟩,
    he_surj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- each pair lies in `X`
    intro j hj φ hφ
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφ
    rcases hφ with rfl | rfl
    · exact he_mem _
    · exact he_mem _
  · -- index-level cover
    intro i
    by_cases hiS₀ : e i ∈ S₀
    · exact Or.inl hiS₀
    · refine Or.inr ?_
      rcases lt_or_gt_of_ne (hcidx_ne i) with hlt | hgt
      · -- `cidx i < i` ⟹ `cidx i ∈ T`, and `e i` is the second component of its pair
        have hcT : cidx i ∈ T := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcidx_notS₀ hiS₀, by rw [hcidx_invol]; exact hlt⟩
        obtain ⟨j, hj⟩ := ht_range _ hcT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inr ?_
        rw [hsnd j.val j.isLt]
        have hci : cidx (t ⟨j.val, j.isLt⟩) = i := by
          rw [(hj : t ⟨j.val, j.isLt⟩ = cidx i)]; exact hcidx_invol i
        rw [hci]
      · -- `i < cidx i` ⟹ `i ∈ T`, and `e i` is the first component of its pair
        have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS₀, hgt⟩
        obtain ⟨j, hj⟩ := ht_range _ hiT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inl ?_
        rw [hfst j.val j.isLt]
        exact congrArg e hj.symm
  · -- `(pair i).1 = χᵢ`
    intro i hi; rw [hfst i hi]
  · -- `(pair i).2 = χ̄ᵢ`
    intro i hi; rw [hsnd i hi, hcidx]
  · -- each pair is disjoint from the prefix accumulated before it
    intro j hj
    rw [Set.disjoint_left]
    intro φ hφj hφu
    rw [OddOrder.Peterfalvi.S07.mem_pairUnion] at hφu
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφj
    rcases hφu with hS₀mem | ⟨k, hkj, hφk⟩
    · rcases hφj with rfl | rfl
      · exact (ht_spec ⟨j, hj⟩).1 hS₀mem
      · exact hcidx_notS₀ (ht_spec ⟨j, hj⟩).1 hS₀mem
    · have hk : k < T.card := hkj.trans hj
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
        hfst k hk, hsnd k hk] at hφk
      have htlt : t ⟨k, hk⟩ < t ⟨j, hj⟩ := htmono (Fin.mk_lt_mk.mpr hkj)
      have hjT := (ht_spec ⟨j, hj⟩).2
      rcases hφj with hj1 | hj1 <;> rcases hφk with hk1 | hk1
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
      · have heq : t ⟨j, hj⟩ = cidx (t ⟨k, hk⟩) := he_inj (hj1.symm.trans hk1)
        have hc : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := by rw [heq, hcidx_invol]
        rw [hc] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have heq : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [heq] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := hcidx_inj (he_inj (hj1.symm.trans hk1))
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
  · -- adjacent pairs are degree-monotone
    intro j hj1
    have hj : j < T.card := by omega
    rw [hfst j hj, hfst (j + 1) hj1]
    exact he_mono (htmono.monotone (Fin.mk_le_mk.mpr (by omega)))

/-- **Conjugate-pair cover without the irreducibility hypothesis** — the (6.8.3)/case-(c2)
generalization of `exists_conjugatePairCover`.  Identical construction, but `X` is an arbitrary
conjugation-closed real-free set (NOT required irreducible).  The cost is dropping the
`IrreducibleCharacter`-typed `hpairχ` output: the pairs are returned as plain `ClassFunction`s with
the
direct conjugate relation `(pair i).2 = ((pair i).1).conj`. Needed for (6.8.3) in case (c2), where
the
set `S` contains the `w₂ − 1` reducible induced characters (so the break-pair `ψ` may be reducible).
The irreducibility hypothesis `hXirr` was used in the original *only* to package the pairs as
`IrreducibleCharacter`s; the conjugate-pair involution itself uses only `hXreal` + `hXconj`. -/
theorem exists_conjugatePairCover_general {Γ : Type*} [Group Γ]
    {X S₀ : Set (ClassFunction Γ ℂ)}
    (hXfin : X.Finite)
    (hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate X)
    (hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters X)
    (hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₀) :
    ∃ (e : Fin X.ncard → ClassFunction Γ ℂ)
      (pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ) (N : ℕ),
      (∀ χ ∈ X, ∃ i, e i = χ) ∧
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X) ∧
      (∀ i : Fin X.ncard, e i ∈ S₀ ∨
        ∃ j, j < N ∧ e i ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j) ∧
      (∀ (i : ℕ), i < N → (pair i).2 = ((pair i).1).conj) ∧
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair j)) ∧
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) := by
  classical
  obtain ⟨e, he_inj, he_mem, he_surj, he_mono⟩ :=
    OddOrder.Peterfalvi.S07.exists_monotoneDegreeEnum (L := Γ) hXfin
  have hconjX : ∀ i, (e i).conj ∈ X := fun i => hXconj (he_mem i)
  let cidx : Fin X.ncard → Fin X.ncard := fun i => (he_surj _ (hconjX i)).choose
  have hcidx : ∀ i, e (cidx i) = (e i).conj := fun i => (he_surj _ (hconjX i)).choose_spec
  have hcidx_invol : ∀ i, cidx (cidx i) = i := fun i =>
    he_inj (by rw [hcidx (cidx i), hcidx i, ClassFunction.conj_conj])
  have hcidx_inj : Function.Injective cidx := fun a b h => by
    rw [← hcidx_invol a, h, hcidx_invol b]
  have hcidx_ne : ∀ i, cidx i ≠ i := by
    intro i hfix
    apply hXreal (he_mem i)
    change (e i).conj = e i
    rw [← hcidx i, hfix]
  have hcidx_notS₀ : ∀ {i}, e i ∉ S₀ → e (cidx i) ∉ S₀ := by
    intro i hi hc
    rw [hcidx i] at hc
    exact hi (by simpa using hS₀conj hc)
  let T : Finset (Fin X.ncard) := Finset.univ.filter (fun i => e i ∉ S₀ ∧ i < cidx i)
  let t : Fin T.card → Fin X.ncard := fun j => T.orderEmbOfFin rfl j
  have htmono : StrictMono t := (T.orderEmbOfFin rfl).strictMono
  have ht_mem : ∀ j, t j ∈ T := fun j => T.orderEmbOfFin_mem rfl j
  have ht_spec : ∀ j, e (t j) ∉ S₀ ∧ t j < cidx (t j) := fun j =>
    (Finset.mem_filter.mp (ht_mem j)).2
  have ht_range : ∀ i ∈ T, ∃ j, t j = i := by
    intro i hi
    have hmem : i ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hi
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩
  let pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ := fun j =>
    if hj : j < T.card then (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) else (0, 0)
  have hpair_eq : ∀ (j : ℕ) (hj : j < T.card),
      pair j = (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) := fun j hj => dif_pos hj
  have hfst : ∀ (j : ℕ) (hj : j < T.card), (pair j).1 = e (t ⟨j, hj⟩) := by
    intro j hj; rw [hpair_eq j hj]
  have hsnd : ∀ (j : ℕ) (hj : j < T.card), (pair j).2 = e (cidx (t ⟨j, hj⟩)) := by
    intro j hj; rw [hpair_eq j hj]; exact (hcidx _).symm
  refine ⟨e, pair, T.card, he_surj, ?_, ?_, ?_, ?_, ?_⟩
  · -- each pair lies in `X`
    intro j hj φ hφ
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφ
    rcases hφ with rfl | rfl
    · exact he_mem _
    · exact he_mem _
  · -- index-level cover
    intro i
    by_cases hiS₀ : e i ∈ S₀
    · exact Or.inl hiS₀
    · refine Or.inr ?_
      rcases lt_or_gt_of_ne (hcidx_ne i) with hlt | hgt
      · have hcT : cidx i ∈ T := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcidx_notS₀ hiS₀, by rw [hcidx_invol]; exact hlt⟩
        obtain ⟨j, hj⟩ := ht_range _ hcT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inr ?_
        rw [hsnd j.val j.isLt]
        have hci : cidx (t ⟨j.val, j.isLt⟩) = i := by
          rw [(hj : t ⟨j.val, j.isLt⟩ = cidx i)]; exact hcidx_invol i
        rw [hci]
      · have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS₀, hgt⟩
        obtain ⟨j, hj⟩ := ht_range _ hiT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inl ?_
        rw [hfst j.val j.isLt]
        exact congrArg e hj.symm
  · -- conjugate relation `(pair i).2 = ((pair i).1).conj`
    intro i hi
    rw [hfst i hi, hsnd i hi, hcidx]
  · -- each pair is disjoint from the prefix accumulated before it
    intro j hj
    rw [Set.disjoint_left]
    intro φ hφj hφu
    rw [OddOrder.Peterfalvi.S07.mem_pairUnion] at hφu
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφj
    rcases hφu with hS₀mem | ⟨k, hkj, hφk⟩
    · rcases hφj with rfl | rfl
      · exact (ht_spec ⟨j, hj⟩).1 hS₀mem
      · exact hcidx_notS₀ (ht_spec ⟨j, hj⟩).1 hS₀mem
    · have hk : k < T.card := hkj.trans hj
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
        hfst k hk, hsnd k hk] at hφk
      have htlt : t ⟨k, hk⟩ < t ⟨j, hj⟩ := htmono (Fin.mk_lt_mk.mpr hkj)
      have hjT := (ht_spec ⟨j, hj⟩).2
      rcases hφj with hj1 | hj1 <;> rcases hφk with hk1 | hk1
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
      · have heq : t ⟨j, hj⟩ = cidx (t ⟨k, hk⟩) := he_inj (hj1.symm.trans hk1)
        have hc : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := by rw [heq, hcidx_invol]
        rw [hc] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have heq : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [heq] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := hcidx_inj (he_inj (hj1.symm.trans hk1))
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
  · -- adjacent pairs are degree-monotone
    intro j hj1
    have hj : j < T.card := by omega
    rw [hfst j hj, hfst (j + 1) hj1]
    exact he_mono (htmono.monotone (Fin.mk_le_mk.mpr (by omega)))

/-- A predicate true at `0` and false at `N` must flip somewhere: there is an index `i < N` with
`P i` true and `P (i + 1)` false.  (Discrete first-failure / boundary extraction, by induction on
`N`.) -/
theorem exists_index_predicate_break {P : ℕ → Prop} (h0 : P 0) :
    ∀ N, ¬ P N → ∃ i, i < N ∧ P i ∧ ¬ P (i + 1)
  | 0, hN => absurd h0 hN
  | N + 1, hN => by
    by_cases hPN : P N
    · exact ⟨N, Nat.lt_succ_self N, hPN, hN⟩
    · obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break h0 N hPN
      exact ⟨i, hiN.trans (Nat.lt_succ_self N), hPi, hnPi⟩

open scoped Classical in
/-- **First obstruction to coherence — the Peterfalvi (6.2) `S₁`/`S₂` decomposition.**

Given conjugation-closed sets `Sa ⊆ Sb` of irreducible characters of `↥L`, with `Sb` finite and
real-free, if `Sa` is coherent for an integral character map `τ` (on the support set `A`) but `Sb`
is not, then there is an intermediate conjugation-closed set `S₁` (`Sa ⊆ S₁ ⊆ Sb`) and a character
`ψ ∈ Sb` such that `S₁` is coherent but adjoining the conjugate pair `{ψ, ψ̄}` destroys coherence:
`S₁ ∪ {ψ, ψ̄}` is not coherent.

This is the decomposition cited at the start of the (6.2) proof ("By (b), there are sets `S₁` and
`S₂ = {ψ, ψ̄}` … such that `S₁` is coherent but `S₁ ∪ S₂` is not coherent").  Construction:
enumerate `Sb ∖ Sa` as conjugate pairs (`exists_conjugatePairCover`), so the running union
`pairUnion Sa pair i` rises from `Sa` (coherent) to `Sb` (not), and take the first pair whose
adjunction breaks coherence (`exists_index_predicate_break`). -/
theorem exists_coherentBreakPair
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) {A : Set ↥L}
    {Sa Sb : Set (ClassFunction ↥L ℂ)}
    (hsub : Sa ⊆ Sb) (hSbfin : Sb.Finite)
    (hSbconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sb)
    (hSbreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sb)
    (hSbirr : ∀ χ ∈ Sb, IsIrreducibleCharacter χ)
    (hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sa)
    (hSacoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sa A))
    (hSbncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sb A)) :
    ∃ (S₁ : Set (ClassFunction ↥L ℂ)) (ψ : ClassFunction ↥L ℂ),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ ∧ Sa ⊆ S₁ ∧ S₁ ⊆ Sb ∧ ψ ∈ Sb ∧
      ψ ∉ S₁ ∧ ψ.conj ∉ S₁ ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A) := by
  classical
  obtain ⟨e, pair, N, hpairχ, hsurj, hpairs, hcoverIdx, hpair0, hpair1, hdisj, _hmono⟩ :=
    exists_conjugatePairCover hSbfin hSbconj hSbreal hSbirr hSaconj
  -- the running union reaches `Sb` after `N` steps
  have hUN : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N = Sb :=
    OddOrder.Peterfalvi.S07.pairUnion_eq_of_enumCover hsurj hsub hpairs hcoverIdx
  -- the coherence predicate along the chain rises from `Sa` (true) to `Sb` (false)
  have hP0 : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair 0) A) := by
    rw [OddOrder.Peterfalvi.S07.pairUnion_zero]; exact hSacoh
  have hPN : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N) A) := by
    rw [hUN]; exact hSbncoh
  obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break
    (P := fun i => Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i) A)) hP0 N hPN
  -- the breaking pair `{ψ, ψ̄}` lies in `Sb` and is disjoint from the prefix `S₁`
  have hψpair : (pair i).1 ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet]
  have hconj2 : (pair i).2 = ((pair i).1).conj := by rw [hpair1 i hiN, hpair0 i hiN]
  have hψcpair : ((pair i).1).conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    rw [← hconj2]; simp [OddOrder.Peterfalvi.S07.pairSet]
  refine ⟨OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i, (pair i).1,
    ?_, ?_, ?_, hpairs i hiN hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψcpair, hPi, ?_⟩
  · -- `S₁` is closed under conjugation (base `Sa` is, each adjoined pair is)
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hSaconj hbase))
    · have hjN : j < N := hji.trans hiN
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ' | hφ'
        · right; rw [hφ', hpair0 j hjN, hpair1 j hjN]
        · left; rw [hφ', hpair1 j hjN, hpair0 j hjN]; simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  · -- `Sa ⊆ S₁`
    exact fun φ hφ => OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  · -- `S₁ ⊆ Sb`
    rw [← hUN]; exact OddOrder.Peterfalvi.S07.pairUnion_mono Sa pair hiN.le
  · -- `S₁ ∪ {ψ, ψ̄}` is not coherent (it is the next accumulator, where coherence fails)
    have hsplit : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair (i + 1) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i ∪ {(pair i).1, ((pair i).1).conj} :=
      OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair rfl hconj2
    rw [← hsplit]; exact hnPi

/-- **First obstruction to coherence without the irreducibility hypothesis** — the (6.8.3)/case-(c2)
generalization of `exists_coherentBreakPair`. `Sb` need only be conjugation-closed and real-free
(NOT
required irreducible), at the cost that the breaking character `ψ ∈ Sb` may itself be reducible.
Used
in (6.8.3) for case (c2), where `S` contains the `w₂ − 1` reducible induced characters; the
downstream
degree bound then uses the norm-weighted sum `χ(1)²/‖χ‖²` (valid for reducibles). -/
theorem exists_coherentBreakPair_general
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) {A : Set ↥L}
    {Sa Sb : Set (ClassFunction ↥L ℂ)}
    (hsub : Sa ⊆ Sb) (hSbfin : Sb.Finite)
    (hSbconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sb)
    (hSbreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sb)
    (hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sa)
    (hSacoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sa A))
    (hSbncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sb A)) :
    ∃ (S₁ : Set (ClassFunction ↥L ℂ)) (ψ : ClassFunction ↥L ℂ),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ ∧ Sa ⊆ S₁ ∧ S₁ ⊆ Sb ∧ ψ ∈ Sb ∧
      ψ ∉ S₁ ∧ ψ.conj ∉ S₁ ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A) := by
  classical
  obtain ⟨e, pair, N, hsurj, hpairs, hcoverIdx, hconjrel, hdisj, _hmono⟩ :=
    exists_conjugatePairCover_general hSbfin hSbconj hSbreal hSaconj
  have hUN : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N = Sb :=
    OddOrder.Peterfalvi.S07.pairUnion_eq_of_enumCover hsurj hsub hpairs hcoverIdx
  have hP0 : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair 0) A) := by
    rw [OddOrder.Peterfalvi.S07.pairUnion_zero]; exact hSacoh
  have hPN : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N) A) := by
    rw [hUN]; exact hSbncoh
  obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break
    (P := fun i => Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i) A)) hP0 N hPN
  have hψpair : (pair i).1 ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet]
  have hconj2 : (pair i).2 = ((pair i).1).conj := hconjrel i hiN
  have hψcpair : ((pair i).1).conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    rw [← hconj2]; simp [OddOrder.Peterfalvi.S07.pairSet]
  refine ⟨OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i, (pair i).1,
    ?_, ?_, ?_, hpairs i hiN hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψcpair, hPi, ?_⟩
  · intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hSaconj hbase))
    · have hjN : j < N := hji.trans hiN
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ' | hφ'
        · right; rw [hφ', hconjrel j hjN]
        · left; rw [hφ', hconjrel j hjN, ClassFunction.conj_conj]
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  · exact fun φ hφ => OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  · rw [← hUN]; exact OddOrder.Peterfalvi.S07.pairUnion_mono Sa pair hiN.le
  · have hsplit : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair (i + 1) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i ∪ {(pair i).1, ((pair i).1).conj} :=
      OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair rfl hconj2
    rw [← hsplit]; exact hnPi

end OddOrder.Peterfalvi.S08


