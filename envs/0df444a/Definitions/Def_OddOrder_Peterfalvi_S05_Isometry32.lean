-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_Isometry32
-- name    : OddOrder_Peterfalvi_S05_Isometry32
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:53:22.13643+00:00
-- url     : https://prove2.me/theorems/afc44935-0b0d-4252-a68d-38b205898d51
-- title:
--   Peterfalvi (3.5.1): the $\beta_{ij}$ family and the isometry $\sigma$ (opening part)
-- statement:
--   Part of the Peterfalvi §3 development of the isometry $\sigma$, computing the Gram matrix of the family $\beta_{ij}=\mathrm{Ind}_W^G\alpha_{ij}-1_G$ of (3.5.1) and an engine for Peterfalvi (1.3)(a).
--
--   Main definitions: `beta` ($\beta_{ij}=\mathrm{Ind}_W^G\alpha_{ij}-1_G$), `Afam` (a fixed choice of signed-triple sets $A_{ij}$) and `innerLeftFunctional` ($\varphi\mapsto\langle\varphi,f\rangle$). Results include `beta_inner` and its special cases when the index pairs agree in exactly one coordinate or differ in both, and `eq_zero_of_mem_of_inner_supported_eq_zero` (the (1.3)(a) vanishing engine).
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_Isometry32.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_Isometry32.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_SignedTripleGrid

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- **Peterfalvi (1.3)(a) engine** (vanishing on `A`).  If `f` is orthogonal to every class function
supported on the conjugation-closed set `A`, then `f` vanishes on `A`. -/
theorem eq_zero_of_mem_of_inner_supported_eq_zero
    {H : Type*} [Group H] [Fintype H] [Invertible (Nat.card H : ℂ)]
    {A : Set H} (hA : ∀ x ∈ A, ∀ h : H, h * x * h⁻¹ ∈ A)
    {f : ClassFunction H ℂ}
    (hf : ∀ φ : ClassFunction H ℂ, φ.support ⊆ A → ClassFunction.inner φ f = 0)
    {a : H} (ha : a ∈ A) : f a = 0 := by
  classical
  -- conjugation-closedness is an equivalence (conjugation permutes `A`)
  have hAconj : ∀ g h : H, h * g * h⁻¹ ∈ A ↔ g ∈ A := fun g h => by
    refine ⟨fun hc => ?_, fun hc => hA g hc h⟩
    have := hA _ hc h⁻¹
    simpa [mul_assoc] using this
  -- the masking `m = f · 1_A`, a class function since `A` is conjugation-closed
  have hconj : ∀ g h : H, (if h * g * h⁻¹ ∈ A then f (h * g * h⁻¹) else 0)
      = (if g ∈ A then f g else (0 : ℂ)) := fun g h => by
    by_cases hg : g ∈ A
    · rw [if_pos ((hAconj g h).mpr hg), if_pos hg, f.conj_eq]
    · rw [if_neg (fun hc => hg ((hAconj g h).mp hc)), if_neg hg]
  let m : ClassFunction H ℂ := ⟨fun x => if x ∈ A then f x else 0, hconj⟩
  have hmval : ∀ g, m g = if g ∈ A then f g else 0 := fun _ => rfl
  have hmsupp : m.support ⊆ A := fun g hg => by
    by_contra hgA
    exact (ClassFunction.mem_support.mp hg) (by rw [hmval, if_neg hgA])
  -- `innerSum m f = ↑(∑_g 1_A(g) · ‖f g‖²)`, a sum of nonnegative reals
  have he : ClassFunction.innerSum m f
      = ((∑ g : H, (if g ∈ A then Complex.normSq (f g) else 0) : ℝ) : ℂ) := by
    rw [ClassFunction.innerSum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hmval]
    by_cases hg : g ∈ A
    · rw [if_pos hg, if_pos hg, Complex.star_def, Complex.mul_conj]
    · rw [if_neg hg, if_neg hg, zero_mul, Complex.ofReal_zero]
  -- `⟨m, f⟩ = 0 ⟹ ∑ ‖f‖²·1_A = 0 ⟹ each term 0`
  have h0 : ClassFunction.innerSum m f = 0 := by
    rw [← ClassFunction.card_mul_inner, hf m hmsupp, mul_zero]
  rw [he, Complex.ofReal_eq_zero] at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun g _ => by
    by_cases hg : g ∈ A
    · rw [if_pos hg]; exact Complex.normSq_nonneg _
    · rw [if_neg hg]).mp h0 a (Finset.mem_univ a)
  rw [if_pos ha] at hterm
  exact Complex.normSq_eq_zero.mp hterm

/-- The linear functional `φ ↦ ⟨φ, f⟩` on class functions (linear in the *left* argument,
since `⟨·, ·⟩` is conjugate-linear on the right).  Used to phrase "`f ⊥ CF(H, A)`" as the
vanishing of a linear map on a basis. -/
def innerLeftFunctional {H : Type*} [Group H] [Fintype H] [Invertible (Nat.card H : ℂ)]
    (f : ClassFunction H ℂ) : ClassFunction H ℂ →ₗ[ℂ] ℂ where
  toFun φ := ClassFunction.inner φ f
  map_add' a b := ClassFunction.inner_add_left a b f
  map_smul' c a := by simp only [ClassFunction.inner_smul_left, RingHom.id_apply, smul_eq_mul]

@[simp] theorem innerLeftFunctional_apply {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (f φ : ClassFunction H ℂ) :
    innerLeftFunctional f φ = ClassFunction.inner φ f := rfl

/-- **Abstract (3.8) core.** A `ℂ`-valued grid `a : ι × κ → ℂ` whose mixed differences vanish
(`a(i,j) + a(i',j') = a(i,j') + a(i',j)`, the (3.7) identity) and whose nonzero set is *smaller*
than `min |ι| |κ|` is identically zero.  Such a grid is additively separable, so its rows differ by
a column-independent constant: if two rows differ, every column carries a nonzero entry (`≥ |κ|`
nonzeros); otherwise all rows are equal, and a single nonzero entry fills a whole column (`≥ |ι|`
nonzeros).  Either way `min |ι| |κ| ≤ #support`, contradicting the hypothesis. -/
theorem grid_eq_zero_of_ncard_support_lt {ι κ : Type*} [Finite ι] [Finite κ]
    (a : ι × κ → ℂ)
    (hadd : ∀ i i' (j j' : κ), a (i, j) + a (i', j') = a (i, j') + a (i', j))
    (hlt : {x | a x ≠ 0}.ncard < min (Nat.card ι) (Nat.card κ))
    (x : ι × κ) : a x = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite _
  have : Fintype κ := Fintype.ofFinite _
  have : Fintype ↥{x : ι × κ | a x ≠ 0} := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card] at hlt
  by_contra hx
  set S := Finset.univ.filter (fun x => a x ≠ 0) with hS
  have hmem : ∀ {y : ι × κ}, y ∈ S ↔ a y ≠ 0 := by
    intro y; rw [hS, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ y)
  by_cases hrows : ∀ (i i' : ι) (j : κ), a (i, j) = a (i', j)
  · -- all rows equal: the column through `x` is entirely nonzero, so `|ι| ≤ #S`
    have hcol : (Finset.univ.image fun i => (i, x.2)) ⊆ S := by
      intro y hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
      obtain ⟨i, rfl⟩ := hy
      rw [hmem, hrows i x.1 x.2]
      exact hx
    have hcard : Fintype.card ι ≤ S.card := by
      have hinj : Function.Injective fun i : ι => (i, x.2) := fun a b h => by simpa using h
      calc Fintype.card ι = (Finset.univ.image fun i => (i, x.2)).card := by
            rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
        _ ≤ S.card := Finset.card_le_card hcol
    omega
  · -- two rows differ in some column ⟹ they differ in *every* column ⟹ `|κ| ≤ #S`
    push Not at hrows
    obtain ⟨i, i', j₀, hjj⟩ := hrows
    have hdiff : ∀ j, a (i, j) ≠ a (i', j) := fun j hj => by
      apply hjj
      have h1 := hadd i i' j j₀
      linear_combination hj - h1
    -- every column `j` contains a nonzero entry, so `S.image (·.2) = univ`
    have himg : S.image (fun y => y.2) = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro j
      rw [Finset.mem_image]
      by_cases h : a (i, j) = 0
      · exact ⟨(i', j), hmem.mpr fun hi' => hdiff j (h.trans hi'.symm), rfl⟩
      · exact ⟨(i, j), hmem.mpr h, rfl⟩
    have hcard : Fintype.card κ ≤ S.card := by
      calc Fintype.card κ = (S.image fun y => y.2).card := by rw [himg, Finset.card_univ]
        _ ≤ S.card := Finset.card_image_le
    omega

namespace TICyclicHypothesis

/-- **Peterfalvi (3.5.1)**: `β_{ij} = Ind_W^G α_{ij} - 1_G` (for `i, j ≥ 1`). -/
noncomputable def beta (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction G ℂ :=
  app.tau.toDadeMap (hyp.alpha hVeq χ₁ χ₂) - trivialClassFunction G

/-- `β_{ij} ∈ ℤ[Irr G]`: `Ind_W^G` preserves virtual characters (`α_{ij} ∈ ℤ[Irr W]`) and `1_G`
is a character. -/
theorem beta_mem_ZIrr (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.beta hVeq app χ₁ χ₂ ∈ ZIrr G :=
  Submodule.sub_mem _
    (app.tau.maps_virtualCharacter (hyp.alpha hVeq χ₁ χ₂) (hyp.alpha_mem_ZIrr hVeq χ₁ χ₂))
    (trivialClassFunction_isIrreducible.mem_ZIrr)

/-- **Peterfalvi (3.5.2)** input: every `β_{ij}` takes the value `-1` at `1 ∈ G`.  Indeed
`Ind_W^G α_{ij}(1) = [G : W] · α_{ij}(1) = 0` because `α_{ij}` vanishes on `W₁ ⊇ {1}`, so
`β_{ij}(1) = 0 - 1_G(1) = -1`.  In particular all the `β_{ij}` agree at `1`, which is what powers
the no-negatives half of `L(ij, i'j')` (Peterfalvi's `2χ₃ = Ind(α₁₁ - α₁₂)` vanishing at `1`). -/
theorem beta_apply_one (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.beta hVeq app χ₁ χ₂ : ClassFunction G ℂ) 1 = -1 := by
  change (app.tau.toDadeIsometryData.toDadeMap (hyp.alpha hVeq χ₁ χ₂) -
    trivialClassFunction G) 1 = -1
  rw [ClassFunction.sub_apply, trivialClassFunction_apply,
    hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq χ₁ χ₂),
    ClassFunction.induce_apply_one, hyp.alpha_coe,
    hyp.alphaCF_eq_zero_of_mem_W1_subgroupOf χ₁ χ₂ (Subgroup.one_mem _), mul_zero, zero_sub]

open Classical in
/-- **Peterfalvi (3.5.1)**: the Gram matrix of the `β_{ij}` family (`i, j ≥ 1`):
`⟨β_{ij}, β_{kl}⟩ = δ_{ik} + δ_{jl} + δ_{(ij),(kl)}`.  Subtracting `1_G` from the induced family
(whose Gram matrix is `tau_alpha_inner`) drops each entry by `1` (Frobenius
`tau_alpha_inner_trivial` and `⟨1_G, 1_G⟩ = 1`), giving `3` on the diagonal, `1` for one shared
index, and `0` when both indices differ. -/
theorem beta_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) =
      (if a₁ = b₁ then 1 else 0) + (if a₂ = b₂ then 1 else 0)
        + (if a₁ = b₁ ∧ a₂ = b₂ then 1 else 0) := by
  change ClassFunction.inner
      (app.tau.toDadeMap (hyp.alpha hVeq a₁ a₂) - trivialClassFunction G)
      (app.tau.toDadeMap (hyp.alpha hVeq b₁ b₂) - trivialClassFunction G) = _
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hyp.tau_alpha_inner hVeq app ha₁ ha₂ hb₁ hb₂,
    hyp.tau_alpha_inner_trivial hVeq app ha₁ ha₂,
    inner_conj_symm (app.tau.toDadeMap (hyp.alpha hVeq b₁ b₂)) (trivialClassFunction G),
    hyp.tau_alpha_inner_trivial hVeq app hb₁ hb₂, inner_trivialClassFunction_self]
  simp only [star_one]
  ring

/-- **Peterfalvi (3.5.1)**: `‖β_{ij}‖² = 3` for `i, j ≥ 1`. -/
theorem beta_inner_self (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app a₁ a₂) = 3 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ ha₁ ha₂]
  norm_num

/-- **Peterfalvi (3.5.1)**: `⟨β_{ij}, 1_G⟩ = 0` for `i, j ≥ 1` (Frobenius `⟨Ind α_{ij}, 1_G⟩ = 1`
cancels `⟨1_G, 1_G⟩ = 1`). -/
theorem beta_inner_trivial (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (trivialClassFunction G) = 0 := by
  change ClassFunction.inner
      (app.tau.toDadeMap (hyp.alpha hVeq a₁ a₂) - trivialClassFunction G)
      (trivialClassFunction G) = 0
  rw [ClassFunction.inner_sub_left, hyp.tau_alpha_inner_trivial hVeq app ha₁ ha₂,
    inner_trivialClassFunction_self, sub_self]

/-- `β_{ij}` packaged as a signed triple: `∃ A, IsSignedTriple β_{ij} A`. -/
theorem exists_isSignedTriple_beta (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) :
    ∃ A : Finset (ClassFunction G ℂ), IsSignedTriple (hyp.beta hVeq app a₁ a₂) A :=
  exists_isSignedTriple_of_inner_self_three (hyp.beta_mem_ZIrr hVeq app a₁ a₂)
    (hyp.beta_inner_self hVeq app ha₁ ha₂) (hyp.beta_inner_trivial hVeq app ha₁ ha₂)

open Classical in
/-- `⟨β_{ij}, β_{i'j'}⟩ = 1` when the two index pairs agree in **exactly one** coordinate
(`i = i', j ≠ j'` or `i ≠ i', j = j'`).  Immediate from the Gram matrix `beta_inner`. -/
theorem beta_inner_eq_one_of_one_shared (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hshared : (a₁ = b₁ ∧ a₂ ≠ b₂) ∨ (a₁ ≠ b₁ ∧ a₂ = b₂)) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) = 1 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ hb₁ hb₂]
  rcases hshared with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; norm_num
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; norm_num

open Classical in
/-- `⟨β_{ij}, β_{i'j'}⟩ = 0` when the two index pairs differ in **both** coordinates
(`i ≠ i'`, `j ≠ j'`).  Immediate from the Gram matrix `beta_inner`. -/
theorem beta_inner_eq_zero_of_both_diff (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {a₁ b₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {a₂ b₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) (ha₂ : a₂ ≠ 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hd₁ : a₁ ≠ b₁) (hd₂ : a₂ ≠ b₂) :
    ClassFunction.inner (hyp.beta hVeq app a₁ a₂) (hyp.beta hVeq app b₁ b₂) = 0 := by
  rw [hyp.beta_inner hVeq app ha₁ ha₂ hb₁ hb₂, if_neg hd₁, if_neg hd₂, if_neg (fun h => hd₁ h.1)]
  norm_num

/-- **Peterfalvi (3.5.3)**: `sup(w₁, w₂) ≥ 5`.  Both `w₁ = |W₁|` and `w₂ = |W₂|` are odd (dividing
the odd `|W|`), greater than `1` (`W₁`, `W₂` nontrivial), and coprime (Hypothesis (3.1)).  Were
both `≤ 4`, each would equal `3` (the only odd number in `(1, 4]`), contradicting coprimality
(`gcd 3 3 = 3 ≠ 1`).  Peterfalvi then assumes `w₁ ≥ 5` by the `W₁ ↔ W₂` symmetry. -/
theorem sup_card_ge_five (hyp : TICyclicHypothesis G) :
    5 ≤ Nat.card hyp.W1 ∨ 5 ≤ Nat.card hyp.W2 := by
  have : Finite G := Finite.of_fintype G
  have h1odd : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have h2odd : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have h1gt : 1 < Nat.card hyp.W1 :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
  have h2gt : 1 < Nat.card hyp.W2 :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
  by_contra h
  obtain ⟨hlt1, hlt2⟩ := not_or.mp h
  rw [not_le] at hlt1 hlt2
  obtain ⟨k, hk⟩ := h1odd
  obtain ⟨l, hl⟩ := h2odd
  have hc1 : Nat.card hyp.W1 = 3 := by omega
  have hc2 : Nat.card hyp.W2 = 3 := by omega
  have hcop := hyp.W_card_coprime
  rw [hc1, hc2] at hcop
  exact absurd hcop (by decide)

/-- **Peterfalvi (3.5.1)**, family form: a fixed choice of signed-triple set `A_{ij}` for each
`β_{ij}` (`i, j ≥ 1`), indexed by pairs of nontrivial linear characters of `W₁`, `W₂`.  This is
the family the `(3.5.4)`-`(3.5.5)` combinatorics reason about. -/
noncomputable def Afam (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
    (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) : Finset (ClassFunction G ℂ) :=
  (hyp.exists_isSignedTriple_beta hVeq app p.2 q.2).choose

/-- `A_{ij}` is a signed triple for `β_{ij}`. -/
theorem Afam_isSignedTriple (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
    (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) :
    IsSignedTriple (hyp.beta hVeq app p.1 q.1) (hyp.Afam hVeq app p q) :=
  (hyp.exists_isSignedTriple_beta hVeq app p.2 q.2).choose_spec

open Classical in
/-- **Peterfalvi (3.5.2)** `L(ij, i'j')`, family form: `A_{ij}` and `A_{i'j'}` with index pairs
sharing exactly one coordinate intersect in one element, with no negated common element. -/
theorem Afam_L (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p p' : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}}
    {q q' : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}}
    (hshared : (p = p' ∧ q ≠ q') ∨ (p ≠ p' ∧ q = q')) :
    (hyp.Afam hVeq app p q ∩ hyp.Afam hVeq app p' q').card = 1 ∧
      ∀ x ∈ hyp.Afam hVeq app p q, -x ∉ hyp.Afam hVeq app p' q' := by
  refine (hyp.Afam_isSignedTriple hVeq app p q).L_of_inner_one
    (hyp.Afam_isSignedTriple hVeq app p' q') ?_ ?_
  · apply hyp.beta_inner_eq_one_of_one_shared hVeq app p.2 q.2 p'.2 q'.2
    rcases hshared with ⟨rfl, hq⟩ | ⟨hp, rfl⟩
    · exact Or.inl ⟨rfl, fun h => hq (Subtype.ext h)⟩
    · exact Or.inr ⟨fun h => hp (Subtype.ext h), rfl⟩
  · rw [hyp.beta_apply_one, hyp.beta_apply_one]

open Classical in
/-- **Peterfalvi (3.5.2)** `O(ij, i'j')`, family form: `A_{ij}` and `A_{i'j'}` with both indices
different satisfy `|A_{ij} ∩ A_{i'j'}| = |{x ∈ A_{ij} : -x ∈ A_{i'j'}}|`. -/
theorem Afam_O (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp)
    {p p' : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}}
    {q q' : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}}
    (hp : p ≠ p') (hq : q ≠ q') :
    (hyp.Afam hVeq app p q ∩ hyp.Afam hVeq app p' q').card =
      ((hyp.Afam hVeq app p q).filter (fun x => -x ∈ hyp.Afam hVeq app p' q')).card :=
  (hyp.Afam_isSignedTriple hVeq app p q).O_card_inter_eq (hyp.Afam_isSignedTriple hVeq app p' q')
    (hyp.beta_inner_eq_zero_of_both_diff hVeq app p.2 q.2 p'.2 q'.2
      (fun h => hp (Subtype.ext h)) (fun h => hq (Subtype.ext h)))

/-- The fixed family `Afam` is a signed-triple grid (`IsSignedTripleGrid`), indexed by nontrivial
linear characters of `W₁` (rows) and `W₂` (columns).  Bundles `Afam_isSignedTriple`/`Afam_L`/
`Afam_O` so the abstract (3.5.4) sunflower argument applies to the `β`-family. -/
theorem Afam_isSignedTripleGrid (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (app : FullDadeApplication (G := G) hyp) :
    IsSignedTripleGrid (fun (p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1})
      (q : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) => hyp.Afam hVeq app p q) where
  card_eq_three p q := (hyp.Afam_isSignedTriple hVeq app p q).card_eq_three
  signed p q := (hyp.Afam_isSignedTriple hVeq app p q).signed
  orthogonal p q := (hyp.Afam_isSignedTriple hVeq app p q).pairwise_orthogonal
  inter_L _ _ _ _ hshared := (hyp.Afam_L hVeq app hshared).1
  noNeg_L _ _ _ _ hshared := (hyp.Afam_L hVeq app hshared).2
  inter_O _ _ _ _ hp hq := hyp.Afam_O hVeq app hp hq

open scoped Classical in
/-- **Peterfalvi (3.5.4)** for the fixed family `A_{ij}`, in the `w₁ ≥ 5` orientation: there is a
*unique* signed irreducible `z = -χ₀₁` common to every `A_{χ₁ χ₂₀}` as `χ₁` ranges over the
nontrivial characters of `W₁`.  This activates the abstract sunflower `existsUnique_common` on the
concrete `Afam` grid: the `≥ 4` rows come from `|W₁| ≥ 5` via `|Irr(W₁') ∖ {1}| = |W₁| − 1`
(Pontryagin `card_charGroup_subgroupOf`).  When only `|W₂| ≥ 5`, apply this to `transpose`. -/
theorem Afam_existsUnique_common (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : 5 ≤ Nat.card hyp.W1)
    {χ₂₀ χ₂₁ : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}} (hne : χ₂₀ ≠ χ₂₁) :
    ∃! z, ∀ χ₁ : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1},
      z ∈ hyp.Afam hVeq app χ₁ χ₂₀ := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have hcard : 4 ≤ Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    have h1 : Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}
        = Nat.card hyp.W1 - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
        hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    rw [h1]; omega
  exact (hyp.Afam_isSignedTripleGrid hVeq app).existsUnique_common hcard hne

open scoped Classical in
/-- **Column-common family** (the `-χ_{0j}` of (3.5)): when `w₁ ≥ 5`, each column `χ₂` (nontrivial)
of the `Afam` grid has a common element `z χ₂ ∈ A_{χ₁, χ₂}` for every row `χ₁`
(`existsUnique_common`,
which needs `≥ 4` rows `= w₁ ≥ 5`).  A witness column `χ₂' ≠ χ₂` exists because `w₂ ≥ 3`. -/
theorem exists_colCommon (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : 5 ≤ Nat.card hyp.W1) :
    ∃ z : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} → ClassFunction G ℂ,
      ∀ q p, z q ∈ hyp.Afam hVeq app p q := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Nontrivial {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    have hodd : Odd (Nat.card hyp.W2) :=
      hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
    have hgt : 1 < Nat.card hyp.W2 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
    obtain ⟨k, hk⟩ := hodd; omega
  have hcol : ∀ q, ∃ z, ∀ p, z ∈ hyp.Afam hVeq app p q := fun q => by
    obtain ⟨q', hq'⟩ := exists_ne q
    exact ⟨_, (hyp.Afam_existsUnique_common hVeq app hw1 (Ne.symm hq')).choose_spec.1⟩
  choose z hz using hcol
  exact ⟨z, hz⟩

open scoped Classical in
/-- **Row-common family** (the `-χ_{i0}` of (3.5) in the `w₂ ≥ 5` case): when `w₂ ≥ 5`, each row
`χ₁` (nontrivial) has a common element `w χ₁ ∈ A_{χ₁, χ₂}` for every column `χ₂`.  Obtained by
applying `existsUnique_common` to the `transpose` grid (whose `≥ 4` rows are the `w₂ ≥ 5` columns);
a witness row `χ₁' ≠ χ₁` exists because `w₁ ≥ 3`. -/
theorem exists_rowCommon (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw2 : 5 ≤ Nat.card hyp.W2) :
    ∃ w : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} → ClassFunction G ℂ,
      ∀ p q, w p ∈ hyp.Afam hVeq app p q := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Nontrivial {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    have hodd : Odd (Nat.card hyp.W1) :=
      hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
    have hgt : 1 < Nat.card hyp.W1 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
    obtain ⟨k, hk⟩ := hodd; omega
  have hcardκ : 4 ≤ Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W2_le_W]; omega
  have hrow : ∀ p, ∃ w, ∀ q, w ∈ hyp.Afam hVeq app p q := fun p => by
    obtain ⟨p', hp'⟩ := exists_ne p
    exact ⟨_, ((hyp.Afam_isSignedTripleGrid hVeq app).transpose.existsUnique_common hcardκ
      (Ne.symm hp')).choose_spec.1⟩
  choose w hw using hrow
  exact ⟨w, hw⟩

open scoped Classical in
/-- **(3.5) χ-assembly** (case-independent core): given the `(3.5.5)` cell decomposition of the
`Afam` grid into column-anchors `z`, row-anchors `w`, and interior thirds `φ`
(`A_{pq} = {z q, w p, φ p q}`) together with the orthonormality of `gridFamily z w φ`, build the
family `(χ_{pq})` over `Ĉ₁ × Ĉ₂` of (3.5): `χ_{00} = 1_G`, `χ_{p0} = -w p`, `χ_{0q} = -z q`,
`χ_{pq} = φ p q`.  It is orthonormal, lies in `ZIrr`, and satisfies
`Ind α_{pq} = 1_G - χ_{p0} - χ_{0q} + χ_{pq}`.  The three orientations of (3.5)
(`w₂ ≥ 5` symmetric, `w₂ = 3`, and the transpose `w₁ = 3`) differ only in how `(z, w, φ)` is
produced; the orthonormality lift (negating individual members, adjoining `1_G ⊥` signed) and the
`Ind` relation (cell sum `β = z + w + φ`) are shared here. -/
theorem exists_chiFamily_of_decomposition (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {z : {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} → ClassFunction G ℂ}
    {w : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} → ClassFunction G ℂ}
    {φ : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} →
        {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} → ClassFunction G ℂ}
    (hcells : ∀ p q, hyp.Afam hVeq app p q = {z q, w p, φ p q})
    (hdiag0 : ∀ a, ClassFunction.inner
        (IsSignedTripleGrid.gridFamily z w φ a) (IsSignedTripleGrid.gridFamily z w φ a) = 1)
    (hoff0 : ∀ a b, a ≠ b → ClassFunction.inner
        (IsSignedTripleGrid.gridFamily z w φ a) (IsSignedTripleGrid.gridFamily z w φ b) = 0) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Nonempty {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [← Fintype.card_pos_iff, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    have hgt : 1 < Nat.card hyp.W1 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
    omega
  have : Nonempty {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [← Fintype.card_pos_iff, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    have hgt : 1 < Nat.card hyp.W2 := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
    omega
  have hgrid := hyp.Afam_isSignedTripleGrid hVeq app
  -- every column-anchor, row-anchor, and interior third is a signed nontrivial irreducible
  have hsigw : ∀ p, IsSignedNontrivialIrr (w p) := fun p =>
    hgrid.signed p (Classical.arbitrary _) _ (by
      rw [hcells p (Classical.arbitrary _)]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hsigz : ∀ q, IsSignedNontrivialIrr (z q) := fun q =>
    hgrid.signed (Classical.arbitrary _) q _ (by
      rw [hcells (Classical.arbitrary _) q]; exact Finset.mem_insert_self _ _)
  have hsigφ : ∀ p q, IsSignedNontrivialIrr (φ p q) := fun p q =>
    hgrid.signed p q _ (by
      rw [hcells p q]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  -- repackage the `gridFamily` orthonormality as a single `ite`, elaborated here (concrete index)
  -- so the assembly's `if_neg` rewrites use the matching `Decidable` instance
  have hortho : ∀ a b, ClassFunction.inner
      (IsSignedTripleGrid.gridFamily z w φ a) (IsSignedTripleGrid.gridFamily z w φ b)
      = if a = b then 1 else 0 := fun a b => by
    split_ifs with h
    · subst h; exact hdiag0 a
    · exact hoff0 a b h
  -- abbreviations for the four χ-values
  set χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
      ClassFunction G ℂ := fun pq => if hp : pq.1 = 1 then
        (if hq : pq.2 = 1 then trivialClassFunction G else -z ⟨pq.2, hq⟩)
      else (if hq : pq.2 = 1 then -w ⟨pq.1, hp⟩ else φ ⟨pq.1, hp⟩ ⟨pq.2, hq⟩) with hχdef
  have hχ11 : χ (1, 1) = trivialClassFunction G := by
    simp only [hχdef, dif_pos]
  have hχp1 : ∀ (p) (hp : p ≠ 1), χ (p, 1) = -w ⟨p, hp⟩ := fun p hp => by
    simp only [hχdef, dif_neg hp, dif_pos]
  have hχ1q : ∀ (q) (hq : q ≠ 1), χ (1, q) = -z ⟨q, hq⟩ := fun q hq => by
    simp only [hχdef, dif_pos, dif_neg hq]
  have hχpq : ∀ (p q) (hp : p ≠ 1) (hq : q ≠ 1), χ (p, q) = φ ⟨p, hp⟩ ⟨q, hq⟩ := fun p q hp hq => by
    simp only [hχdef, dif_neg hp, dif_neg hq]
  -- the gridFamily values, as themselves (definitional), and `1_G ⊥ signed`
  have hgw : ∀ p, w p = IsSignedTripleGrid.gridFamily z w φ (Sum.inl p) := fun _ => rfl
  have hgz : ∀ q, z q = IsSignedTripleGrid.gridFamily z w φ (Sum.inr (Sum.inl q)) := fun _ => rfl
  have hgφ : ∀ p q, φ p q = IsSignedTripleGrid.gridFamily z w φ (Sum.inr (Sum.inr (p, q))) :=
    fun _ _ => rfl
  have h1Gx : ∀ {x : ClassFunction G ℂ}, IsSignedNontrivialIrr x →
      ClassFunction.inner (trivialClassFunction G) x = 0 := fun hx => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hx.inner_trivial, star_zero]
  refine ⟨χ, hχ11, ?_, ?_, ?_⟩
  · -- ZIrr
    rintro ⟨p, q⟩
    by_cases hp : p = 1 <;> by_cases hq : q = 1
    · subst hp; subst hq; rw [hχ11]; exact trivialClassFunction_isIrreducible.mem_ZIrr
    · subst hp; rw [hχ1q q hq]; exact Submodule.neg_mem _ (hsigz ⟨q, hq⟩).mem_ZIrr
    · subst hq; rw [hχp1 p hp]; exact Submodule.neg_mem _ (hsigw ⟨p, hp⟩).mem_ZIrr
    · rw [hχpq p q hp hq]; exact (hsigφ ⟨p, hp⟩ ⟨q, hq⟩).mem_ZIrr
  · -- orthonormality, via the diagonal (norm 1) and off-diagonal (orthogonal) facts
    have hdiag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1 := by
      rintro ⟨p, q⟩
      by_cases hp : p = 1 <;> by_cases hq : q = 1
      · subst hp; subst hq; rw [hχ11]; exact inner_trivialClassFunction_self G
      · subst hp; rw [hχ1q q hq, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg]; exact (hsigz _).inner_self
      · subst hq; rw [hχp1 p hp, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg]; exact (hsigw _).inner_self
      · rw [hχpq p q hp hq]; exact (hsigφ _ _).inner_self
    have hoff : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0 := by
      rintro ⟨p, q⟩ ⟨p', q'⟩ hab
      by_cases hp : p = 1 <;> by_cases hq : q = 1 <;> by_cases hp' : p' = 1 <;>
        by_cases hq' : q' = 1
      · subst hp; subst hq; subst hp'; subst hq'; exact absurd rfl hab
      · subst hp; subst hq; subst hp'
        rw [hχ11, hχ1q q' hq', ClassFunction.inner_neg_right, h1Gx (hsigz _), neg_zero]
      · subst hp; subst hq; subst hq'
        rw [hχ11, hχp1 p' hp', ClassFunction.inner_neg_right, h1Gx (hsigw _), neg_zero]
      · subst hp; subst hq
        rw [hχ11, hχpq p' q' hp' hq', h1Gx (hsigφ _ _)]
      · subst hp; subst hp'; subst hq'
        rw [hχ1q q hq, hχ11, ClassFunction.inner_neg_left, (hsigz _).inner_trivial, neg_zero]
      · subst hp; subst hp'
        rw [hχ1q q hq, hχ1q q' hq', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgz, hgz, hortho, if_neg (by
            simp only [ne_eq, Sum.inr.injEq, Sum.inl.injEq, Subtype.mk.injEq]
            exact fun h => hab (by rw [h]))]
      · subst hp; subst hq'
        rw [hχ1q q hq, hχp1 p' hp', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgz, hgw, hortho, if_neg (by simp)]
      · subst hp
        rw [hχ1q q hq, hχpq p' q' hp' hq', ClassFunction.inner_neg_left, hgz, hgφ, hortho,
          if_neg (by simp), neg_zero]
      · subst hq; subst hp'; subst hq'
        rw [hχp1 p hp, hχ11, ClassFunction.inner_neg_left, (hsigw _).inner_trivial, neg_zero]
      · subst hq; subst hp'
        rw [hχp1 p hp, hχ1q q' hq', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgw, hgz, hortho, if_neg (by simp)]
      · subst hq; subst hq'
        rw [hχp1 p hp, hχp1 p' hp', ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hgw, hgw, hortho, if_neg (by
            simp only [ne_eq, Sum.inl.injEq, Subtype.mk.injEq]
            exact fun h => hab (by rw [h]))]
      · subst hq
        rw [hχp1 p hp, hχpq p' q' hp' hq', ClassFunction.inner_neg_left, hgw, hgφ, hortho,
          if_neg (by simp), neg_zero]
      · subst hp'; subst hq'
        rw [hχpq p q hp hq, hχ11, (hsigφ _ _).inner_trivial]
      · subst hp'
        rw [hχpq p q hp hq, hχ1q q' hq', ClassFunction.inner_neg_right, hgφ, hgz, hortho,
          if_neg (by simp), neg_zero]
      · subst hq'
        rw [hχpq p q hp hq, hχp1 p' hp', ClassFunction.inner_neg_right, hgφ, hgw, hortho,
          if_neg (by simp), neg_zero]
      · rw [hχpq p q hp hq, hχpq p' q' hp' hq', hgφ, hgφ, hortho, if_neg (by
          simp only [ne_eq, Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq]
          exact fun h => hab (by rw [h.1, h.2]))]
    intro a b
    split_ifs with hab
    · subst hab; exact hdiag a
    · exact hoff a b hab
  · -- the Ind relation: `Ind α = 1_G + β` and `β = ∑ (cell) = z + w + φ`
    intro p q hp hq
    have hst := hyp.Afam_isSignedTriple hVeq app ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨hzw, hzφ, hwφ⟩ := triple_distinct (hcells ⟨p, hp⟩ ⟨q, hq⟩ ▸ hst.card_eq_three)
    have hbeta : hyp.beta hVeq app p q
        = z ⟨q, hq⟩ + (w ⟨p, hp⟩ + φ ⟨p, hp⟩ ⟨q, hq⟩) := by
      rw [hst.sum_eq, hcells ⟨p, hp⟩ ⟨q, hq⟩, Finset.sum_insert (by simp [hzw, hzφ]),
        Finset.sum_insert (by simp [hwφ]), Finset.sum_singleton]
    have hind : app.tau.toDadeMap (hyp.alpha hVeq p q)
        = hyp.beta hVeq app p q + trivialClassFunction G := by
      rw [show hyp.beta hVeq app p q
        = app.tau.toDadeMap (hyp.alpha hVeq p q) - trivialClassFunction G from rfl, sub_add_cancel]
    rw [hind, hbeta, hχp1 p hp, hχ1q q hq, hχpq p q hp hq]
    abel

open scoped Classical in
/-- **Peterfalvi (3.5)**, symmetric case `w₁, w₂ ≥ 5`: there is an orthonormal family `(χ_{ij})`
indexed by `Ĉ₁ × Ĉ₂ = Irr(W)` of virtual characters with `χ_{00} = 1_G` and
`Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` for `i, j ≥ 1`.  Assembled from the (3.5.5)
orthonormal `gridFamily` on `Afam` (column-commons `z`, row-commons `w`, interior thirds `φ`):
`χ_{i0} = -w`, `χ_{0j} = -z`, `χ_{ij} = φ`, `χ_{00} = 1_G`.  The orthonormality lifts the
`gridFamily` one (`symm_orthonormal_family`) by negating individual members (sign-invariant) and
adjoining `1_G` (orthogonal to the signed nontrivial irreducibles, `inner_trivial`); the `Ind`
relation is the cell sum `β_{ij} = z + w + φ` (`IsSignedTriple.sum_eq`). -/
theorem exists_chiFamily_symm (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : 5 ≤ Nat.card hyp.W1) (hw2 : 5 ≤ Nat.card hyp.W2) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨z, hz⟩ := hyp.exists_colCommon hVeq app hw1
  obtain ⟨w, hw⟩ := hyp.exists_rowCommon hVeq app hw2
  have hι : 4 ≤ Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W1_le_W]; omega
  have hκ : 4 ≤ Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W2_le_W]; omega
  obtain ⟨φ, hcells, hortho⟩ :=
    (hyp.Afam_isSignedTripleGrid hVeq app).symm_orthonormal_family hι hκ hz hw
  exact hyp.exists_chiFamily_of_decomposition hVeq app hcells
    (fun a => by rw [hortho a a, if_pos rfl]) (fun a b h => by rw [hortho a b, if_neg h])

open scoped Classical in
/-- **Peterfalvi (3.5)**, two-column case `w₁ ≥ 5`, `w₂ = 3`: there is an orthonormal family
`(χ_{ij})` over `Ĉ₁ × Ĉ₂ = Irr(W)` of virtual characters with `χ_{00} = 1_G` and
`Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` for `i, j ≥ 1`.  Here `W₂` has only two nontrivial
characters, so the column-anchors `z` (from `exists_colCommon`, which needs `w₁ ≥ 5`) live over a
two-element index; `two_col_orthonormal_family_reindexed` produces the per-row meets `w` and
interior
thirds `φ` with `A_{ij} = {z j, w i, φ i j}` and an orthonormal `gridFamily`, after which the
χ-family
is assembled by the shared `exists_chiFamily_of_decomposition`.  (This is the case Peterfalvi calls
"complete" after (3.5.5).) -/
theorem exists_chiFamily_two_col (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : 5 ≤ Nat.card hyp.W1) (hw2 : Nat.card hyp.W2 = 3) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨z, hz⟩ := hyp.exists_colCommon hVeq app hw1
  have hι : 4 ≤ Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W1_le_W]; omega
  have hκ2 : Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} = 2 := by
    have h2 : Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}
        = Nat.card hyp.W2 - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
        hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    omega
  obtain ⟨w, φ, hcells, hortho⟩ :=
    (hyp.Afam_isSignedTripleGrid hVeq app).two_col_orthonormal_family_reindexed hι hκ2 hz
  exact hyp.exists_chiFamily_of_decomposition hVeq app hcells
    (fun a => by rw [hortho a a, if_pos rfl]) (fun a b h => by rw [hortho a b, if_neg h])

open scoped Classical in
/-- **Peterfalvi (3.5)**, transpose case `w₁ = 3`, `w₂ ≥ 5`: the `W₁ ↔ W₂`-swapped counterpart of
`exists_chiFamily_two_col`.  Now `W₁` has only two nontrivial characters, so we run the two-column
construction on the **transposed** `Afam` grid (rows `= Ĉ₂` with `w₂ ≥ 5 ⟹ ≥ 4` rows, columns
`= Ĉ₁` with `w₁ = 3 ⟹ 2` columns), whose column-commons are the original *row*-commons
(`exists_rowCommon`, needs `w₂ ≥ 5`).  The transposed orthonormal `gridFamily` (over
`Ĉ₂ ⊕ Ĉ₁ ⊕ Ĉ₂ × Ĉ₁`) is relabelled to the standard `Ĉ₁ ⊕ Ĉ₂ ⊕ Ĉ₁ × Ĉ₂` layout (swap the two
anchors, transpose the interior product index) via the bijection `toT`, and the χ-family is then the
shared `exists_chiFamily_of_decomposition` with column-anchor `= wMeet` (transposed row-meet) and
row-anchor `= wRow` (original row-common). -/
theorem exists_chiFamily_transpose (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hw1 : Nat.card hyp.W1 = 3) (hw2 : 5 ≤ Nat.card hyp.W2) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨wRow, hwRow⟩ := hyp.exists_rowCommon hVeq app hw2
  have hκT : 4 ≤ Fintype.card {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W2_le_W]; omega
  have hιT2 : Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} = 2 := by
    have h2 : Fintype.card {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}
        = Nat.card hyp.W1 - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
        hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    omega
  obtain ⟨wMeet, φT, hcellsT, horthoT⟩ :=
    (hyp.Afam_isSignedTripleGrid hVeq app).transpose.two_col_orthonormal_family_reindexed
      hκT hιT2 (z := wRow) hwRow
  -- the standard-layout decomposition: column-anchor `= wMeet`, row-anchor `= wRow`
  have hcells : ∀ p q, hyp.Afam hVeq app p q = {wMeet q, wRow p, φT q p} := fun p q => by
    rw [hcellsT q p, Finset.insert_comm]
  -- relabel the transposed `gridFamily` layout to the standard one
  let toT : ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ×
          ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) →
      ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ×
          ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) := fun a => match a with
    | Sum.inl p => Sum.inr (Sum.inl p)
    | Sum.inr (Sum.inl q) => Sum.inl q
    | Sum.inr (Sum.inr (p, q)) => Sum.inr (Sum.inr (q, p))
  let fromT : ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ×
          ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) →
      ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ⊕
        ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ⊕
        ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1}) ×
          ({χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) := fun a => match a with
    | Sum.inl q => Sum.inr (Sum.inl q)
    | Sum.inr (Sum.inl p) => Sum.inl p
    | Sum.inr (Sum.inr (q, p)) => Sum.inr (Sum.inr (p, q))
  have htoT_inj : Function.Injective toT :=
    Function.LeftInverse.injective (g := fromT) (by rintro (p | q | ⟨p, q⟩) <;> rfl)
  have hgfeq : ∀ a, IsSignedTripleGrid.gridFamily wMeet wRow (fun p q => φT q p) a
      = IsSignedTripleGrid.gridFamily wRow wMeet φT (toT a) := by
    rintro (p | q | ⟨p, q⟩) <;> rfl
  exact hyp.exists_chiFamily_of_decomposition hVeq app (z := wMeet) (w := wRow)
    (φ := fun p q => φT q p) hcells
    (fun a => by rw [hgfeq a, horthoT (toT a) (toT a), if_pos rfl])
    (fun a b h => by rw [hgfeq a, hgfeq b, horthoT (toT a) (toT b),
      if_neg (fun hh => h (htoT_inj hh))])

open scoped Classical in
/-- **Peterfalvi (3.5)** (full): for any admissible `W = W₁ × W₂` there is an orthonormal family
`(χ_{ij})` indexed by `Ĉ₁ × Ĉ₂ = Irr(W)` of virtual characters with `χ_{00} = 1_G`, all `χ_{ij} ∈
ZIrr G`, and `Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` for `i, j ≥ 1`.  Since `|W₁|,
|W₂|` are
odd `> 1` (so `∈ {3, 5, 7, …}`) and `max(|W₁|, |W₂|) ≥ 5` (`sup_card_ge_five`), the three
orientations
cover every case: `w₁, w₂ ≥ 5` (`exists_chiFamily_symm`), `w₁ ≥ 5 ∧ w₂ = 3`
(`exists_chiFamily_two_col`), and `w₁ = 3 ∧ w₂ ≥ 5` (`exists_chiFamily_transpose`). -/
theorem exists_chiFamily (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    ∃ χ : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) →
        ClassFunction G ℂ,
      χ (1, 1) = trivialClassFunction G ∧ (∀ pq, χ pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (χ a) (χ b) = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - χ (p, 1) - χ (1, q) + χ (p, q) := by
  have : Finite G := Finite.of_fintype G
  have hodd1 : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have hodd2 : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have hgt1 : 1 < Nat.card hyp.W1 := Finite.one_lt_card_iff_nontrivial.mpr
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
  have hgt2 : 1 < Nat.card hyp.W2 := Finite.one_lt_card_iff_nontrivial.mpr
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
  rcases hyp.sup_card_ge_five with hw1 | hw2
  · -- `w₁ ≥ 5`: split on `w₂ = 3` vs `w₂ ≥ 5` (odd `> 1`)
    obtain ⟨k, hk⟩ := hodd2
    rcases (by omega : Nat.card hyp.W2 = 3 ∨ 5 ≤ Nat.card hyp.W2) with h3 | h5
    · exact hyp.exists_chiFamily_two_col hVeq app hw1 h3
    · exact hyp.exists_chiFamily_symm hVeq app hw1 h5
  · -- `w₂ ≥ 5`: either `w₁ ≥ 5` (symmetric) or `w₁ = 3` (transpose)
    by_cases hw1 : 5 ≤ Nat.card hyp.W1
    · exact hyp.exists_chiFamily_symm hVeq app hw1 hw2
    · obtain ⟨k, hk⟩ := hodd1
      exact hyp.exists_chiFamily_transpose hVeq app (by omega) hw2

/-- **`omegaProdChar` is surjective**: every linear character `ξ : W →* ℂˣ` equals `ω_{i0}·ω_{0j}`
for the restrictions `χ_k = ξ|_{W_k}`.  With `omegaProdChar_inj` this makes the product map a
bijection.  Uses the internal direct product reconstruction `w = wProj1 w · wProj2 w`. -/
theorem omegaProdChar_surjective (hyp : TICyclicHypothesis G) :
    Function.Surjective fun p : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) ×
      ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) => hyp.omegaProdChar p.1 p.2 := by
  intro ξ
  refine ⟨(ξ.comp (hyp.W1.subgroupOf hyp.W).subtype, ξ.comp (hyp.W2.subgroupOf hyp.W).subtype), ?_⟩
  ext w
  simp only [omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← map_mul]
  congr 1
  have e1 : (↑(hyp.wFst w) : hyp.W) = hyp.wProj1 w := by rw [wProj1_apply, wFst_apply]
  have e2 : (↑(hyp.wSnd w) : hyp.W) = hyp.wProj2 w := by rw [wProj2_apply, wSnd_apply]
  rw [e1, e2, wProj1_mul_wProj2]

/-- The product-character bijection `Ĉ₁ × Ĉ₂ ≃ (W →* ℂˣ)` (`omegaProdChar`, injective + surjective).
-/
noncomputable def omegaProdEquiv (hyp : TICyclicHypothesis G) :
    (((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) ≃ (hyp.W →* ℂˣ) :=
  Equiv.ofBijective (fun p => hyp.omegaProdChar p.1 p.2)
    ⟨fun _ _ h => Prod.ext (hyp.omegaProdChar_inj h).1 (hyp.omegaProdChar_inj h).2,
      hyp.omegaProdChar_surjective⟩

@[simp] theorem omegaProdEquiv_apply (hyp : TICyclicHypothesis G)
    (p : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.omegaProdEquiv p = hyp.omegaProdChar p.1 p.2 := rfl

/-- **(3.3) index bridge** `Ĉ₁ × Ĉ₂ ≃ Irr(W)`: the product-character bijection composed with
`omegaEquiv`.  Its inverse turns an irreducible character of `W` into the index pair at which the
(3.5) `χ`-family is evaluated, so `σ` can be defined on the `Irr(W)`-basis. -/
noncomputable def omegaIrrEquiv (hyp : TICyclicHypothesis G) :
    (((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) ≃
      IrreducibleCharacter hyp.W :=
  hyp.omegaProdEquiv.trans hyp.omegaEquiv

@[simp] theorem omegaIrrEquiv_apply (hyp : TICyclicHypothesis G)
    (p : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.omegaIrrEquiv p = hyp.omega (hyp.omegaProdChar p.1 p.2) := rfl

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05


