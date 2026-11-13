-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_BetaDecompOrthogonality
-- name    : OddOrder_Peterfalvi_S09_BetaDecompOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:04:12.884375+00:00
-- url     : https://prove2.me/theorems/43878360-6011-44cb-a7e5-ac4b88c814c2
-- title:
--   Peterfalvi (7.8.c) building blocks: the induced principal character on $A$
-- statement:
--   Peterfalvi's (7.8.c) collapse hinges on the fact that $\zeta_1=\mathrm{Ind}_K^L1_K$ satisfies $\zeta_1(x)=\|\zeta_1\|^2=[L:K]$ for $x\in K$, so that the single surviving (7.7.a) term simplifies to $\bar c_1=\mathrm{star}(\beta,\chi)$. This file provides the building blocks.
--
--   The bundle includes `conjBy_trivialClassFunction` (conjugation fixes the trivial class function).
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_BetaDecompOrthogonality.lean

/-
# Peterfalvi §7 — (7.8.c) building blocks: induced principal character and `betaDecomp`
orthogonality

Prefix-split from `OddOrder.Peterfalvi.S09_CertificateDischarge` (2000-line limit, CLAUDE.md
「ファイル粒度」; second split of that file — the first, issue 0103 第 2 パス, produced
`S09_Building78C`).  Content: the `Ind_K^L 1_K` facts (`ζ_1(x) = ‖ζ_1‖² = [L:K]` on `K`) and the
`(7.7.a)`-decomposition orthogonality machinery (`betaDecomp_orth_*`, `inner_beta_nu_*`,
`sum_collapse_to_single`, `inner_sub_smul_left_eq_zero`) feeding the `(7.8.c)` collapse in
`S09_CertificateDischarge`.
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_BetaDecompOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_Building78C

namespace OddOrder.Peterfalvi.S09.Cert

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L]

omit [Fintype L] in
/-- **Conjugation fixes the trivial class function.**  `(1_K)^g = 1_K` for any `g`, since the
trivial class function is constant `1`. -/
theorem conjBy_trivialClassFunction {K : Subgroup L} [K.Normal] (g : L) :
    ClassFunction.conjBy g (trivialClassFunction ↥K) = trivialClassFunction ↥K := by
  ext h
  simp only [ClassFunction.conjBy_apply, trivialClassFunction_apply]

/-- **The induced principal character is `[L:K]` on `K`** (Peterfalvi (7.8.c)).  For a normal
subgroup `K ◁ L` and `x ∈ K`, `(Ind_K^L 1_K)(x) = [L:K]`: every conjugate of `x` lies in `K`
(normality), so all `|L|` induction summands equal `1`, giving `|L|/|K| = [L:K]`. -/
theorem induce_trivialChar_apply_eq_index (K : Subgroup L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {x : L} (hx : x ∈ K) :
    ClassFunction.induce K (trivialClassFunction ↥K) x = (K.index : ℂ) := by
  have : Fintype ↥K := Fintype.ofFinite _
  rw [ClassFunction.induce_apply_of_mem_normal_of_const (le_refl K) (trivialClassFunction ↥K)
      (fun a' _ => trivialClassFunction_apply _) hx, mul_one,
    show (Nat.card L : ℂ) = (K.index : ℂ) * (Nat.card ↥K : ℂ) from by
      rw [← Nat.cast_mul, K.index_mul_card],
    show ⅟(Nat.card ↥K : ℂ) * ((K.index : ℂ) * (Nat.card ↥K : ℂ))
        = (K.index : ℂ) * (⅟(Nat.card ↥K : ℂ) * (Nat.card ↥K : ℂ)) from by ring,
    invOf_mul_self, mul_one]

/-- **The norm of the induced principal character is `[L:K]`** (Peterfalvi (7.8.c)).  For a normal
subgroup `K ◁ L`, `‖Ind_K^L 1_K‖² = [L:K]`: by `card_mul_inner_self_induce_eq_card_inertia`,
`|K| · ‖Ind 1_K‖² = |I_L(1_K)| = |L|` since the trivial character is `L`-invariant
(`inertia 1_K = ⊤`); dividing by `|K|` gives `[L:K]`. -/
theorem induce_trivialChar_normSq_eq_index (K : Subgroup L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] :
    ClassFunction.inner (ClassFunction.induce K (trivialClassFunction ↥K))
      (ClassFunction.induce K (trivialClassFunction ↥K)) = (K.index : ℂ) := by
  have : Fintype ↥K := Fintype.ofFinite _
  have hcoe : (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) = trivialClassFunction ↥K := rfl
  have htop : ClassFunction.inertia (trivialClassFunction ↥K) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [ClassFunction.mem_inertia]
    exact conjBy_trivialClassFunction g
  have hkey := card_mul_inner_self_induce_eq_card_inertia (G := L) (trivialIrreducibleCharacter ↥K)
  rw [hcoe, htop, Subgroup.card_top] at hkey
  have hcardK : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h2 : (Nat.card ↥K : ℂ) * (K.index : ℂ) = (Nat.card L : ℂ) := by
    rw [← Nat.cast_mul, mul_comm, K.index_mul_card]
  exact mul_left_cancel₀ hcardK (hkey.trans h2.symm)

/-- **A nonprincipal induced character is orthogonal to `1_L`** (Peterfalvi (7.8.a), the `(φ,1_L)=0`
step).  For `θ ∈ Irr K` with `θ ≠ 1_K`, `(Ind_K^L θ, 1_L)_L = 0`: by Frobenius reciprocity it is
`(θ, Res_K 1_L)_K = (θ, 1_K)_K`, which vanishes by orthonormality of distinct irreducibles.

This is the honest `(7.8.a)` ingredient that `(φ − d ζ, 1_L) = 0` (for the members `φ, ζ ∈ S`,
induced from nonprincipal characters) rests on; the rest of `(7.8.a)`'s `orth_one` additionally
needs the coherence facts `(φ−dζ)^τ = φ^ν − d ζ^ν` and `(ζ^ν, 1_G) = 0` about the extension `ν`. -/
theorem inner_induce_constOne_eq_zero (K : Subgroup L) [Finite ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    (θ : IrreducibleCharacter ↥K) (hθ : θ ≠ trivialIrreducibleCharacter ↥K) :
    ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
      (Hypothesis71.constOne L) = 0 := by
  have : Fintype ↥K := Fintype.ofFinite _
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    show ClassFunction.restrict K (Hypothesis71.constOne L)
        = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) from by
      ext h; rw [ClassFunction.restrict_apply]; rfl,
    irreducibleCharacter_inner_eq_ite, if_neg hθ]

/-- **The induced principal character has inner product `1` with `1_L`** (Peterfalvi (7.8.a)).
`⟨Ind_K^L 1_K, 1_L⟩ = ⟨1_K, 1_K⟩ = 1` by Frobenius reciprocity.  Supplies `⟨β, 1_G⟩ = ⟨Ind 1_K − ζ,
1_L⟩ = 1 − 0 = 1` in the `Gamma_orth_one` computation. -/
theorem inner_induce_trivialChar_constOne_eq_one (K : Subgroup L) [Finite ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] :
    ClassFunction.inner
        (ClassFunction.induce K (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ))
        (Hypothesis71.constOne L) = 1 := by
  have : Fintype ↥K := Fintype.ofFinite _
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    show ClassFunction.restrict K (Hypothesis71.constOne L)
        = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) from by
      ext h; rw [ClassFunction.restrict_apply]; rfl,
    irreducibleCharacter_inner_eq_ite, if_pos rfl]

/-- **An induced nonprincipal character differs from the induced principal** (the irreducible-vs-
permutation-character distinction).  `Ind_K^L θ ≠ Ind_K^L 1_K` for `θ ≠ 1_K`, since they have
different inner products with `1_L` (`0` vs `1`, by `inner_induce_constOne_eq_zero` /
`inner_induce_trivialChar_constOne_eq_one`).  This supplies the `χ_dist ≠ Ind 1_K` input to
`exists_placed_induced_family` from a distinguished `χ = Ind θ ∈ S` (`θ ≠ 1_K`). -/
theorem induce_ne_trivialChar_induce (K : Subgroup L) [Finite ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    (θ : IrreducibleCharacter ↥K) (hθ : θ ≠ trivialIrreducibleCharacter ↥K) :
    ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
      ≠ ClassFunction.induce K (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by
  have : Fintype ↥K := Fintype.ofFinite _
  intro h
  have h0 := inner_induce_constOne_eq_zero K θ hθ
  rw [h, inner_induce_trivialChar_constOne_eq_one] at h0
  exact one_ne_zero h0

/-- **The Dade image of a supported class function is orthogonal to `1_G` iff the source is to
`1_L`** (Peterfalvi (7.8.a), the `(2.7)`-for-`1_G` instance).  For `α ∈ CF(L,A)`,
`⟨α^τ, 1_G⟩_G = ⟨α, 1_L⟩_L`: by the adjoint formula `chiRho_adjoint` `⟨α^τ, 1_G⟩ = ⟨α, (1_G)^ρ⟩`,
and `(1_G)^ρ = 1` on `A` (`chiRho_constOne`) where `α` is supported (`inner_eq_of_eqOn_support`). -/
theorem inner_tau_supported_constOne {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L) :
    ClassFunction.inner (H71.τ α) (Hypothesis71.constOne G)
      = ClassFunction.inner (α : ClassFunction L ℂ) (Hypothesis71.constOne L) := by
  rw [H71.chiRho_adjoint]
  refine inner_eq_of_eqOn_support fun g hg => ?_
  have hgA : (g : G) ∈ A := by
    have h := (ClassFunction.mem_supportedSubmodule.mp α.2) (ClassFunction.mem_support.mpr hg)
    rwa [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at h
  rw [H71.chiRhoCF_apply, H71.chiRho_constOne, if_pos hgA, Hypothesis71.constOne_apply]

/-- **Peterfalvi (7.8.a), `S^ν ⊥ 1_G`, generic family form.**  Abstracted over an arbitrary family
`ζ : Fin (n+1) → CF(L)` (not necessarily induced), with the coherence agreement
`(ζ_i − d_i ζ_0)^τ = ζ_i^ν − d_i ζ_0^ν` (`hagree`), the distinguished image orthogonality
`⟨ζ_0^ν, 1_G⟩ = 0` (`hzeta0nu`), and the source-side fact `⟨ζ_i, 1_L⟩ = 0` for `i ≠ ind1H`
(`hzeta_orth_one`, true for nonprincipal induced characters), every `ζ_i^ν` (`i ≠ ind1H`) is
orthogonal to `1_G`.  This is the family-agnostic core; the `induce`-specific
`betaDecomp_orth_one` and the abstract-`Hypothesis78`-level constructor both instantiate it. -/
theorem betaDecomp_orth_one_gen {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) {n : ℕ} (ζ : Fin (n + 1) → ClassFunction ↥L ℂ) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩ = ν (ζ i) - d i • ν (ζ 0))
    (hzeta0nu : ClassFunction.inner (ν (ζ 0)) (Hypothesis71.constOne G) = 0)
    (hzeta_orth_one : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner (ζ i) (Hypothesis71.constOne L) = 0) :
    ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner (ν (ζ i)) (Hypothesis71.constOne G) = 0 := by
  intro i hi
  by_cases hi0 : i = 0
  · rw [hi0]; exact hzeta0nu
  · have hrearrange : ν (ζ i)
        = H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩ + d i • ν (ζ 0) := by
      rw [hagree i hi0 hi]; abel
    rw [hrearrange, ClassFunction.inner_add_left, ClassFunction.inner_smul_left, hzeta0nu,
      mul_zero, add_zero, inner_tau_supported_constOne]
    change ClassFunction.inner (ζ i - d i • ζ 0) (Hypothesis71.constOne L) = 0
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      hzeta_orth_one i hi, hzeta_orth_one 0 (Ne.symm hind1H), mul_zero, sub_zero]

/-- **The family-difference inner product, generic family form** (Peterfalvi (7.8.a)).  For an
arbitrary pairwise-orthogonal family `ζ` (`horth`), `⟨ζ_{ind1H} − ζ_0, ζ_i − d_i ζ_0⟩
= star(d_i) ‖ζ_0‖²` (`i ≠ 0, ind1H`, `ind1H ≠ 0`): all cross terms vanish, leaving the
`d_i ζ_0`-against-`ζ_0` term.  The `induce`-specific `inner_family_diff` instantiates `ζ = Ind θ`
with `horth := induce_family_orthogonal_of_injective`. -/
theorem inner_family_diff_gen [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ)
    (horth : ∀ i j : Fin (n + 1), i ≠ j → ClassFunction.inner (ζ i) (ζ j) = 0)
    (d : Fin (n + 1) → ℂ) {i ind1H : Fin (n + 1)}
    (hi0 : i ≠ 0) (hi_ind : i ≠ ind1H) (hind0 : ind1H ≠ 0) :
    ClassFunction.inner (ζ ind1H - ζ 0) (ζ i - d i • ζ 0)
      = star (d i) * ClassFunction.inner (ζ 0) (ζ 0) := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_right, ClassFunction.inner_smul_right,
    horth ind1H i (Ne.symm hi_ind), horth ind1H 0 hind0, horth 0 i (Ne.symm hi0)]
  ring

/-- **The inner product `⟨β, ζ_i^ν − d_i ζ_0^ν⟩`, generic family form** (Peterfalvi (7.8.a)).  For
an
arbitrary pairwise-orthogonal family `ζ` (`horth`), with `β = (ζ_{ind1H} − ζ_0)^τ` and the coherence
agreement `ζ_i^ν − d_i ζ_0^ν = (ζ_i − d_i ζ_0)^τ` (`hagree_i`), the Dade isometry turns the `G`-side
inner product into `⟨ζ_{ind1H} − ζ_0, ζ_i − d_i ζ_0⟩ = star(d_i) ‖ζ_0‖²` (`inner_family_diff_gen`).
Instantiated by the `induce`-specific `inner_beta_nuDiff` and the `Hypothesis78`-level
constructor. -/
theorem inner_beta_nuDiff_gen {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    {n : ℕ} (ζ : Fin (n + 1) → ClassFunction ↥L ℂ)
    (horth : ∀ i j : Fin (n + 1), i ≠ j → ClassFunction.inner (ζ i) (ζ j) = 0)
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (diffβ : (ζ ind1H - ζ 0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {i : Fin (n + 1)} (hi0 : i ≠ 0) (hi_ind : i ≠ ind1H)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hagree_i : ν (ζ i) - d i • ν (ζ 0) = H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩) :
    ClassFunction.inner (H71.τ ⟨ζ ind1H - ζ 0, diffβ⟩) (ν (ζ i) - d i • ν (ζ 0))
      = star (d i) * ClassFunction.inner (ζ 0) (ζ 0) := by
  rw [hagree_i, hτ.inner_eq]
  exact inner_family_diff_gen ζ horth d hi0 hi_ind hind0

/-- **The inner product `⟨weightedNuSum, ζ_j^ν⟩ = ζ_j(1)/ζ_0(1)`, generic family form**
(Peterfalvi (7.8.a)).  For an arbitrary pairwise-orthogonal family `ζ` (`horth`) with nonzero norms
(`hN`) and `ζ_0(1) ≠ 0` (`hz0`), the weighted sum `Σ_{i ≠ ind1H} (ζ_i(1)/(ζ_0(1)‖ζ_i‖²)) ζ_i^ν`
against `ζ_j^ν` (`j ≠ ind1H`) collapses by the `ν`-isometry to the single `i = j` term
`(ζ_j(1)/(ζ_0(1)‖ζ_j‖²)) ‖ζ_j‖² = ζ_j(1)/ζ_0(1)`.  Instantiated by the `induce`-specific
`inner_weightedNuSum_nu` and the `Hypothesis78`-level constructor. -/
theorem inner_weightedNuSum_nu_gen {G : Type*} [Group G] [Fintype G] {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} (ζ : Fin (n + 1) → ClassFunction ↥L ℂ)
    (horth : ∀ i j : Fin (n + 1), i ≠ j → ClassFunction.inner (ζ i) (ζ j) = 0)
    (hN : ∀ j : Fin (n + 1), ClassFunction.inner (ζ j) (ζ j) ≠ 0)
    (hz0 : ζ 0 (1 : ↥L) ≠ 0)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    {ind1H : Fin (n + 1)}
    (hnu : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ζ i)) (ν (ζ j)) = ClassFunction.inner (ζ i) (ζ j))
    {j : Fin (n + 1)} (hj : j ≠ ind1H) :
    ClassFunction.inner
      (∑ i ∈ Finset.univ.erase ind1H,
        (ζ i (1 : ↥L) / (ζ 0 (1 : ↥L) * ClassFunction.inner (ζ i) (ζ i)) : ℂ) • ν (ζ i))
      (ν (ζ j))
    = ζ j (1 : ↥L) / ζ 0 (1 : ↥L) := by
  rw [inner_sum_left, Finset.sum_eq_single_of_mem j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      (fun i hi_mem hij => by
        rw [ClassFunction.inner_smul_left, hnu i j (Finset.ne_of_mem_erase hi_mem) hj,
          horth i j hij, mul_zero]),
    ClassFunction.inner_smul_left, hnu j j hj hj]
  have hNj := hN j
  field_simp

/-- **The inner product `⟨β, ζ_j^ν⟩ = star(d_j) · a`, generic family form** (Peterfalvi (7.8.a)).
For an arbitrary pairwise-orthogonal family `ζ` (`horth`), with `a = ⟨β, ζ_0^ν⟩ + 1` and
`‖ζ_0‖² = 1`
(`hζ0norm`), `inner_beta_nuDiff_gen` rearranges to `⟨β, ζ_j^ν⟩ = star(d_j)(⟨β, ζ_0^ν⟩ + 1)`
(`j ≠ 0, ind1H`).  Instantiated by `inner_beta_nu_eq` and the `Hypothesis78`-level constructor. -/
theorem inner_beta_nu_eq_gen {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    {n : ℕ} (ζ : Fin (n + 1) → ClassFunction ↥L ℂ)
    (horth : ∀ i j : Fin (n + 1), i ≠ j → ClassFunction.inner (ζ i) (ζ j) = 0)
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (diffβ : (ζ ind1H - ζ 0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {j : Fin (n + 1)} (hj0 : j ≠ 0) (hj_ind : j ≠ ind1H)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hagree_j : ν (ζ j) - d j • ν (ζ 0) = H71.τ ⟨ζ j - d j • ζ 0, psi_support j⟩)
    (hζ0norm : ClassFunction.inner (ζ 0) (ζ 0) = 1) :
    ClassFunction.inner (H71.τ ⟨ζ ind1H - ζ 0, diffβ⟩) (ν (ζ j))
      = star (d j) * (ClassFunction.inner (H71.τ ⟨ζ ind1H - ζ 0, diffβ⟩) (ν (ζ 0)) + 1) := by
  have key := inner_beta_nuDiff_gen H71 hτ ζ horth d psi_support hind0 diffβ hj0 hj_ind ν hagree_j
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_smul_right, hζ0norm, mul_one] at key
  linear_combination key

/-- **Peterfalvi (7.8.a), `Γ ⊥ S^ν`, generic family form** (the `Gamma_orth_nu` field of
`BetaDecomp`).  For an arbitrary pairwise-orthogonal family `ζ` with nonzero norms (`hN`),
`ζ_0(1) ≠ 0` (`hz0`), and real degrees (`hP_real`), the residual `Γ = β − (1_G − ζ_0^ν + a · W)`
(`a = ⟨β, ζ_0^ν⟩ + 1`, `W = Σ_{i≠ind1H} (ζ_i(1)/(ζ_0(1)‖ζ_i‖²)) ζ_i^ν`) is orthogonal to every
`ζ_j^ν` (`j ≠ ind1H`): the building blocks are `inner_weightedNuSum_nu_gen`, `inner_beta_nu_eq_gen`,
`horth`, and `hP_real`.  Instantiated by the `induce`-specific `betaDecomp_gamma_orth_nu` and the
`Hypothesis78`-level constructor. -/
theorem betaDecomp_gamma_orth_nu_gen {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    {n : ℕ} (ζ : Fin (n + 1) → ClassFunction ↥L ℂ)
    (horth : ∀ i j : Fin (n + 1), i ≠ j → ClassFunction.inner (ζ i) (ζ j) = 0)
    (hN : ∀ j : Fin (n + 1), ClassFunction.inner (ζ j) (ζ j) ≠ 0)
    (hz0 : ζ 0 (1 : ↥L) ≠ 0) (hP_real : ∀ i, star (ζ i (1 : ↥L)) = ζ i (1 : ↥L))
    (d : Fin (n + 1) → ℂ) (hd : ∀ i, d i = ζ i (1 : ↥L) / ζ 0 (1 : ↥L))
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (diffβ : (ζ ind1H - ζ 0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ζ i)) (ν (ζ j)) = ClassFunction.inner (ζ i) (ζ j))
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      ν (ζ i) - d i • ν (ζ 0) = H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩)
    (horth1 : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner (ν (ζ i)) (Hypothesis71.constOne G) = 0)
    (hζ0norm : ClassFunction.inner (ζ 0) (ζ 0) = 1)
    (β : ClassFunction G ℂ) (hβ : β = H71.τ ⟨ζ ind1H - ζ 0, diffβ⟩)
    (a : ℂ) (ha : a = ClassFunction.inner β (ν (ζ 0)) + 1)
    (W : ClassFunction G ℂ)
    (hW : W = ∑ i ∈ Finset.univ.erase ind1H,
      (ζ i (1 : ↥L) / (ζ 0 (1 : ↥L) * ClassFunction.inner (ζ i) (ζ i)) : ℂ) • ν (ζ i))
    {j : Fin (n + 1)} (hj : j ≠ ind1H) :
    ClassFunction.inner (β - (Hypothesis71.constOne G - ν (ζ 0) + a • W)) (ν (ζ j)) = 0 := by
  have hc1 : ClassFunction.inner (Hypothesis71.constOne G) (ν (ζ j)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, horth1 j hj, star_zero]
  have hWj : ClassFunction.inner W (ν (ζ j)) = ζ j (1 : ↥L) / ζ 0 (1 : ↥L) := by
    rw [hW]; exact inner_weightedNuSum_nu_gen ζ horth hN hz0 ν hnu hj
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, hnu 0 j (Ne.symm hind0) hj, hc1, hWj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [hζ0norm, div_self hz0, ha]; ring
  · rw [horth 0 j (Ne.symm hj0), hβ,
      inner_beta_nu_eq_gen H71 hτ ζ horth d psi_support hind0 diffβ hj0 hj ν (hagree j hj0 hj)
        hζ0norm, ← hβ, ← ha]
    have hstar : star (d j) = ζ j (1 : ↥L) / ζ 0 (1 : ↥L) := by
      rw [hd j, star_div₀, hP_real j, hP_real 0]
    rw [hstar]; ring

/-- **Peterfalvi (7.8.a), `Γ ⊥ 1_G`, generic family form.**  Abstracted over an arbitrary family
`ζ` and taking the family-agnostic `⟨β, 1_G⟩ = 1` (`hβ1`).  For the residual
`Γ = β − (1_G − ζ_0^ν + a · W)`, `⟨Γ, 1_G⟩ = ⟨β,1_G⟩ − ⟨1_G,1_G⟩ + ⟨ζ_0^ν,1_G⟩ − ā⟨W,1_G⟩
= 1 − 1 + 0 − 0 = 0` (`⟨ζ_0^ν,1_G⟩ = 0` and `⟨W,1_G⟩ = 0` from `horth1`).  Instantiated by the
`induce`-specific `betaDecomp_gamma_orth_one` (which computes `⟨β,1_G⟩ = 1`) and the
`Hypothesis78`-level constructor. -/
theorem betaDecomp_gamma_orth_one_gen {G : Type*} [Group G] [Fintype G]
    {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} (ζ : Fin (n + 1) → ClassFunction ↥L ℂ)
    {ind1H : Fin (n + 1)} (hind0 : ind1H ≠ 0)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (horth1 : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner (ν (ζ i)) (Hypothesis71.constOne G) = 0)
    (β : ClassFunction G ℂ) (hβ1 : ClassFunction.inner β (Hypothesis71.constOne G) = 1)
    (a : ℂ) (W : ClassFunction G ℂ)
    (hW : W = ∑ i ∈ Finset.univ.erase ind1H,
      (ζ i (1 : ↥L) / (ζ 0 (1 : ↥L) * ClassFunction.inner (ζ i) (ζ i)) : ℂ) • ν (ζ i)) :
    ClassFunction.inner (β - (Hypothesis71.constOne G - ν (ζ 0) + a • W))
      (Hypothesis71.constOne G) = 0 := by
  have hW0 : ClassFunction.inner W (Hypothesis71.constOne G) = 0 := by
    rw [hW, inner_sum_left]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [ClassFunction.inner_smul_left, horth1 i (Finset.mem_erase.mp hi).1, mul_zero]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, hβ1, hW0, horth1 0 (Ne.symm hind0),
    Hypothesis71.constOne_inner_self_eq_one]
  ring

/-- **The (7.8.c) collapse of the (7.7.a) sum to a single term.**  If, in the `(7.7.a)`
decomposition `χ^ρ(x) = ∑_{i ≥ 1} (c̄_i/‖ζ_i‖²) ζ_i(x)`, all coefficients `c_i` (`i ≥ 1`) vanish
except at one index `i₁`, and the distinguished member satisfies `ζ_{i₁}(x) = ‖ζ_{i₁}‖²`
(the induced-principal-character identity, both `= e`), then the sum collapses to `star(c_{i₁})`.

This is the algebraic core of Peterfalvi (7.8.c): with `ζ_{i₁} = Ind_H^L 1_H` and
`c_{i₁} = (β,χ)`, `induce_trivialChar_apply_eq_index`/`_normSq_eq_index` give the hypothesis
`ζ_{i₁}(x) = ‖ζ_{i₁}‖²`, and `χ^ρ(x) = star(β,χ)`. -/
theorem sum_collapse_to_single [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (c : Fin (n + 1) → ℂ)
    {x : L} {i₁ : Fin (n + 1)} (hi₁ : (0 : Fin (n + 1)) < i₁)
    (hvanish : ∀ i ∈ Finset.Ioi (0 : Fin (n + 1)), i ≠ i₁ → c i = 0)
    (hcrux : ζ i₁ x = ClassFunction.inner (ζ i₁) (ζ i₁))
    (hnorm : ClassFunction.inner (ζ i₁) (ζ i₁) ≠ 0) :
    (∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (c i) / ClassFunction.inner (ζ i) (ζ i)) * ζ i x) = star (c i₁) := by
  rw [Finset.sum_eq_single_of_mem i₁ (Finset.mem_Ioi.mpr hi₁)
      (fun i hi hne => by rw [hvanish i hi hne]; simp), hcrux]
  exact div_mul_cancel₀ _ hnorm

/-- **The coherence vanishing of a (7.7.a) coefficient** (Peterfalvi (7.8.c)).  If `χ` is orthogonal
to both `a` and `b` in `CF(G)`, then `(a − d·b, χ) = 0`.  In (7.8.c), with `a = ζ_i^ν`, `b = ζ_0^ν`
(`ζ_i, ζ_0 ∈ S`) and the coherence agreement `(ζ_i − d_i ζ_0)^τ = ζ_i^ν − d_i ζ_0^ν`, the hypothesis
`χ ⊥ S^ν` makes the coefficient `c_i = ((ζ_i − d_i ζ_0)^τ, χ)` vanish for the non-distinguished
indices. -/
theorem inner_sub_smul_left_eq_zero {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {a b χ : ClassFunction G ℂ} {d : ℂ}
    (ha : ClassFunction.inner χ a = 0) (hb : ClassFunction.inner χ b = 0) :
    ClassFunction.inner (a - d • b) χ = 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    inner_conj_symm χ a, ha, star_zero, inner_conj_symm χ b, hb, star_zero, mul_zero, sub_zero]

end OddOrder.Peterfalvi.S09.Cert


