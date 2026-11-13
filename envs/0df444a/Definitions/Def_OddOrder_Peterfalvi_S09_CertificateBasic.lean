-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_CertificateBasic
-- name    : OddOrder_Peterfalvi_S09_CertificateBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:07:11.913972+00:00
-- url     : https://prove2.me/theorems/2e94dbe2-9bc7-4966-88a7-d53378a37b37
-- title:
--   Peterfalvi §9: certificate discharge, opening layer
-- statement:
--   The opening layer of the certificate-discharge development for Peterfalvi §7/§9, where the (7.7.a)/(7.8.c) certificates are derived from the coherence data.
--
--   Main definitions: `hypothesis78OfDade` (the construction of `Hypothesis78` from coherence data, Peterfalvi (7.8)) and `betaDecompOfFacts` (the (7.8.a) `BetaDecomp` constructor). Results include `induce_degree_sum_bot` and `family_degree_sum` (the (1.5.d) degree sums over distinct induced characters).
--
--   The bundle also proves 17 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_CertificateBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_CertificateBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_BetaDecompOrthogonality

namespace OddOrder.Peterfalvi.S09.Cert

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L]

/-- **Discharge of the (7.8.c.i) certificate for an induced family** (Peterfalvi (7.8.c)).  With the
distinguished `ζ = Ind_K^L θ_0` at index `0` (so the induced principal character `Ind_K^L 1_K` is at
some `ind1H ≠ 0`), `χ` orthogonal to `S^ν` (`hortho`), and the coherence agreement
`(ζ_i − d_i ζ_0)^τ = ζ_i^ν − d_i ζ_0^ν` for the non-distinguished, non-`ind1H` indices (`hagree`),
the `(7.7.a)` decomposition collapses to the single `ind1H` term: every other coefficient vanishes
(`inner_sub_smul_left_eq_zero`), and the surviving term simplifies via `ζ_{ind1H}(x) = ‖ζ_{ind1H}‖²`
(`induce_trivialChar_apply_eq_index`/`_normSq_eq_index`, both `= [L:K]`).  Hence
`χ^ρ(x) = star((ζ_{ind1H} − d_{ind1H} ζ_0)^τ, χ)`; with `d_{ind1H} = 1` this is `star(β,χ)`. -/
theorem chiRho_eq_inner_beta_induced {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (K : Subgroup ↥L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L)
        = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L))
    (hAconj : ∀ g h : ↥L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hAK_off : ∀ y : ↥L, y ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L → y ∈ K)
    (hA_one : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
    (hortho : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner χ (ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) = 0)
    {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x = star (ClassFunction.inner (H71.τ
      ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
          - d ind1H • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ),
        psi_support ind1H⟩) χ) := by
  classical
  have : Fintype ↥K := Fintype.ofFinite ↥K
  rw [chiRho_decomp_induced H71 K θ d psi_support hinj hcover hdeg hAconj hAK_off hA_one χ hx]
  have hxK : x ∈ K := hAK_off x (by rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hx)
  refine sum_collapse_to_single (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
    (fun i => ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ)
    (Fin.pos_iff_ne_zero.mpr hind1H) ?_ ?_ (induce_norm_ne_zero K (θ ind1H))
  · -- the non-`ind1H` coefficients vanish by coherence
    intro i hi hne
    show ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ = 0
    rw [hagree i (Finset.mem_Ioi.mp hi).ne' hne]
    exact inner_sub_smul_left_eq_zero (hortho i hne) (hortho 0 (Ne.symm hind1H))
  · -- the distinguished term: `ζ_{ind1H}(x) = ‖ζ_{ind1H}‖² = [L:K]`
    show ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ) x
      = ClassFunction.inner (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
          (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
    rw [hzeta_ind1H,
      show ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
        = trivialClassFunction ↥K from rfl,
      induce_trivialChar_apply_eq_index K hxK, induce_trivialChar_normSq_eq_index K]

/-- **Construction of `Hypothesis78` from coherence data** (Peterfalvi (7.8)).  Given the
`(7.1)`/`(7.6)` data (`H71`, `hτ`, `H ⊴ L`, `A = H^#`), an enumerating family `θ` of the distinct
induced characters with the **distinguished** member `ζ` at index `0` and the induced principal
`Ind 1_H` at `ind1H`, together with the **coherence inputs** of `(7.8)` — the coherent isometric
extension `ν` and the agreement `τ(ψ_i) = ν ζ_i − d_i ν ζ_0` on `S` — the entire `Hypothesis78`
structure is built, *including* the `(7.8.c.i)` certificate `chiRho_eq_inner_beta`, which is
discharged by `chiRho_eq_inner_beta_induced`.

The distinguished `ζ = ζ_0` has `ζ(1) = (Ind 1_H)(1)` (`hdeg_match`), forcing `d_{ind1H} = 1`, so
the
certificate's `β = τ(Ind 1_H − ζ)` matches the family-difference `τ(ζ_{ind1H} − ζ_0)`.  Together
with
`hypothesis76OfFamily` this realizes the issue-1013 goal: `Hypothesis78` (the §7 floor cited by
`(12.16)` / `(14.11)`) is constructible from `(7.1)` + coherence alone, with no certificate
assumed. -/
noncomputable def hypothesis78OfDade
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥(H.subgroupOf L))
    (hdeg_match : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
          (ν (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          - d i • ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) :
    Hypothesis78 G A L := by
  classical
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  -- `d_{ind1H} = 1` from the degree match `ζ_0(1) = ζ_{ind1H}(1)`.
  have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (θ 0)
  have hd1 : d ind1H = 1 := by
    have h := hdeg ind1H
    rw [← hdeg_match] at h
    have h2 : d ind1H * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = 1 * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) := by
      rw [one_mul, ← h]
    exact mul_right_cancel₀ hz0 h2
  -- `ζ_{ind1H} − ζ_0` is supported on `A` (difference of induced characters of equal degree).
  have hdiff : (ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
      - ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    have h := induce_diff_support (θ ind1H) (θ 0) 1 (by rw [one_mul, ← hdeg_match])
    rw [one_smul] at h
    refine h.trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_iff H hAH x).mpr
      ⟨hx.1, fun h1 => hx.2 (OneMemClass.coe_eq_one.mp h1)⟩
  refine
    { hyp76 := hypothesis76OfFamily H71 hτ H hHL hHnorm hAH θ hinj hcover
      ind1H := ind1H
      zetaDistinct := 0
      zetaDistinct_ne_ind1H := Ne.symm hind1H
      zeta_one_eq_ind1H_one := hdeg_match
      diff_support := hdiff
      nu := ν
      nu_isometry := hnu_isometry
      chiRho_eq_inner_beta := fun χ _ hortho {x} hx => by
        -- Reduce `hyp76.hyp71` to `H71` (`rfl`) so `chiRho_eq_inner_beta_induced` rewrites the LHS.
        rw [show (hypothesis76OfFamily H71 hτ H hHL hHnorm hAH θ hinj hcover).hyp71 = H71 from rfl,
          chiRho_eq_inner_beta_induced H71 (H.subgroupOf L) θ d psi_support hinj hcover hdeg
            (supportInSubgroup_sharp_conj_mem_iff H hAH hHnorm)
            (fun y => supportInSubgroup_sharp_subset_subgroupOf H hAH)
            (one_not_mem_supportInSubgroup_sharp H hAH) ind1H hind1H hzeta_ind1H ν χ hagree hortho
                hx]
        -- Bridge the `(7.7.a)` coefficient `d_{ind1H}` (`= 1`) to the bare difference
        -- `ζ_{ind1H} − ζ_0`.
        refine congrArg star (congrArg (ClassFunction.inner · χ) (congrArg H71.τ ?_))
        apply Subtype.ext
        change ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
            - d ind1H • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) = _
        rw [hd1, one_smul]
        rfl }

/-- **Integrality of the `(7.8.a)` coefficient `a`** (Peterfalvi (7.8.a)).  The weighted-sum
coefficient `a = (β, ζ_0^ν) + 1` is an integer: `β = τ(Ind 1_H − ζ)` is a virtual character (from
`(2.6.b)` Dade preservation, packaged in `beta_mem_ZIrr_of_sourceDiff_mem_ZIrr`, given the source
difference `Ind 1_H − ζ ∈ ℤ[Irr L]`), `ζ_0^ν = ν ζ ∈ ℤ[Irr G]` is the coherent image
(`nu_mem_ZIrr_of_isCoherent`), and `inner_mem_ZIrr_int` makes their inner product an integer.
Supplies the `a : ℤ` field of `BetaDecomp` together with the displayed value `(β, ζ_0^ν) + 1`. -/
theorem exists_betaDecomp_a {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L)
    (hdiffZ : H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L)
    (hζ0nuZ : H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G) :
    ∃ a : ℤ, (a : ℂ) = ClassFunction.inner H78.beta
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) + 1 := by
  obtain ⟨m, hm⟩ :=
    ClassFunction.inner_mem_ZIrr_int (H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr hdiffZ) hζ0nuZ
  exact ⟨m + 1, by push_cast; rw [hm]⟩

/-- **Peterfalvi (7.8.b) coefficient identification, generic index** (`case A`, `ζ_0 = ζ`).  For the
`(7.7.a)` coefficient `c_i = (ψ_i^τ, ζ_0^ν)` with `χ = ζ_0^ν` (the distinguished `ζ = ζ_0` at index
`0`), the coherence agreement `ψ_i^τ = ζ_i^ν − d_i ζ_0^ν` (for `i ≠ 0, ind1H`), the isometry of `ν`,
the family orthogonality `(ζ_i, ζ_0) = 0`, the normalization `‖ζ_0‖² = 1`, and `d_i` real, give
`c_i = −d_i`.  This is the off-distinguished coefficient feeding the (7.8.b) double sum. -/
theorem cCoeff_nu_zeta_zero_eq_neg_d {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    {ind1H : Fin (H76.n + 1)}
    (hagree : ∀ i : Fin (H76.n + 1), i ≠ 0 → i ≠ ind1H →
      H76.hyp71.τ (H76.psiSupp i) = ν (H76.zeta i) - H76.d i • ν (H76.zeta 0))
    (hiso : ∀ a b : Fin (H76.n + 1), a ≠ ind1H → b ≠ ind1H →
      ClassFunction.inner (ν (H76.zeta a)) (ν (H76.zeta b))
        = ClassFunction.inner (H76.zeta a) (H76.zeta b))
    (h0ind : (0 : Fin (H76.n + 1)) ≠ ind1H)
    (horth : ∀ i : Fin (H76.n + 1), i ≠ 0 →
      ClassFunction.inner (H76.zeta i) (H76.zeta 0) = 0)
    (hnorm : ClassFunction.inner (H76.zeta 0) (H76.zeta 0) = 1)
    (i : Fin (H76.n + 1)) (hi0 : i ≠ 0) (hind : i ≠ ind1H) :
    H76.cCoeff (ν (H76.zeta 0)) i = - H76.d i := by
  unfold Hypothesis76.cCoeff
  rw [hagree i hi0 hind, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    hiso i 0 hind h0ind, hiso 0 0 h0ind h0ind, horth i hi0, hnorm, mul_one, zero_sub]

/-- **Peterfalvi (7.8.b) coefficient identification, the `Ind 1_H` index.**  At `i = ind1H`, the
`(7.7.a)` coefficient `c_{ind1H} = (ψ_{ind1H}^τ, ζ_0^ν)` equals `(β, ζ_0^ν)`: with `d_{ind1H} = 1`
and `zetaDistinct = 0`, the supported difference `ψ_{ind1H} = ζ_{ind1H} − ζ_0` coincides (as a
member
of `CF(L,A)`) with `Ind 1_H − ζ`, whose Dade image is `β`.  This is the distinguished coefficient
feeding the (7.8.b) double sum; combined with `exists_betaDecomp_a` it gives `c_{ind1H} = a − 1`. -/
theorem cCoeff_nu_zeta_zero_ind1H_eq {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hzd : H78.zetaDistinct = 0) (hd1 : H78.hyp76.d H78.ind1H = 1) :
    H78.hyp76.cCoeff (ν (H78.hyp76.zeta 0)) H78.ind1H =
      ClassFunction.inner H78.beta (ν (H78.hyp76.zeta 0)) := by
  have hsupp : H78.hyp76.psiSupp H78.ind1H = H78.indMinusZetaSupp := by
    apply Subtype.ext
    simp only [Hypothesis76.psiSupp_coe, Hypothesis78.indMinusZetaSupp, hd1, one_smul, hzd]
  unfold Hypothesis76.cCoeff Hypothesis78.beta
  rw [hsupp]

/-- **Orthogonality collapse of the `(7.7.b)` double sum.**  When the induced family `ζ_i` is
pairwise orthogonal (`(ζ_i, ζ_j) = 0` for `i ≠ j`, true for the distinct induced characters by
Frobenius reciprocity), the `(7.7.b)` double sum splits into a diagonal part and a rank-one
correction:
`‖χ^ρ‖² = Σ_i c̄_i c_i/‖ζ_i‖² − (Σ_i c̄_i ζ_i(1)/‖ζ_i‖²)(Σ_j c_j \overline{ζ_j(1)}/‖ζ_j‖²)/|L|`.
This is the shape used by (7.8.b) (`χ = ζ_0^ν`) before substituting the coefficients. -/
theorem chiRho_norm_sq_collapse {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (χ : ClassFunction G ℂ)
    (horth : ∀ i j : Fin (H76.n + 1), i ≠ j →
      ClassFunction.inner (H76.zeta i) (H76.zeta j) = 0) :
    ClassFunction.inner (H76.hyp71.chiRhoCF χ) (H76.hyp71.chiRhoCF χ) =
      (∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        star (H76.cCoeff χ i) * H76.cCoeff χ i / H76.zetaNormSq i)
      - (∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          star (H76.cCoeff χ i) * H76.zeta i 1 / H76.zetaNormSq i)
        * (∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
            H76.cCoeff χ j * star (H76.zeta j 1) / H76.zetaNormSq j)
        / (Nat.card L : ℂ) := by
  rw [H76.chiRho_norm_sq_double_sum χ]
  have hsplit : ∀ i j : Fin (H76.n + 1),
      star (H76.cCoeff χ i) * H76.cCoeff χ j / (H76.zetaNormSq i * H76.zetaNormSq j) *
          (ClassFunction.inner (H76.zeta i) (H76.zeta j)
            - H76.zeta i 1 * star (H76.zeta j 1) / (Nat.card L : ℂ)) =
        star (H76.cCoeff χ i) * H76.cCoeff χ j / (H76.zetaNormSq i * H76.zetaNormSq j) *
            ClassFunction.inner (H76.zeta i) (H76.zeta j)
          - (star (H76.cCoeff χ i) * H76.zeta i 1 / H76.zetaNormSq i) *
            (H76.cCoeff χ j * star (H76.zeta j 1) / H76.zetaNormSq j) / (Nat.card L : ℂ) := by
    intro i j; ring
  simp only [hsplit, Finset.sum_sub_distrib]
  congr 1
  · -- diagonal collapse via orthogonality
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [horth i j (Ne.symm hji), mul_zero]) (fun hi' => absurd hi hi')]
    rw [show ClassFunction.inner (H76.zeta i) (H76.zeta i) = H76.zetaNormSq i from rfl]
    field_simp
  · -- rank-one factoring
    rw [Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]

/-- **Diagonal-sum split at `ind1H`** for the (7.8.b) collapse.  Splitting the `Ioi 0` diagonal sum
`Σ_i c̄_i c_i / N_i` at the distinguished index `ind1H`, where `c_{ind1H} = cval` and `c_i = −d_i`
for `i ≠ 0, ind1H`, gives `c̄val·cval/N_{ind1H} + Σ_{i ≠ ind1H} d̄_i d_i / N_i` (the sign cancels).
This isolates the `(a−1)²/e` term from the off-distinguished `d_i`-sum. -/
theorem sum_diag_split_ind1H {n : ℕ} (c N d : Fin (n + 1) → ℂ) (cval : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = cval)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i)) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * c i / N i =
      star cval * cval / N ind1H
        + ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, star (d i) * d i / N i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)), hc_ind1H]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
  rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, star_neg, neg_mul, mul_neg, neg_neg]

/-- **Arithmetic core of (7.8.b).**  With the collapsed norm `‖ζ^{νρ}‖² = t₁ − X²/(e·h)` where the
diagonal `t₁ = (a−1)²/e + G/e²` and the rank-one `X = (a−1) − G/e`, and the `(1.5.d)` degree-sum
value `G = e(h−1) − e²`, the norm equals the quadratic `u a² − 2 v a + w` of Peterfalvi (7.8.b),
with `u = (1/e)(1−1/h)`, `v = 1/h`, `w = 1 − e/h`.  Pure field identity (verified by `ring`). -/
theorem normEstimate_matching (a e h G : ℝ) (he : e ≠ 0) (hh : h ≠ 0)
    (hG : G = e * (h - 1) - e ^ 2) :
    ((a - 1) ^ 2 / e + G / e ^ 2) - ((a - 1) - G / e) ^ 2 / (e * h) =
      (1 / e) * (1 - 1 / h) * a ^ 2 - 2 * (1 / h) * a + (1 - e / h) := by
  subst hG
  field_simp
  ring

/-- **Diagonal sum evaluation for (7.8.b)** (`term₁`).  With `c_{ind1H} = a−1`, `c_i = −d_i`
(`i ≠ 0, ind1H`), `N_{ind1H} = e`, `d_i = P_i/e`, and `a` / the `d_i` real, the diagonal sum
`Σ_i c̄_i c_i / N_i` evaluates to `(a−1)²/e + (Σ_{i ≠ ind1H} P_i²/N_i)/e²`. -/
theorem term1_eval_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (d i) = d i)
    (hd : ∀ i, d i = P i / e) (hN_ind1H : N ind1H = e) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * c i / N i =
      (a - 1) ^ 2 / e
        + (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e ^ 2 := by
  rw [sum_diag_split_ind1H c N d (a - 1) hind hc_ind1H hc_rest, hN_ind1H, ha1_real, ← pow_two]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd_real i, ← pow_two, hd i, div_pow]
  ring

/-- **Rank-one sum evaluation for (7.8.b)** (`X`).  With the same data, the rank-one factor
`Σ_i c̄_i P_i / N_i` evaluates to `(a−1) − (Σ_{i ≠ ind1H} P_i²/N_i)/e` (the `Ind 1_H` term gives
`(a−1)·e/e = a−1`; the off-distinguished terms give `−d_i P_i/N_i = −P_i²/(e N_i)`). -/
theorem rank1_eval_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (d i) = d i)
    (hd : ∀ i, d i = P i / e) (hN_ind1H : N ind1H = e) (hP_ind1H : P ind1H = e) (he : e ≠ 0) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * P i / N i =
      (a - 1) - (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)),
    hc_ind1H, ha1_real, hP_ind1H, hN_ind1H, mul_div_assoc, div_self he, mul_one, sub_eq_add_neg]
  rw [show (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, star (c i) * P i / N i)
        = ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i * (-(1 / e)) from
      Finset.sum_congr rfl fun i hi => by
        obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
        rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, star_neg, hd_real i, hd i]; ring,
    ← Finset.sum_mul]
  ring

/-- **Rank-one sum evaluation, conjugate-weight form** (`Y`).  The collapse's second rank-one
factor `Σ_j c_j \overline{P_j} / N_j` (note: bare `c_j`, conjugated `P_j`) evaluates to the same
`(a−1) − (Σ_{i ≠ ind1H} P_i²/N_i)/e` as `rank1_eval_generic`, using that the degrees `P_i` are real
(`\overline{P_i} = P_i`).  Together with `rank1_eval_generic` this gives `X·Y = ((a−1) − G/e)²`. -/
theorem rank1_eval_Y_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (hP_real : ∀ i, star (P i) = P i) (hd : ∀ i, d i = P i / e)
    (hN_ind1H : N ind1H = e) (hP_ind1H : P ind1H = e) (he : e ≠ 0) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), c i * star (P i) / N i =
      (a - 1) - (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)),
    hc_ind1H, hP_real ind1H, hP_ind1H, hN_ind1H, mul_div_assoc, div_self he, mul_one,
    sub_eq_add_neg]
  rw [show (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, c i * star (P i) / N i)
        = ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i * (-(1 / e)) from
      Finset.sum_congr rfl fun i hi => by
        obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
        rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, hP_real i, hd i]; ring,
    ← Finset.sum_mul]
  ring

/-- **(7.8.b) ℂ-level norm identity.**  Assembling the collapse with the three sum evaluations,
the `ζ_0^ν` self-inner-product equals `(a−1)²/e + G/e² − ((a−1) − G/e)²/|L|` where
`G = Σ_{i ≠ ind1H} ζ_i(1)²/‖ζ_i‖²` is the off-distinguished degree-sum.  (The `.re` and the
`(1.5.d)` value `G = e(h−1)−e²` then yield the (7.8.b) lower bound via `normEstimate_matching`.) -/
theorem zetaNuRho_inner_eq_cexpr {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    {ind1H : Fin (H76.n + 1)} (a e : ℂ) (hind : ind1H ≠ 0)
    (horth : ∀ i j : Fin (H76.n + 1), i ≠ j →
      ClassFunction.inner (H76.zeta i) (H76.zeta j) = 0)
    (hc_ind1H : H76.cCoeff (ν (H76.zeta 0)) ind1H = a - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → H76.cCoeff (ν (H76.zeta 0)) i = -(H76.d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (H76.d i) = H76.d i)
    (hP_real : ∀ i, star (H76.zeta i 1) = H76.zeta i 1)
    (hd : ∀ i, H76.d i = H76.zeta i 1 / e)
    (hN_ind1H : H76.zetaNormSq ind1H = e) (hP_ind1H : H76.zeta ind1H 1 = e) (he : e ≠ 0) :
    ClassFunction.inner (H76.hyp71.chiRhoCF (ν (H76.zeta 0)))
        (H76.hyp71.chiRhoCF (ν (H76.zeta 0))) =
      (a - 1) ^ 2 / e
        + (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase ind1H,
            H76.zeta i 1 ^ 2 / H76.zetaNormSq i) / e ^ 2
        - ((a - 1) - (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase ind1H,
            H76.zeta i 1 ^ 2 / H76.zetaNormSq i) / e) ^ 2 / (Nat.card L : ℂ) := by
  rw [chiRho_norm_sq_collapse H76 (ν (H76.zeta 0)) horth,
    term1_eval_generic (H76.cCoeff (ν (H76.zeta 0))) H76.zetaNormSq (fun i => H76.zeta i 1) H76.d
      a e hind hc_ind1H hc_rest ha1_real hd_real hd hN_ind1H,
    rank1_eval_generic (H76.cCoeff (ν (H76.zeta 0))) H76.zetaNormSq (fun i => H76.zeta i 1) H76.d
      a e hind hc_ind1H hc_rest ha1_real hd_real hd hN_ind1H hP_ind1H he,
    rank1_eval_Y_generic (H76.cCoeff (ν (H76.zeta 0))) H76.zetaNormSq (fun i => H76.zeta i 1) H76.d
      a e hind hc_ind1H hc_rest hP_real hd hN_ind1H hP_ind1H he]
  ring

/-- **(7.8.b) real-part + matching.**  Taking the real part of the ℂ-level norm identity (all of
`a, e, G, |L| = e·h` being real casts) and applying `normEstimate_matching`, the `ζ_0^ν`-norm
equals Peterfalvi's quadratic
`(1/e)(1−1/h)a² − (2/h)a + (1−e/h) = normQuadraticCorrection + (1−e/h)`.
This bridges the ℂ-level `zetaNuRho_inner_eq_cexpr` to the ℝ-valued `NormEstimates` field. -/
theorem cexpr_re_eq_normQuad (a e h G : ℝ) (he : e ≠ 0) (hh : h ≠ 0)
    (hG : G = e * (h - 1) - e ^ 2) :
    (((a : ℂ) - 1) ^ 2 / (e : ℂ) + (G : ℂ) / (e : ℂ) ^ 2
        - (((a : ℂ) - 1) - (G : ℂ) / (e : ℂ)) ^ 2 / ((e : ℂ) * (h : ℂ))).re =
      (1 / e) * (1 - 1 / h) * a ^ 2 - 2 * (1 / h) * a + (1 - e / h) := by
  rw [show (((a : ℂ) - 1) ^ 2 / (e : ℂ) + (G : ℂ) / (e : ℂ) ^ 2
        - (((a : ℂ) - 1) - (G : ℂ) / (e : ℂ)) ^ 2 / ((e : ℂ) * (h : ℂ)))
      = (((a - 1) ^ 2 / e + G / e ^ 2 - ((a - 1) - G / e) ^ 2 / (e * h) : ℝ) : ℂ) from by
      push_cast; ring,
    Complex.ofReal_re, normEstimate_matching a e h G he hh hG]

/-- **(7.8.b) identification** (last mile).  Given the ℂ-level norm identity (`h_inner`, supplied by
`zetaNuRho_inner_eq_cexpr` with `a, e, G` as the real casts `hBD.a`, `complementIndex`, and the
`(1.5.d)` degree-sum value), the real norm `‖ζ_0^{νρ}‖²` equals
`normQuadraticCorrection + (1 − e/h)`.  Fed to `zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq`,
this yields the Peterfalvi (7.8.b) lower bound. -/
theorem zetaNuRhoNormSq_eq_normQuad {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (a_ℝ e_ℝ h_ℝ G_ℝ : ℝ) (he : e_ℝ ≠ 0) (hh : h_ℝ ≠ 0)
    (hG : G_ℝ = e_ℝ * (h_ℝ - 1) - e_ℝ ^ 2)
    (ha : a_ℝ = (hBD.a : ℝ)) (he' : e_ℝ = (H78.complementIndex : ℝ))
    (hh' : h_ℝ = (H78.kernelOrder : ℝ))
    (h_inner : ClassFunction.inner H78.zetaNuRho H78.zetaNuRho =
      ((a_ℝ : ℂ) - 1) ^ 2 / (e_ℝ : ℂ) + (G_ℝ : ℂ) / (e_ℝ : ℂ) ^ 2
        - (((a_ℝ : ℂ) - 1) - (G_ℝ : ℂ) / (e_ℝ : ℂ)) ^ 2 / ((e_ℝ : ℂ) * (h_ℝ : ℂ))) :
    H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD
        + (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)) := by
  unfold OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRhoNormSq
  rw [h_inner, cexpr_re_eq_normQuad a_ℝ e_ℝ h_ℝ G_ℝ he hh hG,
    OddOrder.Peterfalvi.S09.Hypothesis78.normQuadraticCorrection, ha, he', hh']

open scoped Classical in
/-- **(1.5.d) degree-sum over distinct induced characters** (`A = ⊥` specialization of the S08
orbit-count `sum_div_normSq_induce_kernelFilter_eq`).  Summing `χ(1)²/‖χ‖²` over the distinct
nontrivially-induced characters `Ind_K^L θ` (`θ ≠ 1`) gives `[L:K]·(|K| − 1)`.  With `K = H ◁ L`
this is `e·(h − 1)` of Peterfalvi (1.5.d). -/
theorem induce_degree_sum_bot {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        θ ≠ trivialIrreducibleCharacter ↥K)).image
        (fun θ => ClassFunction.induce K θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = (K.index : ℂ) * ((Nat.card ↥K : ℂ) - 1) := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  have hbot : (⊥ : Subgroup L).subgroupOf K = ⊥ := by
    ext x; simp
  have h := OddOrder.Peterfalvi.S08.sum_div_normSq_induce_kernelFilter_eq (G := L) (H := K) (A := ⊥)
  have hfilter : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
      (↑((⊥ : Subgroup L).subgroupOf K) : Set ↥K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) ∧
        θ ≠ trivialIrreducibleCharacter ↥K))
      = Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        θ ≠ trivialIrreducibleCharacter ↥K) := by
    refine Finset.filter_congr fun θ _ => ?_
    rw [and_iff_right_iff_imp]
    intro _
    rw [hbot, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  rw [hfilter] at h
  rw [h, hbot]
  congr 2
  exact_mod_cast Nat.card_congr QuotientGroup.quotientBot.toEquiv

open scoped Classical in
/-- **(1.5.d) family degree-sum** (reindexed to the distinct-induced enumeration).  For a
`DistinctInducedFamily` enumeration `θ` with `Ind 1_H` at `ind1H`, the family degree-sum over
`i ≠ ind1H` equals the `induce_degree_sum_bot` image sum `= [L:K]·(|K|−1)`.  The reindexing is
`Finset.sum_image` (injectivity `hinj`); the image equality uses `hcover` and the orbit fact
`Ind θ' = Ind 1_H ↔ θ' = 1` (via `⟨Ind θ', 1_L⟩ = 0` for `θ' ≠ 1` vs `⟨Ind 1_H, 1_L⟩ = 1`). -/
theorem family_degree_sum {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (ind1H : Fin (n + 1)) (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K) :
    ∑ i ∈ Finset.univ.erase ind1H,
        ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) 1 ^ 2 /
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) =
      (K.index : ℂ) * ((Nat.card ↥K : ℂ) - 1) := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  rw [← induce_degree_sum_bot K,
    ← Finset.sum_image (f := fun φ : ClassFunction L ℂ => φ 1 ^ 2 / ClassFunction.inner φ φ)
      (g := fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
      (fun i _ j _ h => hinj h)]
  congr 1
  ext φ
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter,
    true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨θ i, ?_, rfl⟩
    intro hc
    exact hi (hinj (show ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
      = ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ) by rw [hc, hzeta_ind1H]))
  · rintro ⟨φ', hφ', rfl⟩
    obtain ⟨j, hj⟩ := hcover φ'
    refine ⟨j, ?_, hj⟩
    intro hjeq
    have hone : ClassFunction.inner (ClassFunction.induce K (φ' : ClassFunction ↥K ℂ))
        (Hypothesis71.constOne L) = 1 := by
      rw [← hj, hjeq]
      change ClassFunction.inner (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
        (Hypothesis71.constOne L) = 1
      rw [hzeta_ind1H]; exact inner_induce_trivialChar_constOne_eq_one K
    rw [inner_induce_constOne_eq_zero K φ' hφ'] at hone
    exact one_ne_zero hone.symm

/-- **(1.5.d) off-distinguished degree-sum** (`G`).  Removing the distinguished `ζ_0` (index `0`,
with `ζ_0(1) = [L:K]` and `‖ζ_0‖² = 1`) from `family_degree_sum` gives the `(7.8.b)` quantity
`G = Σ_{i ∈ Ioi 0, i ≠ ind1H} ζ_i(1)²/‖ζ_i‖² = [L:K]·(|K|−1) − [L:K]²` (`= e(h−1) − e²`). -/
theorem family_degree_sum_Ioi {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (ind1H : Fin (n + 1)) (hind : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K)
    (hz0_deg : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) 1 = (K.index : ℂ))
    (hz0_norm : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) = 1) :
    ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H,
        ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) 1 ^ 2 /
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) =
      (K.index : ℂ) * ((Nat.card ↥K : ℂ) - 1) - (K.index : ℂ) ^ 2 := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  have hIoi : (Finset.Ioi (0 : Fin (n + 1))).erase ind1H
      = (Finset.univ.erase ind1H).erase 0 := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_Ioi, Finset.mem_univ, and_true, Fin.pos_iff_ne_zero]
    tauto
  have h0mem : (0 : Fin (n + 1)) ∈ Finset.univ.erase ind1H :=
    Finset.mem_erase.mpr ⟨Ne.symm hind, Finset.mem_univ _⟩
  rw [hIoi, Finset.sum_erase_eq_sub h0mem,
    family_degree_sum K θ hinj hcover ind1H hzeta_ind1H, hz0_deg, hz0_norm]
  ring

/-- **(7.8.b) ℂ-level norm identity at the `Hypothesis78` level** (the `h_inner` producer).  Lifts
`zetaNuRho_inner_eq_cexpr` (stated for `chiRhoCF (ν ζ_0)`) to
`H78.zetaNuRho = chiRhoCF (ν ζ_{zetaDistinct})` under the constructor convention `zetaDistinct = 0`,
then identifies the off-distinguished degree sum
`G = Σ_{i ∈ Ioi 0, i ≠ ind1H} ζ_i(1)²/‖ζ_i‖²` with `e·(h−1) − e²` (via `hGsum`, the `(1.5.d)`
`family_degree_sum_Ioi` value) and `|L| = e·h` (Lagrange
`kernelOrder_mul_complementIndex_eq_card_L`).
The conclusion is in the `(e_ℝ:ℂ)` real-cast shape consumed by `zetaNuRhoNormSq_eq_normQuad`. -/
theorem zetaNuRho_inner_eq_cexpr_H78 {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hc_ind1H : H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) H78.ind1H = (hBD.a : ℂ) - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) i = -(H78.hyp76.d i))
    (hd_real : ∀ i, star (H78.hyp76.d i) = H78.hyp76.d i)
    (hP_real : ∀ i, star (H78.hyp76.zeta i 1) = H78.hyp76.zeta i 1)
    (hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i 1 / (H78.complementIndex : ℂ))
    (hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ))
    (hP_ind1H : H78.hyp76.zeta H78.ind1H 1 = (H78.complementIndex : ℂ))
    (hGsum : ∑ i ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta i 1 ^ 2 / H78.hyp76.zetaNormSq i
      = (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) - (H78.complementIndex : ℂ) ^ 2) :
    ClassFunction.inner H78.zetaNuRho H78.zetaNuRho =
      (((hBD.a : ℝ) : ℂ) - 1) ^ 2 / ((H78.complementIndex : ℝ) : ℂ)
        + (((H78.complementIndex : ℝ) * ((H78.kernelOrder : ℝ) - 1)
              - (H78.complementIndex : ℝ) ^ 2 : ℝ) : ℂ) / ((H78.complementIndex : ℝ) : ℂ) ^ 2
        - ((((hBD.a : ℝ) : ℂ) - 1)
            - (((H78.complementIndex : ℝ) * ((H78.kernelOrder : ℝ) - 1)
                  - (H78.complementIndex : ℝ) ^ 2 : ℝ) : ℂ) / ((H78.complementIndex : ℝ) : ℂ)) ^ 2
          / (((H78.complementIndex : ℝ) : ℂ) * ((H78.kernelOrder : ℝ) : ℂ)) := by
  have he_ne : (H78.complementIndex : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr H78.complementIndex_pos.ne'
  have hind : H78.ind1H ≠ 0 := fun h => H78.zetaDistinct_ne_ind1H (hzd.trans h.symm)
  have ha1_real : star ((hBD.a : ℂ) - 1) = (hBD.a : ℂ) - 1 := by simp
  have hLcard : (Nat.card L : ℂ) = (H78.complementIndex : ℂ) * (H78.kernelOrder : ℂ) := by
    rw [mul_comm]; exact_mod_cast H78.kernelOrder_mul_complementIndex_eq_card_L.symm
  simp only [OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho, hzd]
  rw [zetaNuRho_inner_eq_cexpr H78.hyp76 H78.nu (hBD.a : ℂ) (H78.complementIndex : ℂ) hind horth
      hc_ind1H hc_rest ha1_real hd_real hP_real hd hN_ind1H hP_ind1H he_ne,
    hGsum, hLcard]
  push_cast
  ring

/-- **Peterfalvi (7.8.b), the `ζ`-norm lower bound** (`Hypothesis78` level).  Assembles the full
chain: the `h_inner` identity `zetaNuRho_inner_eq_cexpr_H78`, the real-part identification
`zetaNuRhoNormSq_eq_normQuad` (`‖ζ_0^{νρ}‖² = normQuadraticCorrection + (1 − e/h)`), and the
nonnegativity reduction `zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq` (valid under
`2e + 1 ≤ h`).  The result `1 − e/h ≤ ‖ζ_0^{νρ}‖²` is exactly the (7.8.b)
`NormEstimates.zetaNuRho_norm_sq_ge` target, discharged from the abstract
`(7.8.a)`-decomposition / coherence / degree facts. -/
theorem zetaNuRhoNormSq_eq_normQuad_of_facts {G : Type*} [Group G] [Fintype G] {A : Set G}
    {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hc_ind1H : H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) H78.ind1H = (hBD.a : ℂ) - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) i = -(H78.hyp76.d i))
    (hd_real : ∀ i, star (H78.hyp76.d i) = H78.hyp76.d i)
    (hP_real : ∀ i, star (H78.hyp76.zeta i 1) = H78.hyp76.zeta i 1)
    (hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i 1 / (H78.complementIndex : ℂ))
    (hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ))
    (hP_ind1H : H78.hyp76.zeta H78.ind1H 1 = (H78.complementIndex : ℂ))
    (hGsum : ∑ i ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta i 1 ^ 2 / H78.hyp76.zetaNormSq i
      = (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) - (H78.complementIndex : ℂ) ^ 2) :
    H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD
        + (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)) :=
  zetaNuRhoNormSq_eq_normQuad H78 hBD (hBD.a : ℝ) (H78.complementIndex : ℝ) (H78.kernelOrder : ℝ)
    ((H78.complementIndex : ℝ) * ((H78.kernelOrder : ℝ) - 1) - (H78.complementIndex : ℝ) ^ 2)
    (Nat.cast_ne_zero.mpr H78.complementIndex_pos.ne')
    (Nat.cast_ne_zero.mpr H78.kernelOrder_pos.ne') rfl rfl rfl rfl
    (zetaNuRho_inner_eq_cexpr_H78 H78 hBD hzd horth hc_ind1H hc_rest hd_real hP_real hd
      hN_ind1H hP_ind1H hGsum)

/-- **Peterfalvi (7.8.b), the `ζ`-norm lower bound** (`Hypothesis78` level).  The direct `≤` form of
the (7.8.b) target `NormEstimates.zetaNuRho_norm_sq_ge`: from the
`zetaNuRhoNormSq_eq_normQuad_of_facts`
identity and the `smallIndex` (`2e + 1 ≤ h`) nonnegativity reduction
`zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq`, the coherent `ζ`-image satisfies
`1 − e/h ≤ ‖ζ_0^{νρ}‖²`.

To obtain the *full* (7.8.b) `NormEstimates` (both the `ζ` bound and the `Γ` bound `‖Γ‖² ≤ e − 1`),
feed `zetaNuRhoNormSq_eq_normQuad_of_facts` as the `hzeta` argument of the already-assembled
source-side
`OddOrder.Peterfalvi.S09.Hypothesis78.normEstimates_of_source_orthogonal`. -/
theorem zetaNuRhoNormSq_ge_of_facts {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hc_ind1H : H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) H78.ind1H = (hBD.a : ℂ) - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) i = -(H78.hyp76.d i))
    (hd_real : ∀ i, star (H78.hyp76.d i) = H78.hyp76.d i)
    (hP_real : ∀ i, star (H78.hyp76.zeta i 1) = H78.hyp76.zeta i 1)
    (hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i 1 / (H78.complementIndex : ℂ))
    (hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ))
    (hP_ind1H : H78.hyp76.zeta H78.ind1H 1 = (H78.complementIndex : ℂ))
    (hGsum : ∑ i ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta i 1 ^ 2 / H78.hyp76.zetaNormSq i
      = (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) - (H78.complementIndex : ℂ) ^ 2)
    (hsmall : H78.smallIndex) :
    1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤ H78.zetaNuRhoNormSq :=
  H78.zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq hBD
    (zetaNuRhoNormSq_eq_normQuad_of_facts H78 hBD hzd horth hc_ind1H hc_rest hd_real hP_real hd
      hN_ind1H hP_ind1H hGsum) hsmall

/-- **Peterfalvi (7.8.a), the `BetaDecomp` constructor** (`Hypothesis78` level).  Assembles the full
`(7.8.a)` decomposition `β = 1_G − ζ_0^ν + a · W + Γ` (with `Γ` the explicit residual) for an
abstract `H78` from the `(7.8.a)` coherence / family facts, discharging all four `BetaDecomp` proof
fields via the family-agnostic gen lemmas (`betaDecomp_orth_one_gen`,
`betaDecomp_gamma_orth_nu_gen`,
`betaDecomp_gamma_orth_one_gen`).  Because `H78` is abstract here (not a `hypothesis78OfDade`
application), the field projections `H78.hyp76.zeta` / `H78.beta` / `H78.weightedNuSum` do not trip
the whnf-wall.  The hypotheses (family orthogonality, coherence agreement `hagree`, source
orthogonalities, `⟨β,1_G⟩ = 1`, `‖ζ_0‖² = 1`, the integer `a`) are all constructible from the Dade
family; `a` is `exists_betaDecomp_a`. -/
noncomputable def betaDecompOfFacts {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hN : ∀ j : Fin (H78.hyp76.n + 1),
      ClassFunction.inner (H78.hyp76.zeta j) (H78.hyp76.zeta j) ≠ 0)
    (hz0 : H78.hyp76.zeta 0 (1 : ↥L) ≠ 0)
    (hP_real : ∀ i, star (H78.hyp76.zeta i (1 : ↥L)) = H78.hyp76.zeta i (1 : ↥L))
    (hagree : ∀ i : Fin (H78.hyp76.n + 1), i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.hyp71.τ ⟨H78.hyp76.zeta i - H78.hyp76.d i • H78.hyp76.zeta 0,
          H78.hyp76.psi_support i⟩
        = H78.nu (H78.hyp76.zeta i) - H78.hyp76.d i • H78.nu (H78.hyp76.zeta 0))
    (hzeta0nu : ClassFunction.inner (H78.nu (H78.hyp76.zeta 0)) (Hypothesis71.constOne G) = 0)
    (hzeta_orth_one : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.hyp76.zeta i) (Hypothesis71.constOne L) = 0)
    (hβ1 : ClassFunction.inner H78.beta (Hypothesis71.constOne G) = 1)
    (hζ0norm : ClassFunction.inner (H78.hyp76.zeta 0) (H78.hyp76.zeta 0) = 1)
    (a : ℤ) (ha : (a : ℂ) = ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta 0)) + 1) :
    H78.BetaDecomp := by
  have hind0 : H78.ind1H ≠ 0 := fun h => H78.zetaDistinct_ne_ind1H (hzd.trans h.symm)
  have hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i (1 : ↥L) / H78.hyp76.zeta 0 (1 : ↥L) :=
    fun i => by rw [eq_div_iff hz0]; exact (H78.hyp76.zeta_one_eq_d_mul i).symm
  have diffβ : (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    have h := H78.diff_support; rw [hzd] at h; exact h
  have hβ : H78.beta
      = H78.hyp76.hyp71.τ ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta 0, diffβ⟩ := by
    rw [H78.beta_def]; congr 1; apply Subtype.ext
    change H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct
      = H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta 0
    rw [hzd]
  have hW : H78.weightedNuSum = ∑ i ∈ Finset.univ.erase H78.ind1H,
      (H78.hyp76.zeta i (1 : ↥L) /
        (H78.hyp76.zeta 0 (1 : ↥L) * ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
        : ℂ) • H78.nu (H78.hyp76.zeta i) := by
    unfold OddOrder.Peterfalvi.S09.Hypothesis78.weightedNuSum; rw [hzd]
  have horth1 : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) (Hypothesis71.constOne G) = 0 :=
    betaDecomp_orth_one_gen H78.hyp76.hyp71 H78.hyp76.zeta H78.hyp76.d H78.hyp76.psi_support
      H78.ind1H hind0 H78.nu hagree hzeta0nu hzeta_orth_one
  exact
    { orth_one := horth1
      a := a
      Gamma := H78.beta - (Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta 0)
        + (a : ℂ) • H78.weightedNuSum)
      Gamma_orth_nu := fun i hi =>
        betaDecomp_gamma_orth_nu_gen H78.hyp76.hyp71 H78.hyp76.isDadeIsometry H78.hyp76.zeta
          horth hN hz0 hP_real H78.hyp76.d hd H78.hyp76.psi_support hind0 diffβ H78.nu
          H78.nu_isometry (fun i hi0 hii => (hagree i hi0 hii).symm) horth1 hζ0norm H78.beta hβ
          (a : ℂ) ha H78.weightedNuSum hW hi
      Gamma_orth_one :=
        betaDecomp_gamma_orth_one_gen H78.hyp76.zeta hind0 H78.nu horth1 H78.beta hβ1
          (a : ℂ) H78.weightedNuSum hW
      beta_eq := by rw [hzd]; abel }

end OddOrder.Peterfalvi.S09.Cert


