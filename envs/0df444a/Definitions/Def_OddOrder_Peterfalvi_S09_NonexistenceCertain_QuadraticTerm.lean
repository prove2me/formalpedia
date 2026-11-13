-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm
-- name    : OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:35:00.68267+00:00
-- url     : https://prove2.me/theorems/d90ad359-a366-442a-982c-fbdd994d933a
-- title:
--   Peterfalvi (7.8): the quadratic term of the coherence formula
-- statement:
--   Part of the Peterfalvi §7 coherence-formula development, concerning Hypothesis (7.8) and the quantities it uses.
--
--   Main definitions: `Hypothesis78` (Hypothesis (7.6) with the coherence input), `indMinusZetaSupp` ($\mathrm{Ind}\,1_H-\zeta$), `beta` ($\beta=(\mathrm{Ind}\,1_H-\zeta)^\tau$), `sourceSet` (the coherent source set), `delta` (the residual $\Delta=\beta-1_G+\zeta^\nu$ used in (7.9)), `betaNormSq` and `sourceDiffNormSq`.
--
--   The bundle also proves 21 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_NormalCase

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

/-- **Peterfalvi (7.8) Hypothesis.**  Hypothesis (7.6) together with the
coherence input for `S = T \ {Ind 1_H}` and a distinguished `ζ ∈ S` of degree
`e = [L:H] = (Ind 1_H)(1)`.

The (7.8.c) conclusion (the pointwise identity on `A`) is the field
`chiRho_eq_inner_beta`; `hypothesis78OfDade` discharges it from `(7.1)` plus coherence, so it is
a *conclusion carried in the record*, not an extra assumption. -/
structure Hypothesis78 (G : Type*) [Group G] [Fintype G]
    (A : Set G) (L : Subgroup G) [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The underlying Hypothesis (7.6). -/
  hyp76 : Hypothesis76 G A L
  /-- Index of the induced principal character `Ind 1_H` in `T = {ζ_0, ..., ζ_n}`. -/
  ind1H : Fin (hyp76.n + 1)
  /-- Index of the distinguished `ζ ∈ S = T \ {Ind 1_H}`. -/
  zetaDistinct : Fin (hyp76.n + 1)
  /-- `ζ ≠ Ind 1_H`, so the distinguished `ζ` lies in `S`. -/
  zetaDistinct_ne_ind1H : zetaDistinct ≠ ind1H
  /-- `ζ(1) = (Ind 1_H)(1)` (= `e = [L:H]`).  Makes the difference
  `Ind 1_H − ζ` vanish at `1`, hence supported on `A = H \ {1}`. -/
  zeta_one_eq_ind1H_one :
    hyp76.zeta zetaDistinct (1 : L) = hyp76.zeta ind1H (1 : L)
  /-- `Ind 1_H − ζ` is supported on `A`.  Carried so the supported-class-function
  `β` can be formed cleanly. -/
  diff_support : (hyp76.zeta ind1H - hyp76.zeta zetaDistinct).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  /-- The coherent isometric extension `ν : ℤ[S] → ℤ[Irr G]`, presented as an
  `ℤ`-linear map on the ambient class-function space. -/
  nu : ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ
  /-- `ν` is a *family* isometry: it preserves the Gram matrix of the coherent
  family `{ζ_i : i ≠ ind1H}`.  This is the genuine content of coherence (Dade);
  a *global* isometry `CF(L) → CF(G)` need not exist (it would be an isometric
  embedding, but `dim CF(L)` can exceed `dim CF(G)`). -/
  nu_isometry : ∀ i j : Fin (hyp76.n + 1), i ≠ ind1H → j ≠ ind1H →
    ClassFunction.inner (nu (hyp76.zeta i)) (nu (hyp76.zeta j)) =
      ClassFunction.inner (hyp76.zeta i) (hyp76.zeta j)
  /-- **Peterfalvi (7.8.c.i) certificate.**  For χ ∈ Irr G orthogonal to `S^ν`
  (i.e. `(χ, ν ζ_i)_G = 0` for every `i ≠ ind1H`), and `x ∈ A`,
  `χ^ρ(x) = star (β, χ)_G`, where `β = τ (Ind 1_H − ζ) ∈ CF(G)`.

  Encodes the coherence-based reduction of the (7.7.a) decomposition: under
  `χ ⊥ S^ν`, the inner products `(ψ_i^τ, χ) = (ν(ψ_i), χ)` collapse to a
  single contribution proportional to `β`. -/
  chiRho_eq_inner_beta : ∀ (χ : ClassFunction G ℂ),
    IsIrreducibleCharacter χ →
    (∀ i : Fin (hyp76.n + 1), i ≠ ind1H →
      ClassFunction.inner χ (nu (hyp76.zeta i)) = 0) →
    ∀ {x : L}, (x : G) ∈ A →
    hyp76.hyp71.chiRho χ x =
      star (ClassFunction.inner
        (hyp76.hyp71.τ
          ⟨hyp76.zeta ind1H - hyp76.zeta zetaDistinct, diff_support⟩) χ)

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- `Ind 1_H − ζ ∈ CF(L,A)`, the supported difference defining `β`. -/
noncomputable def indMinusZetaSupp (H78 : Hypothesis78 G A L) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
  ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct, H78.diff_support⟩

/-- **`β = (Ind 1_H − ζ)^τ ∈ CF(G)`.** -/
noncomputable def beta (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  H78.hyp76.hyp71.τ H78.indMinusZetaSupp

theorem beta_def (H78 : Hypothesis78 G A L) :
    H78.beta =
      H78.hyp76.hyp71.τ
        ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct,
          H78.diff_support⟩ :=
  rfl

/-- The Dade image defining `β` is a virtual character whenever the source
difference `Ind 1_H - ζ` is a virtual character on `L`. -/
theorem beta_mem_ZIrr_of_sourceDiff_mem_ZIrr (H78 : Hypothesis78 G A L)
    (hdiffZ :
      H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L) :
    H78.beta ∈ ZIrr G := by
  have hτ : H78.hyp76.hyp71.τ = H78.hyp76.hyp71.hyp.dadeMap (k := ℂ) :=
    OddOrder.Peterfalvi.S04.IsDadeMap.unique H78.hyp76.hyp71.isDadeMap
      (H78.hyp76.hyp71.hyp.isDadeMap_dadeMap (k := ℂ))
  have hvirt :=
    H78.hyp76.hyp71.hyp.fullDadeIsometryData.maps_virtualCharacter
      H78.indMinusZetaSupp hdiffZ
  rw [beta, hτ]
  rwa [show H78.hyp76.hyp71.hyp.fullDadeIsometryData.toDadeMap =
        H78.hyp76.hyp71.hyp.dadeMap (k := ℂ) from
      H78.hyp76.hyp71.hyp.dadeIsometryData_toDadeMap] at hvirt

/-- The coherent source set `S = T \ {Ind 1_H}` from Peterfalvi (7.8),
presented as a set of class functions on `L`. -/
def sourceSet (H78 : Hypothesis78 G A L) : Set (ClassFunction L ℂ) :=
  {φ | ∃ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H ∧ H78.hyp76.zeta i = φ}

/-- Each non-`Ind 1_H` source character belongs to the coherent source set `S`. -/
theorem zeta_mem_sourceSet (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H) :
    H78.hyp76.zeta i ∈ H78.sourceSet :=
  ⟨i, hi, rfl⟩

/-- If the abstract `ν` carried by `Hypothesis78` is identified with a concrete
S07 coherent extension, then `ν` sends the coherent lattice `ℤ[S]` into virtual
irreducible characters of `G`.

This is the S09-facing bridge to the real S07 coherence construction: it adds no
new field to `Hypothesis78`, but lets downstream (7.8)/(7.9) arguments use
`IsCoherent.extension_mem_ZIrr` whenever the concrete witness is available. -/
theorem nu_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {φ : ClassFunction L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) S) :
    H78.nu φ ∈ ZIrr G := by
  rw [hnu]
  exact hcoh.extension_mem_ZIrr φ hφ

/-- Generator form of `nu_mem_ZIrr_of_isCoherent`: a member of the coherent set
itself is automatically in its `ℤ`-span. -/
theorem nu_mem_ZIrr_of_isCoherent_of_mem (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ S) :
    H78.nu φ ∈ ZIrr G :=
  H78.nu_mem_ZIrr_of_isCoherent hcoh hnu (Submodule.subset_span hφ)

/-- If the concrete S07 coherent witness is built over the source set
`S = T \ {Ind 1_H}`, then every non-`Ind 1_H` indexed source character has
virtual-irreducible image under `ν`. -/
theorem nu_zeta_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H) :
    H78.nu (H78.hyp76.zeta i) ∈ ZIrr G :=
  H78.nu_mem_ZIrr_of_isCoherent_of_mem hcoh hnu (H78.zeta_mem_sourceSet hi)

/-- Distinguished-`ζ` specialization of `nu_zeta_mem_ZIrr_of_isCoherent`. -/
theorem nu_zetaDistinct_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension) :
    H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G :=
  H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu H78.zetaDistinct_ne_ind1H

/-- The residual `Δ = β - 1_G + ζ^ν` used in Peterfalvi (7.9). -/
noncomputable def delta (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  H78.beta - Hypothesis71.constOne G +
    H78.nu (H78.hyp76.zeta H78.zetaDistinct)

/-- The real norm square `‖β‖²` used in Peterfalvi (7.8.b). -/
noncomputable def betaNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner H78.beta H78.beta).re

/-- The source-side norm square `‖Ind 1_H - ζ‖²` corresponding to `β`. -/
noncomputable def sourceDiffNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner
    (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
    (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)).re

/-- The Dade-isometry step in Peterfalvi (7.8.b): the norm of `β` equals the
norm of the source difference `Ind 1_H - ζ`.  The remaining `‖β‖² = e + 1`
calculation is therefore a source-side character computation. -/
theorem beta_inner_self_eq_sourceDiff_inner_self (H78 : Hypothesis78 G A L) :
    ClassFunction.inner H78.beta H78.beta =
      ClassFunction.inner
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct) := by
  simpa [beta, indMinusZetaSupp] using
    H78.hyp76.isDadeIsometry.inner_eq H78.indMinusZetaSupp H78.indMinusZetaSupp

/-- Real-valued form of `beta_inner_self_eq_sourceDiff_inner_self`. -/
theorem betaNormSq_eq_sourceDiffNormSq (H78 : Hypothesis78 G A L) :
    H78.betaNormSq = H78.sourceDiffNormSq := by
  rw [betaNormSq, sourceDiffNormSq, H78.beta_inner_self_eq_sourceDiff_inner_self]

/-- Source-side expansion of `‖Ind 1_H - ζ‖²`.  This isolates the remaining
character-theoretic facts needed to turn the source norm into `e + 1`. -/
theorem sourceDiff_inner_self_expand (H78 : Hypothesis78 G A L) :
    ClassFunction.inner
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct) =
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
          (H78.hyp76.zeta H78.zetaDistinct) +
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.zetaDistinct) := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
  ring

/-- Real-valued source-side expansion corresponding to
`sourceDiff_inner_self_expand`. -/
theorem sourceDiffNormSq_expand (H78 : Hypothesis78 G A L) :
    H78.sourceDiffNormSq =
      (ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
          (H78.hyp76.zeta H78.zetaDistinct) +
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.zetaDistinct)).re := by
  rw [sourceDiffNormSq, H78.sourceDiff_inner_self_expand]

/-- The weighted `S^ν`-sum occurring in Peterfalvi (7.8.a):
`Σ_{φ ∈ S} φ(1)/(e ‖φ‖²) · φ^ν`, where `S = T \ {Ind 1_H}` and
`e = ζ(1)` for the distinguished `ζ`. -/
noncomputable def weightedNuSum (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  ∑ i ∈ (Finset.univ.erase H78.ind1H),
    (H78.hyp76.zeta i (1 : L) /
        (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))) •
      H78.nu (H78.hyp76.zeta i)

/-- **Peterfalvi (7.8.a), the conclusion.**  The coherent images `S^ν` are orthogonal to
`1_G`, and `β` has the displayed decomposition
`β = 1_G - ζ^ν + a · Σ_{φ∈S} φ(1)/(e‖φ‖²) φ^ν + Γ`, with `a ∈ ℤ`
and `Γ` orthogonal to `S^ν ∪ {1_G}`.

Carried as a standalone record rather than a field of `Hypothesis78`, so that it adds no
assumption to results that do not need it.  It is **proved**, not assumed:
`Cert.betaDecompOfFacts` builds it at abstract `Hypothesis78` level from the coherence/family
facts, and `Cert.betaDecompOfDade` discharges every one of those facts for the Dade-family
construction `hypothesis78OfDade`. -/
structure BetaDecomp (H78 : Hypothesis78 G A L) where
  /-- `S^ν ⊥ 1_G`. -/
  orth_one : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) (Hypothesis71.constOne G) = 0
  /-- The integer coefficient `a` in Peterfalvi (7.8.a). -/
  a : ℤ
  /-- The residual term `Γ`. -/
  Gamma : ClassFunction G ℂ
  /-- `Γ` is orthogonal to `S^ν`. -/
  Gamma_orth_nu : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner Gamma (H78.nu (H78.hyp76.zeta i)) = 0
  /-- `Γ` is orthogonal to `1_G`. -/
  Gamma_orth_one : ClassFunction.inner Gamma (Hypothesis71.constOne G) = 0
  /-- The displayed decomposition of `β`. -/
  beta_eq :
    H78.beta =
      Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta H78.zetaDistinct) +
        (a : ℂ) • H78.weightedNuSum + Gamma

/-- Kernel order `h = |H|` for Peterfalvi (7.8.b). -/
noncomputable def kernelOrder (H78 : Hypothesis78 G A L) : ℕ :=
  Nat.card H78.hyp76.H

/-- Complement index `e = |L:H|` for Peterfalvi (7.8.b), stored as
`|L| / |H|` using the ambient normal-subgroup data. -/
noncomputable def complementIndex (H78 : Hypothesis78 G A L) : ℕ :=
  Nat.card L / Nat.card H78.hyp76.H

/-- The kernel order `h` is positive. -/
theorem kernelOrder_pos (H78 : Hypothesis78 G A L) : 0 < H78.kernelOrder := by
  rw [kernelOrder]
  exact Nat.card_pos

/-- The complement index `e = |L:H|` is positive. -/
theorem complementIndex_pos (H78 : Hypothesis78 G A L) : 0 < H78.complementIndex := by
  rw [complementIndex]
  have hH_card : Nat.card ((H78.hyp76.H).subgroupOf L) = Nat.card H78.hyp76.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H78.hyp76.H_le_L).toEquiv
  have hdvd : Nat.card H78.hyp76.H ∣ Nat.card L := by
    rw [← hH_card]
    exact Subgroup.card_subgroup_dvd_card ((H78.hyp76.H).subgroupOf L)
  exact Nat.div_pos (Nat.le_of_dvd Nat.card_pos hdvd) Nat.card_pos

/-- Lagrange in the notation of (7.8.b): `h * e = |L|`. -/
theorem kernelOrder_mul_complementIndex_eq_card_L (H78 : Hypothesis78 G A L) :
    H78.kernelOrder * H78.complementIndex = Nat.card L := by
  rw [kernelOrder, complementIndex]
  have hH_card : Nat.card ((H78.hyp76.H).subgroupOf L) = Nat.card H78.hyp76.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H78.hyp76.H_le_L).toEquiv
  have hdvd : Nat.card H78.hyp76.H ∣ Nat.card L := by
    rw [← hH_card]
    exact Subgroup.card_subgroup_dvd_card ((H78.hyp76.H).subgroupOf L)
  exact Nat.mul_div_cancel' hdvd

/-- **Peterfalvi (7.8.b) source norm target.**  The remaining source-side
character computation for `‖β‖² = e + 1`, after the Dade-isometry bridge has
reduced the norm of `β` to `‖Ind 1_H - ζ‖²`.

This is standalone target data, not a field of `Hypothesis78`; completing it
requires evaluating the four source inner products isolated by
`sourceDiffNormSq_expand`. -/
structure SourceDiffNormEvaluation (H78 : Hypothesis78 G A L) : Prop where
  /-- `‖Ind 1_H - ζ‖² = e + 1`. -/
  sourceDiffNormSq_eq :
    H78.sourceDiffNormSq = (H78.complementIndex : ℝ) + 1

/-- Once the source-side norm computation is available, the beta norm identity
`‖β‖² = e + 1` follows from the Dade isometry. -/
theorem betaNormSq_eq_complementIndex_add_one (H78 : Hypothesis78 G A L)
    (hsrc : H78.SourceDiffNormEvaluation) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  rw [H78.betaNormSq_eq_sourceDiffNormSq, hsrc.sourceDiffNormSq_eq]

/-- The four source-side inner-product evaluations needed for
`‖Ind 1_H - ζ‖² = e + 1` imply `SourceDiffNormEvaluation`.

In the textbook proof these are the normal-subgroup character computations for
`Ind_H^L 1_H` and the chosen irreducible `ζ`: the induced principal character
has norm square `e`, it is orthogonal to `ζ` on both sides, and `ζ` has norm
one. -/
theorem sourceDiffNormEvaluation_of_inner_values (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.SourceDiffNormEvaluation where
  sourceDiffNormSq_eq := by
    rw [H78.sourceDiffNormSq_expand, hind_norm, hzeta_ind, hind_zeta, hzeta_norm]
    simp

/-- Any indexed source character has norm one once it is known to be irreducible. -/
theorem zeta_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)}
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1 := by
  simpa using
    (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨H78.hyp76.zeta i, hzeta_irr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter L)
      (⟨H78.hyp76.zeta i, hzeta_irr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter L))

/-- The chosen non-principal `ζ` has norm one once it is known to be irreducible. -/
theorem zetaDistinct_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
  H78.zeta_inner_self_eq_one_of_irreducible hzeta_irr

/-- Variant using Hermitian symmetry: one orthogonality direction determines the other. -/
theorem sourceDiffNormEvaluation_of_zeta_ind_orthogonal (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.SourceDiffNormEvaluation := by
  refine H78.sourceDiffNormEvaluation_of_inner_values hind_norm hzeta_ind ?_ hzeta_norm
  rw [Hypothesis71.ClassFunction.inner_symm, hzeta_ind, star_zero]

/-- Variant using one orthogonality direction and irreducibility of the chosen `ζ`. -/
theorem sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal
    hind_norm hzeta_ind
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

/-- The size hypothesis `e ≤ (h - 1) / 2`, written without division as
`2e + 1 ≤ h`. -/
noncomputable def smallIndex (H78 : Hypothesis78 G A L) : Prop :=
  2 * H78.complementIndex + 1 ≤ H78.kernelOrder

/-- Real-valued form of `smallIndex`, for the arithmetic in (7.8.b). -/
theorem smallIndex_real (H78 : Hypothesis78 G A L) (hsmall : H78.smallIndex) :
    2 * (H78.complementIndex : ℝ) + 1 ≤ (H78.kernelOrder : ℝ) := by
  rw [smallIndex] at hsmall
  exact_mod_cast hsmall

/-- The quadratic correction `u a² - 2 v a` in Peterfalvi (7.8.b), with
`u = (1/e)(1 - 1/h)` and `v = 1/h`. -/
noncomputable def normQuadraticCorrection (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : ℝ :=
  (1 / (H78.complementIndex : ℝ)) *
      (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
    2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ)

/-- The class function `(ζ^ν)^ρ` whose norm is estimated in Peterfalvi (7.8.b). -/
noncomputable def zetaNuRho (H78 : Hypothesis78 G A L) : ClassFunction L ℂ :=
  H78.hyp76.hyp71.chiRhoCF (H78.nu (H78.hyp76.zeta H78.zetaDistinct))

/-- The real norm square `‖(ζ^ν)^ρ‖²` from Peterfalvi (7.8.b). -/
noncomputable def zetaNuRhoNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re

/-- The real norm square `‖Γ‖²` from Peterfalvi (7.8.b). -/
noncomputable def gammaNormSq (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : ℝ :=
  (ClassFunction.inner hBD.Gamma hBD.Gamma).re

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09


