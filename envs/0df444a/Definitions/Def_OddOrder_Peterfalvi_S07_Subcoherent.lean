-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_Subcoherent
-- name    : OddOrder_Peterfalvi_S07_Subcoherent
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:12:04.894193+00:00
-- url     : https://prove2.me/theorems/26574202-ba31-4e0b-a5eb-93f77a61faf1
-- title:
--   Peterfalvi (5.3)(a): the subcoherent $R$-datum producer
-- statement:
--   Formalizes the subcoherence structure of Peterfalvi (5.2) and its producer in (5.3)(a) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §5, pp. 21-24), together with the weight $\mathrm{Snorm}$ of (9.11).
--
--   Main declarations: `irrSubcoherent` (Peterfalvi (5.3)(a), assembler form (`irr_subcoherent`)); `Hypothesis.restrict` (Peterfalvi (5.3)(a) restriction (`subset_subcoherent`)); `Snorm` (Peterfalvi (9.11): the degree-square-over-norm weight `Snorm ψ = ψ(1)²/'[ψ]` (real form)); `sumnS` (Peterfalvi (9.11): the summed degree-square-over-norm `sumnS Si = ∑_{ψ ∈ Si} Snorm ψ`).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_Subcoherent.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Subcoherent.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade
import Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceConstantDegree

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Source-side (5.2.e) orthogonality of conjugate differences.**

If `⟨χ, ψ⟩ = 0` and `⟨χ, ψ̄⟩ = 0`, then the conjugate differences are orthogonal:
`⟨χ − χ̄, ψ − ψ̄⟩ = 0`.

Expanding `⟨χ−χ̄, ψ−ψ̄⟩ = ⟨χ,ψ⟩ − ⟨χ,ψ̄⟩ − ⟨χ̄,ψ⟩ + ⟨χ̄,ψ̄⟩`.  The two remaining
cross terms are the conjugates of the given zeros
(`OddOrder.RepresentationTheory.inner_conj_conj`, `⟨φ̄, ψ̄⟩ = conj⟨φ, ψ⟩`):
`⟨χ̄, ψ̄⟩ = conj⟨χ, ψ⟩ = 0`, and `⟨χ̄, ψ⟩ = ⟨χ̄, (ψ̄)̄⟩ = conj⟨χ, ψ̄⟩ = 0`. -/
theorem inner_conjugateDifference_eq_zero
    {χ ψ : ClassFunction L ℂ}
    (hχψ : ClassFunction.inner χ ψ = 0)
    (hχψbar : ClassFunction.inner χ ψ.conj = 0) :
    ClassFunction.inner (χ - χ.conj) (ψ - ψ.conj) = 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hχψ, hχψbar]
  -- Remaining: `- (0 - 0) - (⟨χ̄, ψ⟩ - ⟨χ̄, ψ̄⟩) = 0`, i.e. `⟨χ̄,ψ⟩ = ⟨χ̄,ψ̄⟩ = 0`.
  have hbar1 : ClassFunction.inner χ.conj ψ = 0 := by
    have h := inner_conj_conj χ ψ.conj
    rw [ClassFunction.conj_conj, hχψbar, star_zero] at h
    exact h
  have hbar2 : ClassFunction.inner χ.conj ψ.conj = 0 := by
    have h := inner_conj_conj χ ψ
    rw [hχψ, star_zero] at h
    exact h
  rw [hbar1, hbar2]; ring

variable {S : Set (ClassFunction L ℂ)} {A : Set L}

/-- **Peterfalvi (5.3)(a), assembler form (`irr_subcoherent`).**

Given
* `τ` a base integral character map,
* a family `S` that is conjugate-closed (`hconj`), has no real members (`hreal`),
  and is pairwise orthogonal (`hortho`),
* `A`-supportedness of the conjugate differences `χ − χ̄` (`hconjsupp` — Coq's
  `'Z[S, L^#]` membership of the (5.2.d) differences),
* `τ` a lattice-relative isometry on `ℤ[S, A]` (`hiso`, the (0099) `zSupportedSpan`
  form of Coq's `{in 'Z[S, L^#], isometry tau}`), and
* per-member difference images `Rdatum χ : CharacterDifferenceImage τ χ` whose
  underlying map is `τ` and whose image obeys `τ(χ − χ̄) = ε·(μ − ν)`,

this constructs the subcoherent `S07.Hypothesis` record on `S` with base `τ`.
This is the top-level producer that every §7/§14 consumer hand-assembled before.

Field (e) `difference_images_orthogonal` is derived: from `⟨φ, χ⟩ = 0` and
`⟨φ, χ̄⟩ = 0`, `inner_conjugateDifference_eq_zero` gives `⟨φ − φ̄, χ − χ̄⟩ = 0`;
the lattice isometry `hiso` (fed the `ℤ[S, A]`-membership of the conjugate
differences, via `hconjsupp`) transports this to `⟨(φ−φ̄)^τ, (χ−χ̄)^τ⟩ = 0`, i.e.
`⟨signedDiff φ, signedDiff χ⟩ = 0` (via `image_eq`), feeding
`orthogonal_of_signedDifference_inner_eq_zero`. -/
noncomputable def irrSubcoherent (τ : IntegralCharacterMap L G) (A : Set L)
    (Rdatum : ∀ χ ∈ S, CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hortho : OddOrder.Peterfalvi.S03.PairwiseOrthogonal S)
    (hconjsupp : ∀ χ ∈ S, ((χ - χ.conj : ClassFunction L ℂ)).support ⊆ A)
    (hiso : ∀ ⦃φ ψ : ClassFunction L ℂ⦄, φ ∈ zSupportedSpan (L := L) S A →
      ψ ∈ zSupportedSpan (L := L) S A →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ) :
    Hypothesis (L := L) (G := G) S A where
  tau := τ
  tau_isometry_diff := hiso
  conjugate_closed := hconj
  no_real_characters := hreal
  pairwise_orthogonal := hortho
  difference_image := fun χ hχ => Rdatum χ hχ
  difference_images_orthogonal := fun {φ χ} hφ hχ h1 h2 => by
    -- (5.2.e): reduce to `⟨signedDiff φ, signedDiff χ⟩ = 0`.
    refine (Rdatum φ hφ).orthogonal_of_signedDifference_inner_eq_zero (Rdatum χ hχ) ?_
    -- Rewrite both signed differences as `τ` applied to the conjugate differences.
    rw [← (Rdatum φ hφ).image_eq_signedDifference, ← (Rdatum χ hχ).image_eq_signedDifference]
    -- Conjugate differences lie in `ℤ[S, A]` (members + `hconjsupp`).
    have hmem : ∀ ⦃ψ : ClassFunction L ℂ⦄, ψ ∈ S →
        ψ - ψ.conj ∈ zSupportedSpan (L := L) S A := fun ψ hψ =>
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψ) (Submodule.subset_span (hconj hψ)),
        hconjsupp _ hψ⟩
    -- Isometry: `⟨τ(φ−φ̄), τ(χ−χ̄)⟩ = ⟨φ−φ̄, χ−χ̄⟩`, then source orthogonality.
    rw [hiso (hmem hφ) (hmem hχ)]
    exact inner_conjugateDifference_eq_zero h1 h2

/-- **Peterfalvi (5.3)(a) restriction (`subset_subcoherent`).**

Restrict a subcoherent `S07.Hypothesis` on `S` to a subset `S' ⊆ S` that is itself conjugate-closed.
All fields restrict directly along the inclusion `hsub`; the base map `τ`, the difference isometry,
the no-real / pairwise-orthogonal predicates, the per-member `R`-datum, and the cross-orthogonality
all hold a fortiori on the smaller family.  Conjugate-closedness of `S'` (`hconj'`) is supplied
separately, matching Coq's `cfConjC_subset S' S` premise. -/
noncomputable def Hypothesis.restrict (hyp : Hypothesis (L := L) (G := G) S A)
    {S' : Set (ClassFunction L ℂ)} (hsub : S' ⊆ S)
    (hconj' : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S') :
    Hypothesis (L := L) (G := G) S' A where
  tau := hyp.tau
  tau_isometry_diff := fun {_φ _ψ} hφ hψ =>
    hyp.tau_isometry_diff (zSupportedSpan_mono_left hsub hφ) (zSupportedSpan_mono_left hsub hψ)
  conjugate_closed := hconj'
  no_real_characters := fun {_χ} hχ => hyp.no_real_characters (hsub hχ)
  pairwise_orthogonal := fun {_χ _ψ} hχ hψ hne => hyp.pairwise_orthogonal (hsub hχ) (hsub hψ) hne
  difference_image := fun {_χ} hχ => hyp.difference_image (hsub hχ)
  difference_images_orthogonal := fun {_φ _χ} hφ hχ h1 h2 =>
    hyp.difference_images_orthogonal (hsub hφ) (hsub hχ) h1 h2

/-- **Peterfalvi (5.7)∘(5.3)(a): coherence of a uniform-degree conjugate-closed subfamily.**

Given a subcoherent `S07.Hypothesis` on `S` and a *uniform-degree* conjugate-closed subset
`S' ⊆ S` (finite, `≥ 2` members, all irreducible with equal, nonzero degree, whose member
differences the base map `τ` sends into `ℤ[Irr G]` and which are `A`-supported), the subfamily
`(S', A, τ)` is coherent.

This factors the `uniform_degree_coherence (subset_subcoherent …)` idiom of the (9.11) proof: it
`subset_subcoherent`-restricts to `S'`, then applies `coherent_of_constant_degree`.  It is the base
case of the (9.11) derived-series induction and the whole Galois case; it is *not* the full (9.11)
coherence for a mixed-degree family (which needs the (9.11.1)-(9.11.8) pair-adjoining induction on
top of this base). -/
theorem coherent_subset_of_constant_degree
    (hyp : Hypothesis (L := L) (G := G) S A)
    {S' : Set (ClassFunction L ℂ)} (hsub : S' ⊆ S)
    (hconj' : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S')
    (hSfin : S'.Finite) (hcard : 2 ≤ S'.ncard)
    (hirr : ∀ ζ ∈ S', ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S', ∀ b ∈ S', hyp.tau (a - b) ∈ ZIrr G)
    (hconst : ∀ a ∈ S', ∀ b ∈ S',
      ((a : ClassFunction L ℂ) : L → ℂ) 1 = ((b : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ∀ a ∈ S', ((a : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0) (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ a ∈ S', ∀ b ∈ S', ((a - b : ClassFunction L ℂ)).support ⊆ A) :
    Nonempty (IsCoherent hyp.tau S' A) := by
  -- `(hyp.restrict hsub hconj').tau = hyp.tau` definitionally; rewrite `hZIrr` through it so the
  -- `coherent_of_constant_degree` application's `tau`-typed argument aligns syntactically.
  have htau : (hyp.restrict hsub hconj').tau = hyp.tau := rfl
  refine coherent_of_constant_degree (hyp.restrict hsub hconj') hSfin hcard hirr ?_ hconst hdeg0
    h1A hsuppdiff
  rw [htau]; exact hZIrr

/-- **Peterfalvi (9.11): the degree-square-over-norm weight `Snorm ψ = ψ(1)²/'[ψ]` (real form).**

Coq `PFsection9.v:1534` `pose Snorm (psi : 'CF(M)) := psi 1%g ^+ 2 / '[psi]`.  The real-part form
`(ψ 1).re² / (⟨ψ,ψ⟩).re` used throughout §8 (`S08_CaseBEnumeration.lean:829`,
`S08_Theorem63.lean:46`): for an actual character `ψ`, `ψ(1)` is a real degree and `⟨ψ,ψ⟩` a
positive
real, so this real form agrees with the complex `ψ(1)²/⟨ψ,ψ⟩`. -/
noncomputable def Snorm (ψ : ClassFunction L ℂ) : ℝ :=
  (ψ (1 : L)).re ^ 2 / (ClassFunction.inner ψ ψ).re

/-- **Peterfalvi (9.11): the summed degree-square-over-norm `sumnS Si = ∑_{ψ ∈ Si} Snorm ψ`.**

Coq `PFsection9.v:1535` `pose sumnS Si := \sum_(psi <- Si) Snorm psi`.  Taken over a `Finset` of
class functions (the finite subfamilies `S1'`, `S2` of the (9.11) induction). -/
noncomputable def sumnS (Si : Finset (ClassFunction L ℂ)) : ℝ :=
  ∑ ψ ∈ Si, Snorm ψ

@[simp] theorem sumnS_empty : sumnS (L := L) (∅ : Finset (ClassFunction L ℂ)) = 0 := by
  simp [sumnS]

/-- Each `Snorm` weight is nonnegative (`ψ(1).re²` is a square, `⟨ψ,ψ⟩.re ≥ 0`). -/
theorem Snorm_nonneg (ψ : ClassFunction L ℂ) : 0 ≤ Snorm (L := L) ψ :=
  div_nonneg (sq_nonneg _) (inner_self_re_nonneg ψ)

/-- `sumnS` is monotone under `⊆` (adding nonnegative-`Snorm` members can only increase it). -/
theorem sumnS_le_of_subset {S₁ S₂ : Finset (ClassFunction L ℂ)} (h : S₁ ⊆ S₂) :
    sumnS (L := L) S₁ ≤ sumnS (L := L) S₂ :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ψ _ _ => Snorm_nonneg ψ

/-- **`Snorm` of a norm-one class function is its squared real degree** (`⟨ψ,ψ⟩.re = 1 ⟹
Snorm ψ = ψ(1).re²`).  For an irreducible character `ψ`, `IsIrreducibleCharacter.inner_self_eq_one`
gives `⟨ψ,ψ⟩ = 1`, hence `⟨ψ,ψ⟩.re = 1`; this is the `Snorm ψ = ψ(1)²` specialization used on the
uniform sub-family `S1'` of Peterfalvi (9.11), whose members are irreducible of degree `q·a`. -/
theorem Snorm_of_inner_self_re_one {ψ : ClassFunction L ℂ}
    (hψ : (ClassFunction.inner ψ ψ).re = 1) : Snorm (L := L) ψ = (ψ (1 : L)).re ^ 2 := by
  rw [Snorm, hψ, div_one]

/-- **`sumnS` of a family with constant `Snorm` weight** (`Snorm ψ = v` on `Si ⟹
sumnS Si = |Si|·v`).  The `Finset.sum_const` specialization of `sumnS`. -/
theorem sumnS_constant {Si : Finset (ClassFunction L ℂ)} {v : ℝ}
    (h : ∀ ψ ∈ Si, Snorm ψ = v) : sumnS (L := L) Si = (Si.card : ℝ) * v := by
  rw [sumnS, Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

/-- **Peterfalvi (9.11): the uniform sub-family `sumnS` value (Coq `lb3S1'` left endpoint).**

If every member of `Si` is norm-one (`⟨ψ,ψ⟩.re = 1`, e.g. irreducible) of common real degree `d`,
then `sumnS Si = |Si|·d²`.  This is the value Coq computes for `sumnS S1'` (`PFsection9.v:1607`,
`rewrite (eq_bigr (fun _ => ((q * a) ^ 2)%:R))`): on `S1'` every member is irreducible of degree
`q·a`, so `Snorm ≡ (q·a)²` and `sumnS S1' = |S1'|·(q·a)²` — the left endpoint of the
`lb3 ≤ sumnS S1'`
squeeze step, combined with the `lb_Sqa` lower bound `|S1'| ≥ (p−1)·|U:U'| / a²`. -/
theorem sumnS_of_norm_one_constant_degree {Si : Finset (ClassFunction L ℂ)} {d : ℝ}
    (hnorm : ∀ ψ ∈ Si, (ClassFunction.inner ψ ψ).re = 1)
    (hdeg : ∀ ψ ∈ Si, (ψ (1 : L)).re = d) :
    sumnS (L := L) Si = (Si.card : ℝ) * d ^ 2 :=
  sumnS_constant fun ψ hψ => by rw [Snorm_of_inner_self_re_one (hnorm ψ hψ), hdeg ψ hψ]

/-- **Peterfalvi (9.11): the `lb12` divisibility monotonicity `2a ≤ p−1` (`≤` form).**

Coq `PFsection9.v:1571` `have lb12: lb1 <= lb2 ?= iff (a == p.-1./2)`, with `lb1 = 2·a·q²·u` and
`lb2 = (p−1)·q²·u`.  After cancelling the positive `q²·u` the content is purely `ℕ`: with
`a ∣ (p−1)` (Coq `a_dvd_pm1`), `a` odd (odd order), and `p` odd — so `p−1` even (Coq
`Dp: p = 2·(p.-1./2)+1`) —
Gauss's lemma (`Nat.Coprime 2 a`, `a` odd) upgrades `a ∣ m` and `2 ∣ m` to `2·a ∣ m`, hence
`2·a ≤ m` by `Nat.le_of_dvd`.  Stated as a pure `ℕ` lemma; the caller identifies `m = p−1` and
multiplies through by `q²·u`. -/
theorem two_mul_le_of_dvd_of_odd {a m : ℕ} (hdvd : a ∣ m) (ha : Odd a) (hm : Even m)
    (hm0 : 0 < m) : 2 * a ≤ m :=
  Nat.le_of_dvd hm0 (ha.coprime_two_left.mul_dvd_of_dvd_of_dvd hm.two_dvd hdvd)

/-- **Peterfalvi (9.11): the `lb23` subgroup-index monotonicity `[U:C] ≤ [U:U']` (`≤` form).**

Coq `PFsection9.v:1590` `have lb23: lb2 <= lb3 ?= iff (C :==: U')`, with `lb2 = (p−1)·q²·u`,
`lb3 = (p−1)·q²·[U:U']` and `u = [U:C]`.  After cancelling `(p−1)·q²` the content is Lagrange
monotonicity of relative index: for nested subgroups `U' ≤ C ≤ U`, the relative index `[U:C]`
(`= C.relIndex U`) divides `[U:U']` (`Subgroup.relIndex_dvd_of_le_left`, the `U' ≤ C` half), so
`[U:C] ≤ [U:U']` (`Nat.le_of_dvd`, `[U:U'] > 0` from finiteness).  Stated group-theoretically over
an abstract finite group `Γ`; the caller identifies `u = [U:C]`, `[U:U']`, `p−1`, `q²` and the
ambient group.  (`_hCU : C ≤ U` records the full `U' ≤ C ≤ U` nesting of the `lb23` datum; the `≤`
bound itself needs only `U' ≤ C`, the strict/equality companion below uses both.) -/
theorem relIndex_le_relIndex_of_le {Γ : Type*} [Group Γ] [Finite Γ] {U' C U : Subgroup Γ}
    (hU'C : U' ≤ C) (_hCU : C ≤ U) : C.relIndex U ≤ U'.relIndex U :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.relIndex_dvd_of_le_left U hU'C)

/-- **Peterfalvi (9.11): the strict `lb23` bound off the equality (`C ≠ U' ⟹ [U:C]<[U:U']`).**

The strict companion of `relIndex_le_relIndex_of_le` supplying the `lb23` `?= iff (C:==:U')` clause.
From `[U:U'] = [C:U']·[U:C]` (`Subgroup.relIndex_mul_relIndex`, `U' ≤ C ≤ U`), equality
`[U:C] = [U:U']` forces `[C:U'] = 1` (cancel the positive `[U:U']`), i.e. `C ≤ U'`
(`Subgroup.relIndex_eq_one`); with `U' ≤ C` this is `C = U'`.  Contrapositive: `C ≠ U'` makes the
`lb23` squeeze strict.  Group-theoretic over a finite `Γ`; identification deferred to the caller. -/
theorem relIndex_lt_relIndex_of_le_of_ne {Γ : Type*} [Group Γ] [Finite Γ] {U' C U : Subgroup Γ}
    (hU'C : U' ≤ C) (hCU : C ≤ U) (hne : C ≠ U') : C.relIndex U < U'.relIndex U := by
  refine lt_of_le_of_ne (relIndex_le_relIndex_of_le hU'C hCU) ?_
  intro heq
  have hcomp : U'.relIndex C * C.relIndex U = U'.relIndex U :=
    Subgroup.relIndex_mul_relIndex U' C U hU'C hCU
  rw [heq] at hcomp
  have hpos : 0 < U'.relIndex U := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hone : U'.relIndex C = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hcomp)
  exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp hone) hU'C)

/-- **Peterfalvi (9.11): a maximal coherent conjugation-closed subfamily exists.**

*"Let `𝒮₂` be maximal such that `𝒮₁ ⊂ 𝒮₂ ⊂ 𝒮(H₀C′)`, `𝒮₂` is coherent and `𝒮₂` is closed
under complex conjugation."*  For a finite ambient family `S`, the collection of coherent
conjugation-closed intermediates `S₁ ⊆ S₂ ⊆ S` is finite and contains `S₁`, so a maximal one
exists (`Set.Finite.exists_maximalFor` on subset order).  The maximality clause is stated in the
"any bigger candidate collapses" form consumed by the refutation skeleton. -/
theorem exists_maximal_coherent_between
    {τ : IntegralCharacterMap L G} {A : Set L}
    {S S₁ : Set (ClassFunction L ℂ)} (hSfin : S.Finite) (hS₁S : S₁ ⊆ S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (h0 : Nonempty (IsCoherent τ S₁ A)) :
    ∃ S₂ : Set (ClassFunction L ℂ), S₁ ⊆ S₂ ∧ S₂ ⊆ S ∧
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ ∧ Nonempty (IsCoherent τ S₂ A) ∧
      ∀ S' : Set (ClassFunction L ℂ), S' ⊆ S →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S' → Nonempty (IsCoherent τ S' A) →
        S₂ ⊆ S' → S' = S₂ := by
  classical
  obtain ⟨S₂, hmem, hmax⟩ :=
    Set.Finite.exists_maximalFor (id : Set (ClassFunction L ℂ) → Set (ClassFunction L ℂ))
      {T | S₁ ⊆ T ∧ T ⊆ S ∧ OddOrder.Peterfalvi.S03.ClosedUnderConjugate T ∧
        Nonempty (IsCoherent τ T A)}
      (hSfin.finite_subsets.subset fun _ hT => hT.2.1)
      ⟨S₁, subset_rfl, hS₁S, hS₁conj, h0⟩
  obtain ⟨hS₁S₂, hS₂S, hS₂conj, hS₂coh⟩ := hmem
  refine ⟨S₂, hS₁S₂, hS₂S, hS₂conj, hS₂coh, fun S' hS'S hS'conj hS'coh hS₂S' => ?_⟩
  exact le_antisymm (hmax ⟨hS₁S₂.trans hS₂S', hS'S, hS'conj, hS'coh⟩ hS₂S') hS₂S'

/-- **Peterfalvi (9.11): the refute-the-maximal-subfamily skeleton.**

If every *proper* maximal coherent conjugation-closed intermediate `S₁ ⊆ S₂ ⊊ S` is absurd
(`hrefute` receives its maximality clause and must produce `False`), then the full family `S` is
coherent.  This is the outermost reduction of the (9.11) proof: the maximal `S₂` of
`exists_maximal_coherent_between` either equals `S` (done) or is handed to the refuter. -/
theorem coherent_of_maximal_coherent_refuted
    {τ : IntegralCharacterMap L G} {A : Set L}
    {S S₁ : Set (ClassFunction L ℂ)} (hSfin : S.Finite) (hS₁S : S₁ ⊆ S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (h0 : Nonempty (IsCoherent τ S₁ A))
    (hrefute : ∀ S₂ : Set (ClassFunction L ℂ), S₁ ⊆ S₂ → S₂ ⊆ S →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ → Nonempty (IsCoherent τ S₂ A) →
      S₂ ≠ S →
      (∀ S' : Set (ClassFunction L ℂ), S' ⊆ S →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S' → Nonempty (IsCoherent τ S' A) →
        S₂ ⊆ S' → S' = S₂) → False) :
    Nonempty (IsCoherent τ S A) := by
  obtain ⟨S₂, hS₁S₂, hS₂S, hS₂conj, hS₂coh, hS₂max⟩ :=
    exists_maximal_coherent_between hSfin hS₁S hS₁conj h0
  by_cases hS₂eq : S₂ = S
  · exact hS₂eq ▸ hS₂coh
  · exact (hrefute S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₂eq hS₂max).elim

/-- **Peterfalvi (9.11): the conjugate-pair form of the maximal-subfamily refutation.**

The specialization the (9.11) argument actually runs: the refuter receives a proper coherent
conjugation-closed `S₁ ⊆ S₂ ⊊ S` together with `𝒮₃ = S \ S₂ ≠ ∅` and the fact that **no
conjugate pair `{χ, χ̄}` with `χ ∈ 𝒮₃` can be coherently adjoined** — the negation of what the
(5.6) adjoining engine would produce.  Maximality converts a successful adjoining
`IsCoherent τ (S₂ ∪ {χ, χ̄}) A` into `S₂ ∪ {χ, χ̄} = S₂`, contradicting `χ ∉ S₂`; so the pair
clause holds for the maximal `S₂` and the refuter applies.  Requires the ambient family to be
conjugation-closed (so the adjoined pair stays inside `S`). -/
theorem coherent_of_maximal_coherent_pair_refuted
    {τ : IntegralCharacterMap L G} {A : Set L}
    {S S₁ : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (hSconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S) (hS₁S : S₁ ⊆ S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (h0 : Nonempty (IsCoherent τ S₁ A))
    (hrefute : ∀ S₂ : Set (ClassFunction L ℂ), S₁ ⊆ S₂ → S₂ ⊆ S →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ → Nonempty (IsCoherent τ S₂ A) →
      (S \ S₂).Nonempty →
      (∀ χ ∈ S \ S₂, ¬ Nonempty (IsCoherent τ (S₂ ∪ {χ, χ.conj}) A)) → False) :
    Nonempty (IsCoherent τ S A) := by
  refine coherent_of_maximal_coherent_refuted hSfin hS₁S hS₁conj h0 ?_
  intro S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₂ne hS₂max
  have hS₃ne : (S \ S₂).Nonempty := by
    rcases Set.eq_empty_or_nonempty (S \ S₂) with he | hne
    · exact absurd (Set.Subset.antisymm hS₂S (fun ψ hψ => by
        by_contra hψ₂
        exact Set.notMem_empty ψ (he ▸ Set.mem_sdiff_of_mem hψ hψ₂))) hS₂ne
    · exact hne
  refine hrefute S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne ?_
  rintro χ ⟨hχS, hχS₂⟩ ⟨hcoh'⟩
  have hS'S : S₂ ∪ {χ, χ.conj} ⊆ S := by
    rintro ψ (hψ | hψ)
    · exact hS₂S hψ
    · rcases hψ with rfl | hψ
      · exact hχS
      · rw [Set.mem_singleton_iff] at hψ
        exact hψ ▸ hSconj hχS
  have hS'conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (S₂ ∪ {χ, χ.conj}) := by
    rintro ψ (hψ | hψ)
    · exact Or.inl (hS₂conj hψ)
    · rcases hψ with rfl | hψ
      · exact Or.inr (Set.mem_insert_of_mem _ rfl)
      · rw [Set.mem_singleton_iff] at hψ
        subst hψ
        exact Or.inr (Set.mem_insert_iff.mpr (Or.inl (ClassFunction.conj_conj χ)))
  have heq := hS₂max _ hS'S hS'conj ⟨hcoh'⟩ Set.subset_union_left
  exact hχS₂ (heq ▸ Set.mem_union_right _ (Set.mem_insert _ _))

end OddOrder.Peterfalvi.S07


