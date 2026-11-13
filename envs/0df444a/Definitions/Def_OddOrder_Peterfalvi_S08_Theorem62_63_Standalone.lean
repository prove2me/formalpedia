-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_Theorem62_63_Standalone
-- name    : OddOrder_Peterfalvi_S08_Theorem62_63_Standalone
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:21:55.930485+00:00
-- url     : https://prove2.me/theorems/e2f47f05-a8a6-4f64-9344-60d74ecfe7f9
-- title:
--   Peterfalvi (6.2)/(6.3): the standalone general (6.1) coherence theorems
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.1)-(6.3). Earlier files proved the coherence theorems (6.2)/(6.3) only in the Sibley–Dade capstone setup, where the induced-character kernel $K$ equals the nilpotent Frobenius complement $H$; this file states them for the general (6.1) hypothesis with $K$ solvable.
--
--   Main results: `six_two_general` (the general (6.2) form), `inducedMember_re_le_general` (the (6.2) $\theta$-bound for an induced member of a general solvable kernel) and `six_three_index_bound_general` (the (6.3) per-step index bound), plus `subset` (coherence is inherited by subsets).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

variable [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

namespace IsCoherent

variable {τ : IntegralCharacterMap L G} {S S' : Set (ClassFunction L ℂ)} {A : Set L}

/-- **Coherence is inherited by subsets.**  If `(S, A, τ)` is coherent and `S' ⊆ S` still admits a
nonzero `A`-supported element of `ℤ[S']`, then `(S', A, τ)` is coherent.

The *same* coherent extension works: `ℤ[S'] ≤ ℤ[S]` (`Submodule.span_mono`) so the lattice isometry
(`extension_inner_eq`) and the `ℤ[Irr G]`-codomain condition (`extension_mem_ZIrr`) restrict, and
`zSupportedSpan S' A ⊆ zSupportedSpan S A` (`zSupportedSpan_mono_left`) so agreement with `τ` on the
supported lattice (`extends_on_supported`) restricts.  Only the nondegeneracy witness `nonzero` has
to be re-supplied — it is genuinely set-dependent — hence the `hne` hypothesis.

This is the general monotonicity of Peterfalvi's (5.1) coherence predicate.  In the (6.2) coherence
dichotomy a smaller coherent set's witness `φ ∈ zSupportedSpan S(A) A` transports up by
`zSupportedSpan_mono_left`, so `hne` is always available when `S' ⊇` a known coherent set. -/
noncomputable def subset (hτ : IsCoherent τ S A) (hsub : S' ⊆ S)
    (hne : ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S' A ∧ φ ≠ 0) :
    IsCoherent τ S' A where
  nonzero := hne
  extension := hτ.extension
  extension_inner_eq := fun φ ψ hφ hψ =>
    hτ.extension_inner_eq φ ψ (Submodule.span_mono hsub hφ) (Submodule.span_mono hsub hψ)
  extends_on_supported := fun φ hφ =>
    hτ.extends_on_supported φ (zSupportedSpan_mono_left hsub hφ)
  extension_mem_ZIrr := fun φ hφ =>
    hτ.extension_mem_ZIrr φ (Submodule.span_mono hsub hφ)

end IsCoherent

end OddOrder.Peterfalvi.S07

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **Peterfalvi (6.3), general Hypothesis (6.1) form** (the minimal-`A` descent).

Let `K` be a solvable normal subgroup of `L` (the induced-family kernel `S = {Ind_K^L θ}`), and let
`M ≤ H₁ < H ≤ K` be normal subgroups with `H` nilpotent (Peterfalvi states `H/M` nilpotent; the
§11 consumer has `M = 1`, `H = HC` nilpotent).  Writing `S(·)` for the coherence functor `SOf`, if
`S(H₁)` is coherent and `|H : H₁| > 4|L:K|² + 1`, then `S(M)` is coherent.

The character-theoretic content — Peterfalvi (6.2) in index form, `|H:H₁| ≤ 4|L:K|² + 1` whenever a
proper section `B ⊆ A ⊆ H₁` has `A/B` central in `H/B`, `S(A)` coherent and `S(B)` not — is the
explicit **oracle** `h62`.  (In the Sibley case `h62` is `six_three_index_bound`; for a general
solvable `K` it bottoms out in the (5.6) bound for reducible induced members.)  Everything else is
proved here, mirroring `S08.six_three` but with `K` and `H` separated:

* the minimal coherent `A ∈ [M, H₁]` (`Set.Finite.exists_minimalFor`);
* the maximal proper normal `B` below it (`exists_maximal_normal_between`);
* `S(B)` not coherent (minimality of `A`);
* `A/B ⊆ Z(H/B)` (`normal_central_of_maximal_normal_below`, `H` nilpotent);
* `[K/A, K/A] ≠ ⊤` from `K` solvable and `A < K` (the degree-`|L:K|` anchor input of (6.2)).

This is the producer cited by `S13.coherent_S_of_coherent_SH0C` (Peterfalvi (11.3), `(6.3)` applied
with `(L,K,M,H,H₁) = (M, M', 1, HC, H₀C)`). -/
theorem six_three_descent
    {K H M H₁ : Subgroup ↥L} [Group.IsSolvable ↥K]
    [M.Normal] [H₁.Normal]
    [Group.IsNilpotent (↥H ⧸ M.subgroupOf H)] (hHnorm : H.Normal)
    (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H) (hHK : H ≤ K)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G) (A0 : Set ↥L)
    (SOf : Subgroup ↥L → Set (ClassFunction ↥L ℂ))
    (h62 : ∀ (A B : Subgroup ↥L) [A.Normal] [B.Normal], B ≤ A → A ≤ H₁ →
        _root_.commutator (↥K ⧸ A.subgroupOf K) ≠ ⊤ →
        (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
          Subgroup.center (↥H ⧸ B.subgroupOf H) →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf A) A0) →
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf B) A0) →
        Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * K.index ^ 2 + 1)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf H₁) A0))
    (hbound : 4 * K.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf M) A0) := by
  classical
  have : Finite (Subgroup ↥L) := Finite.of_injective (fun K : Subgroup ↥L => (K : Set ↥L))
    (fun _ _ h => SetLike.coe_injective h)
  set s : Set (Subgroup ↥L) := {A | A.Normal ∧ M ≤ A ∧ A ≤ H₁ ∧
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf A) A0)} with hs_def
  have hH₁s : H₁ ∈ s := by
    simp only [hs_def, Set.mem_ofPred_eq]; exact ⟨‹H₁.Normal›, hMH₁, le_refl _, hcoh⟩
  obtain ⟨A, hAmem, hAmin⟩ :=
    Set.Finite.exists_minimalFor (id : Subgroup ↥L → Subgroup ↥L) s (Set.toFinite _) ⟨H₁, hH₁s⟩
  simp only [hs_def, Set.mem_ofPred_eq] at hAmem
  obtain ⟨hAnorm, hMA, hAH₁, hAcoh⟩ := hAmem
  have : A.Normal := hAnorm
  have hAeqM : A = M := by
    by_contra hne
    have hMltA : M < A := lt_of_le_of_ne hMA (Ne.symm hne)
    obtain ⟨B, hBnorm, hMB, hBltA, hBmaxl⟩ := exists_maximal_normal_between hMltA
    have : B.Normal := hBnorm
    have hAltH : A < H := lt_of_le_of_lt hAH₁ hH₁H
    have hAltK : A < K := lt_of_lt_of_le hAltH hHK
    -- `[K/A, K/A] ≠ ⊤`: `K` solvable, `K/A` nontrivial (`A < K`).
    have hAcomm : _root_.commutator (↥K ⧸ A.subgroupOf K) ≠ ⊤ := by
      have : (A.subgroupOf K).Normal := (‹A.Normal›).subgroupOf K
      have : Nontrivial (↥K ⧸ A.subgroupOf K) := by
        rw [QuotientGroup.nontrivial_iff]
        intro htop
        exact hAltK.ne' (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hAltK.le)
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ A.subgroupOf K)).ne
    -- `A/B ⊆ Z(H/B)`: `H/B` nilpotent (a quotient of the nilpotent `H/M`, as `M ≤ B`), and
    -- `B` is maximal below `A`.
    have hnilB : Group.IsNilpotent (↥H ⧸ B.subgroupOf H) :=
      Group.nilpotent_of_surjective
        (QuotientGroup.map (M.subgroupOf H) (B.subgroupOf H) (MonoidHom.id ↥H)
          (by simpa using Subgroup.subgroupOf_mono H hMB))
        (by
          intro q
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := B.subgroupOf H) q
          exact ⟨QuotientGroup.mk x, by simp⟩)
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      hHnorm hAltH.le hBltA hBmaxl
    -- `S(B)` not coherent: else `B` beats the minimality of `A`.
    have hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf B) A0) := by
      intro hBcoh
      have hBs : B ∈ s := by
        simp only [hs_def, Set.mem_ofPred_eq]
        exact ⟨hBnorm, hMB, hBltA.le.trans hAH₁, hBcoh⟩
      exact lt_irrefl _ (hBltA.trans_le (hAmin hBs hBltA.le))
    have hbnd := h62 A B hBltA.le hAH₁ hAcomm hcentral hAcoh hSBncoh
    omega
  rw [← hAeqM]; exact hAcoh

set_option linter.unusedFintypeInType false in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Peterfalvi (6.3) per-step index bound, general (6.1) form** (`K` solvable, `H ≤ K`, `K ≠ H`).

The arithmetic glue from the (6.2) bound to the (6.3) index bound, separating `K` (the
induced-family kernel) from `H` (the nilpotent middle group).  The Sibley `six_three_index_bound`
has `K = H` (`|K:H| = 1`); here `K ≠ H` is allowed.  Given the (6.2) consequence for the section
`C = H, D = A` — `|K:A| − 1 ≤ 2|L:H|·√|H:A|` (`h62`) — the index `|H:H₁|` is at most `4|L:K|² + 1`.

Rewrites `|K:A| = |H:A|·|K:H|` (`relindex_mul_relindex`, `A ≤ H ≤ K`) and `|L:H| = |K:H|·|L:K|`
(`relindex_mul_index`, `H ≤ K`) into the `|K:H|·|H:A| − 1 ≤ 2|L:K|·|K:H|·√|H:A|` form consumed by
the arithmetic core `six_three_HH1_le` (`LK = |L:K|`, `KH = |K:H|`, `HA = |H:A|`).

Composing this with `six_three_descent` (supply `h62 := fun A B _ _ _ _ hA hB =>
six_three_index_bound_general … (six_two A B … hA hB)`) leaves the single remaining gate the general
`six_two` (the (6.2) bound for the possibly-reducible induced members of a solvable `K`). -/
theorem six_three_index_bound_general
    {K H A H₁ : Subgroup ↥L} (hAH₁ : A ≤ H₁) (hAH : A ≤ H) (hHK : H ≤ K)
    (h62 : (Nat.card (↥K ⧸ A.subgroupOf K) : ℝ) - 1 ≤
        2 * (H.index : ℝ) * Real.sqrt (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ)) :
    Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * K.index ^ 2 + 1 := by
  -- `relindex`/`Nat.card`-quotient identities (`relindex H K = (H.subgroupOf K).index`).
  have hcardKA : Nat.card (↥K ⧸ A.subgroupOf K) = A.relIndex K := (Subgroup.index_eq_card _).symm
  have hcardHA : Nat.card (↥H ⧸ A.subgroupOf H) = A.relIndex H := (Subgroup.index_eq_card _).symm
  have hcardHH1 : Nat.card (↥H ⧸ H₁.subgroupOf H) = H₁.relIndex H := (Subgroup.index_eq_card _).symm
  -- tower index multiplicativity: `|K:A| = |H:A|·|K:H|` and `|L:H| = |K:H|·|L:K|`.
  have key1 : A.relIndex K = A.relIndex H * H.relIndex K :=
    (Subgroup.relIndex_mul_relIndex A H K hAH hHK).symm
  have key2 : H.index = H.relIndex K * K.index := (Subgroup.relIndex_mul_index hHK).symm
  -- `1 ≤ |K:H|`.
  have hKHpos : 0 < H.relIndex K := by
    rw [show H.relIndex K = Nat.card (↥K ⧸ H.subgroupOf K) from (Subgroup.index_eq_card _).symm]
    exact Nat.card_pos
  -- `|H:H₁| ≤ |H:A|` (from `A ≤ H₁`, `A∩H ≤ H₁∩H`).
  have hHH1le : H₁.relIndex H ≤ A.relIndex H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono H hAH₁))
  rw [hcardHH1]
  refine six_three_HH1_le (LK := K.index) (KH := H.relIndex K) (HA := A.relIndex H)
    (HH1 := H₁.relIndex H) hKHpos hHH1le ?_
  -- the (6.2) real bound, recast into the `six_three_HH1_le` shape.
  rw [hcardKA, key1, key2, hcardHA] at h62
  set s : ℝ := Real.sqrt (A.relIndex H : ℝ) with hs
  calc (H.relIndex K : ℝ) * (A.relIndex H : ℝ) - 1
      = (A.relIndex H : ℝ) * (H.relIndex K : ℝ) - 1 := by ring
    _ ≤ 2 * ((H.relIndex K : ℝ) * (K.index : ℝ)) * s := by push_cast at h62 ⊢; linarith [h62]
    _ = 2 * (K.index : ℝ) * (H.relIndex K : ℝ) * s := by ring

/-- **Image in the centre of a quotient ⟺ commutator condition.**

For `N ◁ Γ` and `D ≤ Γ`, the image `D ⧸ N ↦ Γ ⧸ N` lands in the centre `Z(Γ ⧸ N)` iff every
`d ∈ D` commutes with every `g ∈ Γ` modulo `N` (`g d g⁻¹ d⁻¹ ∈ N`).  This is the elementwise
characterisation of "`D ⧸ N` central in `Γ ⧸ N`", letting the centrality hypothesis be transported
across the natural isomorphism `↥(H.subgroupOf K) ≃* ↥H` in `inducedMember_re_le_general`. -/
theorem map_mk'_le_center_iff {Γ : Type*} [Group Γ] {N D : Subgroup Γ} [N.Normal] :
    D.map (QuotientGroup.mk' N) ≤ Subgroup.center (Γ ⧸ N) ↔
      ∀ d ∈ D, ∀ g : Γ, g * d * g⁻¹ * d⁻¹ ∈ N := by
  rw [Subgroup.map_le_iff_le_comap]
  constructor
  · intro hle d hd g
    have hmem : QuotientGroup.mk' N d ∈ Subgroup.center (Γ ⧸ N) :=
      Subgroup.mem_comap.mp (hle hd)
    rw [Subgroup.mem_center_iff] at hmem
    have h2 := hmem (QuotientGroup.mk' N g)
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h2]; group
  · intro hcomm d hd
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hthis : QuotientGroup.mk' N (g * d * g⁻¹ * d⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hcomm d hd g
    simp only [map_mul, map_inv] at hthis
    rw [mul_inv_eq_one] at hthis
    calc QuotientGroup.mk' N g * QuotientGroup.mk' N d
        = (QuotientGroup.mk' N g * QuotientGroup.mk' N d * (QuotientGroup.mk' N g)⁻¹)
            * QuotientGroup.mk' N g := by group
      _ = QuotientGroup.mk' N d * QuotientGroup.mk' N g := by rw [hthis]

open scoped Classical in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Peterfalvi (6.2) θ-bound for an induced member of a general (solvable) kernel `K`.**

For a section `B ≤ D ≤ C ≤ K` (Peterfalvi's `B ⊂ D ⊂ C ⊂ K`) and an irreducible character `θ` of `K`
trivial on `B`, with `D ⧸ B` central in `C ⧸ B`, the induced member `ψ = Ind_K^L θ` has degree
bounded by `ψ(1) ≤ |L:C|·√|C:D|`.  The §11/§13 consumer applies this two ways: `(C, D) = (H, A)`
(the central case feeding (6.3)) and `(C, D) = (HC, HC)` (Peterfalvi (11.4), `√1 = 1`).

This is the half of `(6.2)` the consumer needs in its **general** form: the kernel `K` (the derived
subgroup `M'`, solvable) is strictly larger than the section group `C`, so unlike the Sibley central
case (`psi_degree_le_of_source_central`, `K = H = C`) the Clifford a-half is required.  The proof
feeds the fully general `theta_degree_le_index_mul_sqrt_index` (a-half + b-half) the section
`CK = C.subgroupOf K`, `NB = (B.subgroupOf K).subgroupOf CK ≤ DK = (D.subgroupOf K).subgroupOf CK`:

* the kernel hypothesis `NB ⊆ Ker(Res_{CK} θ)` is `characterKernel_restrict_subgroupOf`;
* the index identities `|CK| = |K:C|` and `|DK| = |C:D|` are `rfl` / `relIndex_subgroupOf`;
* the centrality `DK ⧸ NB ⊆ Z(CK ⧸ NB)` is transported from the given `D ⧸ B ⊆ Z(C ⧸ B)` across the
  natural isomorphism `e : ↥CK ≃* ↥C` (`subgroupOfEquivOfLe`, which preserves the underlying `↥L`
  element) using the commutator characterisation `map_mk'_le_center_iff`;
* `ψ(1) = |L:K|·θ(1)` (`induce_apply_one`) and `|L:K|·|K:C| = |L:C|` (`relIndex_mul_index`). -/
theorem inducedMember_re_le_general
    {K C D B : Subgroup ↥L} [Invertible (Nat.card ↥K : ℂ)] [B.Normal]
    (hBD : B ≤ D) (hCK : C ≤ K)
    (θ : IrreducibleCharacter ↥K)
    (hθB : (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (θ : ClassFunction ↥K ℂ))
    (hcentral : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (↥C ⧸ B.subgroupOf C)) :
    (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re ≤
      (C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ) := by
  have : Fintype ↥K := Fintype.ofFinite _
  have : (B.subgroupOf C).Normal := (‹B.Normal›).subgroupOf C
  set CK : Subgroup ↥K := C.subgroupOf K with hCK_def
  have : Fintype ↥CK := Fintype.ofFinite _
  have : Invertible (Nat.card ↥CK : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := ↥CK)).ne')
  have : (B.subgroupOf K).Normal := (‹B.Normal›).subgroupOf K
  set NB : Subgroup ↥CK := (B.subgroupOf K).subgroupOf CK with hNB
  set DK : Subgroup ↥CK := (D.subgroupOf K).subgroupOf CK with hDK
  have : NB.Normal := (‹(B.subgroupOf K).Normal›).subgroupOf CK
  have hNBDK : NB ≤ DK := Subgroup.subgroupOf_mono CK (Subgroup.subgroupOf_mono K hBD)
  -- the kernel hypothesis: `θ` trivial on `B` ⟹ `Res_{C∩K} θ` trivial on `NB`.
  have hθNB : (↑NB : Set ↥CK) ⊆ OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.restrict CK (θ : ClassFunction ↥K ℂ)) :=
    characterKernel_restrict_subgroupOf CK hθB
  -- centrality transport `D ⧸ B ⊆ Z(C ⧸ B)` ⟹ `DK ⧸ NB ⊆ Z(CK ⧸ NB)` across `e : ↥CK ≃* ↥C`.
  have hcentralCK : DK.map (QuotientGroup.mk' NB) ≤ Subgroup.center (↥CK ⧸ NB) := by
    rw [map_mk'_le_center_iff]
    rw [map_mk'_le_center_iff] at hcentral
    intro d hd c
    set e := Subgroup.subgroupOfEquivOfLe hCK with he_def
    have hcoe : ∀ x : ↥CK, ((e x : ↥C) : ↥L) = ((x : ↥K) : ↥L) := fun _ => rfl
    have hdD : e d ∈ D.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf, hcoe]
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hd)
    have key : (e c) * (e d) * (e c)⁻¹ * (e d)⁻¹ ∈ B.subgroupOf C := hcentral (e d) hdD (e c)
    have hcomm : (e c) * (e d) * (e c)⁻¹ * (e d)⁻¹ = e (c * d * c⁻¹ * d⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hcomm, Subgroup.mem_subgroupOf, hcoe] at key
    rw [hNB, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact key
  -- the general (6.2) θ-bound: `θ(1) ≤ |K:C|·√|C:D|`.
  have hθbound :=
    theta_degree_le_index_mul_sqrt_index (K := ↥K) θ CK (N := NB) DK hNBDK hθNB hcentralCK
  -- index identities `|CK| = |K:C|` and `|DK| = |C:D|`.
  have hCKindex : CK.index = C.relIndex K := rfl
  have hDKindex : DK.index = Nat.card (↥C ⧸ D.subgroupOf C) := by
    have hd0 : DK.index = (D.subgroupOf K).relIndex CK := rfl
    rw [hd0, hCK_def, Subgroup.relIndex_subgroupOf hCK]; rfl
  -- `ψ(1) = |L:K|·θ(1)`.
  have hind : (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re
      = (K.index : ℝ) * ((θ : ClassFunction ↥K ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind]
  calc (K.index : ℝ) * ((θ : ClassFunction ↥K ℂ) 1).re
      ≤ (K.index : ℝ) * ((CK.index : ℝ) * Real.sqrt (DK.index : ℝ)) :=
        mul_le_mul_of_nonneg_left hθbound (Nat.cast_nonneg _)
    _ = (C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ) := by
        rw [hDKindex, hCKindex, ← Subgroup.relIndex_mul_index hCK]; push_cast; ring

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Peterfalvi (6.2), general Hypothesis (6.1) form** (`K` solvable, section `B ⊆ D ⊆ C ⊆ K`).

Given the **(5.6) norm-weighted coherence bound** `h56` — proved from Hypothesis (5.2)'s image
families by `S08.exists_source_index_le_two_psi_of_imageData`
(`S08_SixTwoThreeFromImageFamilies`, issue 0153), and in the concrete §11/§13 context from the
`muGrid`/`columnSum` columns (`S12.Hypothesis.exists_source_of_coherence_dichotomy`) — this
produces the (6.2) real-inequality `|K:A| − 1 ≤ 2|L:C|·√|C:D|`.  The §11/§13 consumer instantiates
it two ways: `(C, D) = (H, A)` feeds `six_three_index_bound_general` (hence (6.3) /
`S13.coherent_S_of_coherent_SH0C`, Peterfalvi (11.3)); `(C, D) = (HC, HC)` (`√1 = 1`) gives
`|M':H₁| − 1 ≤ 2|M:HC|`, Peterfalvi (11.4) `S13.coherent_quotient_bound`.

The oracle `h56` packages the break member as `ψ = Ind_K^L θ` (`θ ∈ Irr K`, `θ` trivial on `B`,
`θ ≠ 1`; every member of the induced family `S` has this shape) with the degree bound
`|K:A| − 1 ≤ 2ψ(1)`.  Everything *downstream* of `h56` is proved here generally: the θ-degree bound
`ψ(1) ≤ |L:C|·√|C:D|` (`inducedMember_re_le_general`) and the arithmetic, so the §11/§13 consumer's
remaining obligation is exactly `h56`. -/
theorem six_two_general
    {K A C D B : Subgroup ↥L} [Invertible (Nat.card ↥K : ℂ)] [B.Normal]
    (hBD : B ≤ D) (hCK : C ≤ K)
    (hcentral : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (↥C ⧸ B.subgroupOf C))
    (h56 : ∃ θ : IrreducibleCharacter ↥K,
        (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥K ℂ) ∧
        (Nat.card (↥K ⧸ A.subgroupOf K) : ℝ) - 1 ≤
            2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re) :
    (Nat.card (↥K ⧸ A.subgroupOf K) : ℝ) - 1 ≤
        2 * (C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ) := by
  obtain ⟨θ, hθB, hψbound⟩ := h56
  have hdeg := inducedMember_re_le_general hBD hCK θ hθB hcentral
  calc (Nat.card (↥K ⧸ A.subgroupOf K) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re := hψbound
    _ ≤ 2 * ((C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ)) := by linarith [hdeg]
    _ = 2 * (C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ) := by ring

/-- **Peterfalvi (6.3), general (6.1) form, reduced to the (5.6) coherence oracle** — the
single-cite producer for the §11/§13 consumer.

Bundles the full standalone chain `six_three_descent ∘ six_three_index_bound_general ∘
six_two_general`: with `K` solvable normal, `H ≤ K` nilpotent (`K ≠ H` allowed), `M ≤ H₁ < H`, if
`S(H₁)` is coherent, `|H:H₁| > 4|L:K|² + 1`, **and** the per-section **(5.6) break-member oracle**
`h56` holds, then `S(M)` is coherent.

`h56` is the only remaining hypothesis with genuine character-theoretic content: for each section
`B ≤ A ≤ H₁` with `A ⧸ B` central in `H ⧸ B`, `S(A)` coherent and `S(B)` not, it asks for a break
member `ψ = Ind_K^L θ` (`θ ∈ Irr K` trivial on `B`) with `|K:A| − 1 ≤ 2ψ(1)`.  It is *proved* from
Hypothesis (5.2)'s image families in `S08_SixTwoThreeFromImageFamilies` (giving the oracle-free
`six_three_of_imageData`), and in the §11/§13 context from the `muGrid` columns
(`S12.Hypothesis.exists_source_of_coherence_dichotomy`).  Everything else — minimal-`A`/maximal-`B`
descent, nilpotency-forces-centrality, the θ-degree bound, and the `√`-arithmetic — is discharged
here.  This is the theorem `S13.coherent_S_of_coherent_SH0C` (Peterfalvi (11.3)) cites, applied
with `(L,K,M,H,H₁) = (M, M', 1, HC, H₀C)`. -/
theorem six_three_of_six_two_oracle
    {K H M H₁ : Subgroup ↥L} [Group.IsSolvable ↥K]
    [Invertible (Nat.card ↥K : ℂ)]
    [M.Normal] [H₁.Normal]
    [Group.IsNilpotent (↥H ⧸ M.subgroupOf H)] (hHnorm : H.Normal)
    (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H) (hHK : H ≤ K)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G) (A0 : Set ↥L)
    (SOf : Subgroup ↥L → Set (ClassFunction ↥L ℂ))
    (h56 : ∀ (A B : Subgroup ↥L) [A.Normal] [B.Normal], B ≤ A → A ≤ H₁ →
        (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
          Subgroup.center (↥H ⧸ B.subgroupOf H) →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf A) A0) →
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf B) A0) →
        ∃ θ : IrreducibleCharacter ↥K,
          (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥K ℂ) ∧
          (Nat.card (↥K ⧸ A.subgroupOf K) : ℝ) - 1 ≤
              2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf H₁) A0))
    (hbound : 4 * K.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf M) A0) := by
  refine six_three_descent hHnorm hMH₁ hH₁H hHK τ A0 SOf ?_ hcoh hbound
  intro A B _ _ hBA hAH₁ _hAcomm hcentral hAcoh hBncoh
  exact six_three_index_bound_general hAH₁ (hAH₁.trans hH₁H.le) hHK
    (six_two_general (A := A) (C := H) (D := A) (B := B) hBA hHK hcentral
      (h56 A B hBA hAH₁ hcentral hAcoh hBncoh))

end OddOrder.Peterfalvi.S08


