-- Prove2me | Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular
-- name    : Mathlib_RingTheory_RegularLocalRingQuotientRegular
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a4119926-0177-5bf2-9e12-f649738337aa
-- title:
--   Quotient of a regular local ring by an element outside m2
-- statement:
--   Throughout, $R$ is a commutative ring, assumed local and Noetherian (and, for the main results, regular local in Mathlib's sense `IsRegularLocalRing`, i.e. Noetherian local with $\operatorname{spanFinrank}\mathfrak m$ equal to the Krull dimension), and $x$ is an element of the maximal ideal $\mathfrak m =$ `maximalIdeal R`. The module introduces no new definitions; it collects statements about the quotient $R/(x)$, where $(x) =$ `Ideal.span {x}`. First, `isLocalRing_quotient_span_singleton`: for $x \in \mathfrak m$ the ring $R/(x)$ is again local. Next, for $x \in \mathfrak m \setminus \mathfrak m^2$ with $R$ Noetherian local: `exists_span_eq_maximalIdeal_ncard_le` produces a finite subset $S \subseteq R$ containing $x$, of cardinality at most $\operatorname{spanFinrank}\mathfrak m$, with $\operatorname{span} S = \mathfrak m$ (obtained by extending the linearly independent singleton given by the image of $x$ in the cotangent space $\mathfrak m/\mathfrak m^2$ to a basis over the residue field); `one_le_spanFinrank_maximalIdeal_of_notMem_sq` gives $\operatorname{spanFinrank}\mathfrak m \ge 1$; and `spanFinrank_map_quotientMk_le_sub_one`, together with its reformulation `spanFinrank_maximalIdeal_quotient_le_sub_one` for the maximal ideal of $R/(x)$, gives the inequality $\operatorname{spanFinrank} \le \operatorname{spanFinrank}\mathfrak m - 1$ (truncated subtraction in $\mathbb N$). Two auxiliary facts record that for $R$ Noetherian local the Krull dimension is finite, and that it is the cast of a natural number in `WithBot ℕ∞`. The main result `isRegularLocalRing_quotient_and_ringKrullDim_succ_eq` asserts, for $R$ regular local and $x \in \mathfrak m \setminus \mathfrak m^2$, that $R/(x)$ is regular local and that $\dim R/(x) + 1 = \dim R$; its two components are also stated separately, and `spanFinrank_maximalIdeal_quotient_succ_eq` records the corresponding equality of minimal numbers of generators, $\operatorname{spanFinrank}\mathfrak m_{R/(x)} + 1 = \operatorname{spanFinrank}\mathfrak m$. The dimension bound in the other direction comes from Mathlib's `ringKrullDim_le_ringKrullDim_quotient_add_encard`.
--
--   **Relation to Mathlib.** Everything is phrased in Mathlib's vocabulary (`IsLocalRing`, `IsRegularLocalRing`, `Submodule.spanFinrank`, `IsLocalRing.CotangentSpace`, `ringKrullDim`); no project-specific notion is introduced, and the statements supplement Mathlib's regular-local-ring API with the dimension-drop results for quotients by a single element of $\mathfrak m \setminus \mathfrak m^2$.
--
--   **Where it is used.** These results serve as commutative-algebra input elsewhere in the development, where regularity of a local ring is propagated to a quotient by one element of $\mathfrak m$ that is nonzero in the cotangent space, with the Krull dimension and the minimal number of generators of the maximal ideal each dropping by one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open IsLocalRing

namespace RegularQuotientEngine

variable (R : Type u) [CommRing R]

theorem isLocalRing_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hle : Ideal.span {x} ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hne : Ideal.span {x} ≠ ⊤ := fun htop =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (htop ▸ hle))
  haveI := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem exists_span_eq_maximalIdeal_ncard_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ S : Set R, x ∈ S ∧ S.Finite ∧ S.ncard ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span S = maximalIdeal R := by
  classical

  set ξ : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩ with hξdef
  have hξ0 : ξ ≠ 0 := by
    rw [hξdef, ne_eq, Ideal.toCotangent_eq_zero]
    exact hx2

  have hli : LinearIndepOn (ResidueField R) id ({ξ} : Set (CotangentSpace R)) := by
    refine LinearIndepOn.singleton' ?_
    intro r hr
    rcases smul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h hξ0

  obtain ⟨B, hξB, hBfin, hBcard, hBspan⟩ :
      ∃ B : Set (CotangentSpace R), ξ ∈ B ∧ B.Finite ∧
        B.ncard = (maximalIdeal R).spanFinrank ∧
        Submodule.span (ResidueField R) B = ⊤ := by
    refine ⟨hli.extend (Set.subset_univ _),
      hli.subset_extend _ (Set.mem_singleton ξ), ?_, ?_, ?_⟩
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      exact Set.toFinite _
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      haveI : Fintype (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Fintype.ofFinite _
      rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R,
        Module.finrank_eq_card_basis (Module.Basis.extend hli),
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    · have h1 := (Module.Basis.extend hli).span_eq
      rwa [Module.Basis.range_extend] at h1

  choose lift hlift using (maximalIdeal R).toCotangent_surjective
  set S₀ : Set ↥(maximalIdeal R) := insert ⟨x, hx⟩ (lift '' (B \ {ξ})) with hS₀def

  have himg : (maximalIdeal R).toCotangent '' S₀ = B := by
    rw [hS₀def, Set.image_insert_eq, ← hξdef, ← Set.image_comp]
    have hcomp : ((maximalIdeal R).toCotangent ∘ lift) '' (B \ {ξ}) = B \ {ξ} := by
      have : ∀ v ∈ B \ {ξ}, ((maximalIdeal R).toCotangent ∘ lift) v = id v :=
        fun v _ => hlift v
      rw [Set.image_congr this, Set.image_id]
    rw [hcomp, Set.insert_diff_singleton, Set.insert_eq_self.mpr hξB]

  have hspanR : Submodule.span R S₀ = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw [himg, hBspan]
  have hspan : Ideal.span ((↑) '' S₀ : Set R) = maximalIdeal R := by
    have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspanR
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap

  refine ⟨(↑) '' S₀, ⟨⟨x, hx⟩, by rw [hS₀def]; exact Set.mem_insert _ _, rfl⟩, ?_, ?_, hspan⟩
  · rw [hS₀def]
    exact (((hBfin.diff).image _).insert _).image _
  ·
    have hfin₁ : (lift '' (B \ {ξ})).Finite := (hBfin.diff).image _
    have h1 : ((↑) '' S₀ : Set R).ncard ≤ S₀.ncard := by
      apply Set.ncard_image_le
      rw [hS₀def]; exact hfin₁.insert _
    have h2 : S₀.ncard ≤ (lift '' (B \ {ξ})).ncard + 1 := by
      rw [hS₀def]; exact Set.ncard_insert_le _ _
    have h3 : (lift '' (B \ {ξ})).ncard ≤ (B \ {ξ}).ncard :=
      Set.ncard_image_le hBfin.diff
    have h4 : (B \ {ξ}).ncard + 1 = B.ncard :=
      Set.ncard_diff_singleton_add_one hξB hBfin
    omega

theorem one_le_spanFinrank_maximalIdeal_of_notMem_sq [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    1 ≤ (maximalIdeal R).spanFinrank := by
  by_contra h
  have h0 : (maximalIdeal R).spanFinrank = 0 := by omega
  have hbot : maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot
      ((maximalIdeal R).fg_of_isNoetherianRing)).mp h0
  rw [hbot, Ideal.mem_bot] at hx
  subst hx
  exact hx2 (Submodule.zero_mem _)

theorem spanFinrank_map_quotientMk_le_sub_one [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x}))).spanFinrank ≤
      (maximalIdeal R).spanFinrank - 1 := by
  obtain ⟨S, hxS, hSfin, hScard, hSspan⟩ := exists_span_eq_maximalIdeal_ncard_le R hx hx2
  have hmkx : (Ideal.Quotient.mk (Ideal.span {x})) x = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (S \ {x})) := by
    rw [← hSspan, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x
      · subst hyx
        rw [SetLike.mem_coe, hmkx]
        exact Submodule.zero_mem _
      · exact Ideal.subset_span ⟨y, ⟨hy, hyx⟩, rfl⟩
    · exact Ideal.span_mono (Set.image_mono Set.diff_subset)
  have h1 : ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x}))).spanFinrank ≤
      (S \ {x}).ncard := by
    rw [hmap]
    exact le_trans
      (Submodule.spanFinrank_span_le_ncard_of_finite ((hSfin.diff).image _))
      (Set.ncard_image_le hSfin.diff)
  have h2 : (S \ {x}).ncard + 1 = S.ncard :=
    Set.ncard_diff_singleton_add_one hxS hSfin
  omega

theorem spanFinrank_maximalIdeal_quotient_le_sub_one [IsLocalRing R] [IsNoetherianRing R]
    {x : R} [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ (maximalIdeal R).spanFinrank - 1 := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective]
  exact spanFinrank_map_quotientMk_le_sub_one R hx hx2

theorem ringKrullDim_lt_top_of_isNoetherianRing_of_isLocalRing
    [IsNoetherianRing R] [IsLocalRing R] : ringKrullDim R < ⊤ :=
  ringKrullDim_lt_top

theorem exists_ringKrullDim_eq_natCast [IsNoetherianRing R] [IsLocalRing R] :
    ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
  have h1 : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  have h2 : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  cases hd : ringKrullDim R with
  | bot => exact absurd hd h2
  | coe d =>
    cases d with
    | top => exact absurd hd (by simpa using h1)
    | coe d => exact ⟨d, rfl⟩

theorem isRegularLocalRing_quotient_and_ringKrullDim_succ_eq [IsRegularLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  haveI hloc : IsLocalRing (R ⧸ Ideal.span {x}) := isLocalRing_quotient_span_singleton R hx
  have hn1 : 1 ≤ (maximalIdeal R).spanFinrank :=
    one_le_spanFinrank_maximalIdeal_of_notMem_sq R hx hx2
  have hregR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hupper : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤
      (maximalIdeal R).spanFinrank - 1 :=
    spanFinrank_maximalIdeal_quotient_le_sub_one R hx hx2
  have hkrull : ringKrullDim (R ⧸ Ideal.span {x}) ≤
      ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})

  have hdle : d ≤ (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank := by
    have h := hkrull
    rw [hd] at h
    exact_mod_cast h

  have hlow : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    have hsub : ({x} : Set R) ⊆ ↑(Ring.jacobson R) := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hx
    simpa using ringKrullDim_le_ringKrullDim_quotient_add_encard ({x} : Set R) hsub
  have hnle : (maximalIdeal R).spanFinrank ≤ d + 1 := by
    have h := hlow
    rw [← hregR, hd] at h
    have h' : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
      refine h.trans (le_of_eq ?_)
      push_cast
      ring
    exact_mod_cast h'

  have hdeq : d + 1 = (maximalIdeal R).spanFinrank := by omega
  constructor
  · refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [hd]
    have hle : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ d := by omega
    exact_mod_cast hle
  · rw [hd, ← hregR]
    have hc : ((d : ℕ) : WithBot ℕ∞) + 1 = ((d + 1 : ℕ) : WithBot ℕ∞) := by
      push_cast
      ring
    rw [hc, hdeq]

theorem isRegularLocalRing_quotient_span_singleton [IsRegularLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
  (isRegularLocalRing_quotient_and_ringKrullDim_succ_eq R hx hx2).1

theorem ringKrullDim_quotient_span_singleton_succ_eq [IsRegularLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
  (isRegularLocalRing_quotient_and_ringKrullDim_succ_eq R hx hx2).2

theorem spanFinrank_maximalIdeal_quotient_succ_eq [IsRegularLocalRing R]
    {x : R} [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
  obtain ⟨hreg, hdim⟩ := isRegularLocalRing_quotient_and_ringKrullDim_succ_eq R hx hx2
  haveI := hreg
  have h1 : ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (R ⧸ Ideal.span {x}) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {x})
  have h2 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hcast : (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) =
      (((maximalIdeal R).spanFinrank : ℕ) : WithBot ℕ∞) := by
    push_cast
    rw [h1, hdim, ← h2]
  exact_mod_cast hcast

end RegularQuotientEngine

/--
info: 'RegularQuotientEngine.isLocalRing_quotient_span_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.isLocalRing_quotient_span_singleton

/--
info: 'RegularQuotientEngine.exists_span_eq_maximalIdeal_ncard_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.exists_span_eq_maximalIdeal_ncard_le

/--
info: 'RegularQuotientEngine.spanFinrank_map_quotientMk_le_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.spanFinrank_map_quotientMk_le_sub_one

/--
info: 'RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_le_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_le_sub_one

/--
info: 'RegularQuotientEngine.ringKrullDim_lt_top_of_isNoetherianRing_of_isLocalRing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.ringKrullDim_lt_top_of_isNoetherianRing_of_isLocalRing

/--
info: 'RegularQuotientEngine.exists_ringKrullDim_eq_natCast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.exists_ringKrullDim_eq_natCast

/--
info: 'RegularQuotientEngine.isRegularLocalRing_quotient_and_ringKrullDim_succ_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.isRegularLocalRing_quotient_and_ringKrullDim_succ_eq

/--
info: 'RegularQuotientEngine.isRegularLocalRing_quotient_span_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.isRegularLocalRing_quotient_span_singleton

/--
info: 'RegularQuotientEngine.ringKrullDim_quotient_span_singleton_succ_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.ringKrullDim_quotient_span_singleton_succ_eq

/--
info: 'RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_succ_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_succ_eq


