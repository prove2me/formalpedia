-- Prove2me | Definitions.Def_RPLib_S4_JacDivisorsA
-- name    : RPLib_S4_JacDivisorsA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:15:50.258942+00:00
-- url     : https://prove2.me/theorems/d78467f4-57de-40a5-9819-28eb5bb9f00a
-- title:
--   Cutting a regular local ring by an element of $\mathfrak m\setminus\mathfrak m^2$; regular local rings are domains
-- statement:
--   Let $(R,\mathfrak m)$ be a Noetherian local ring and $x \in \mathfrak m \setminus \mathfrak m^2$. Then $\mathfrak m = (x, t_1, \dots, t_r)$ with $r + 1 \le \mu(\mathfrak m)$, the minimal number of generators, and $\mu(\mathfrak m/(x)) + 1 \le \mu(\mathfrak m)$. If $R$ is regular ($\mu(\mathfrak m) = \dim R$), then $R/(x)$ is again regular local with $$\mu(\mathfrak m_{R/(x)}) + 1 = \mu(\mathfrak m), \qquad \dim R/(x) = \dim R - 1.$$ By induction on $\mu(\mathfrak m)$ and prime avoidance (choose $x \notin \mathfrak m^2$ outside every minimal prime), every regular local ring is an integral domain, and $(x)$ is a prime ideal for every $x \in \mathfrak m \setminus \mathfrak m^2$.
--
--   **Formalization note.** This file is a library module (namespace `RamanujanPetersson.JacDivisors`) of a formalization of the Ramanujan-Petersson conjecture; it is the regular-local-ring part of that library. It contains definitions together with proved lemmas (no `sorry`), stated with Mathlib's `IsRegularLocalRing`, `Ideal.spanFinrank` and the categorical `HasProjectiveDimensionLT` on `ModuleCat`, so that later solution files can import them.
-- source:
--   H. Matsumura, Commutative Ring Theory, Cambridge Stud. Adv. Math. 8, Cambridge University Press 1986, doi:10.1017/CBO9781139171762, Theorem 14.2 and Theorem 14.3

import Mathlib

/-!
# S4-JacDivisors A (O1): first facts on regular local rings
For `x ∈ m \ m²` in a regular local ring `R`, `R ⧸ (x)` is regular local with one generator fewer;
regular local rings are domains; such `x` generate prime ideals.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open IsLocalRing Ideal

universe u

section Cotangent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A nonzero vector extends to a spanning set with `finrank` elements. -/
theorem exists_finite_span_insert {v : V} (hv : v ≠ 0) :
    ∃ t : Set V, t.Finite ∧ t.ncard + 1 ≤ Module.finrank K V ∧
      Submodule.span K (insert v t) = ⊤ := by
  have hs : LinearIndepOn K id ({v} : Set V) := (linearIndepOn_singleton_iff K (v := id)).mpr hv
  let b := Module.Basis.extend hs
  set T := hs.extend (Set.subset_univ _) with hTdef
  have : Finite T := Module.Finite.finite_basis b
  have hT : T.Finite := Set.toFinite T
  have hvT : v ∈ T := hs.subset_extend _ (Set.mem_singleton v)
  refine ⟨T \ {v}, hT.sdiff, ?_, ?_⟩
  · rw [Set.ncard_sdiff_singleton_add_one hvT hT, Module.finrank_eq_nat_card_basis b,
      Nat.card_coe_set_eq]
  · rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hvT]
    have h := (Module.Basis.extend hs).span_eq
    rw [Module.Basis.range_extend] at h
    exact h

end Cotangent

variable {R : Type u} [CommRing R]

theorem isLocalRing_quotient_span [IsLocalRing R] {x : R} (hx : x ∈ maximalIdeal R) :
    IsLocalRing (R ⧸ span {x}) := by
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal x).mp hx)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- `x ∈ m \ m²` is part of a minimal generating set of `m`. -/
theorem exists_span_insert_eq_maximalIdeal [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ t : Set R, t.Finite ∧ t.ncard + 1 ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span (insert x t) = maximalIdeal R := by
  have hv : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  obtain ⟨t, htf, htc, hts⟩ := exists_finite_span_insert (K := ResidueField R) hv
  choose ℓ hℓ using fun w : CotangentSpace R => (maximalIdeal R).toCotangent_surjective w
  refine ⟨(fun w => (ℓ w : R)) '' t, htf.image _, ?_, ?_⟩
  · calc _ ≤ t.ncard + 1 := by gcongr; exact Set.ncard_image_le htf
      _ ≤ _ := by rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; exact htc
  · have key : Submodule.span R (insert (⟨x, hx⟩ : maximalIdeal R) (ℓ '' t)) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, Set.image_insert_eq, Set.image_image]
      simpa [hℓ] using hts
    have := congrArg (Submodule.map (maximalIdeal R).subtype) key
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_insert_eq,
      Set.image_image] at this
    exact this

theorem spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  obtain ⟨t, htf, htc, hts⟩ := exists_span_insert_eq_maximalIdeal hx hx2
  have hmap : maximalIdeal (R ⧸ span {x}) = Ideal.span (Ideal.Quotient.mk (span {x}) '' t) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hts,
      Ideal.map_span, Set.image_insert_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self x), Ideal.span_insert_zero]
  calc _ ≤ ((Ideal.Quotient.mk (span {x})) '' t).ncard + 1 := by
        rw [hmap]; gcongr; exact Submodule.spanFinrank_span_le_ncard_of_finite (htf.image _)
    _ ≤ t.ncard + 1 := by gcongr; exact Set.ncard_image_le htf
    _ ≤ _ := htc

/-- The Krull dimension of a Noetherian local ring is a natural number. -/
theorem exists_nat_ringKrullDim_eq [IsLocalRing R] [IsNoetherianRing R] :
    ∃ k : ℕ, ringKrullDim R = k := by
  have h := ringKrullDim_le_spanFinrank_maximalIdeal R
  have h0 : ringKrullDim R ≠ ⊥ := by
    intro h'
    have h0' := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [h'] at h0'
    exact absurd h0' (by simp)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp h0
  rw [← ha] at h ⊢
  have ha' : a ≤ (maximalIdeal R).spanFinrank := WithBot.coe_le_coe.mp h
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) ha')
  exact ⟨k, rfl⟩

/-- `R ⧸ (x)` is regular local for `x ∈ m \ m²`, and its maximal ideal needs one generator fewer. -/
theorem isRegularLocalRing_quotient [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧
      (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
  have h1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    have := ringKrullDim_le_ringKrullDim_quotient_add_encard (R := R) ({x} : Set R)
      (by simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using hx)
    simpa using this
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ span {x})
  have h4 : ringKrullDim R = (maximalIdeal R).spanFinrank :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  obtain ⟨k, hk⟩ := exists_nat_ringKrullDim_eq (R := R ⧸ span {x})
  rw [hk] at h2 h3
  rw [h4] at h2
  have h2' : (maximalIdeal R).spanFinrank ≤ k + 1 := by exact_mod_cast h2
  have h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast h3
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, by omega⟩
  rw [hk]
  exact_mod_cast (by omega : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ k)

/-- Prime avoidance: an element of `m` outside `m²` and outside every minimal prime. -/
theorem exists_mem_maximalIdeal_avoid [IsLocalRing R] [IsNoetherianRing R]
    (hm : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2) (hmin : maximalIdeal R ∉ minimalPrimes R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ P ∈ minimalPrimes R, x ∉ P := by
  classical
  by_contra hcon
  push Not at hcon
  let s : Finset (Ideal R) := insert (maximalIdeal R ^ 2)
    (minimalPrimes.finite_of_isNoetherianRing R).toFinset
  have hp : ∀ i ∈ s, i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → IsPrime (id i) := by
    intro i hi h1 _
    rcases Finset.mem_insert.mp hi with h | h
    · exact absurd h h1
    · exact ((Set.Finite.mem_toFinset _).mp h).1.1
  have hsub : ((maximalIdeal R : Set R)) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), id i := by
    intro y hy
    simp only [id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    by_cases hy2 : y ∈ maximalIdeal R ^ 2
    · exact ⟨_, by simp [s], hy2⟩
    · obtain ⟨P, hP, hyP⟩ := hcon y hy hy2
      exact ⟨P, by simp [s, hP], hyP⟩
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with h | h
  · exact hm (h ▸ hle)
  · have hP := (Set.Finite.mem_toFinset _).mp h
    have heq : i = maximalIdeal R := le_antisymm (le_maximalIdeal hP.1.1.ne_top) hle
    exact hmin (heq ▸ hP)

/-- Regular local rings are domains (induction on the number of generators of `m`). -/
theorem isDomain_of_spanFinrank_eq : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
    (maximalIdeal R).spanFinrank = n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    have hb : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h
    let := ((isField_iff_maximalIdeal_eq).mpr hb).toField
    infer_instance
  | succ n ih =>
    intro R _ _ h
    have hm : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
      intro hle
      have hb : maximalIdeal R = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
        (maximalIdeal R).fg_of_isNoetherianRing (by rwa [pow_two] at hle)
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
      rw [hb, Submodule.spanFinrank_bot] at h
      omega
    have hmin : maximalIdeal R ∉ minimalPrimes R := by
      intro hmin
      have h0 := (Ideal.height_eq_zero_iff (I := maximalIdeal R)).mpr hmin
      have h5 : ringKrullDim R = (maximalIdeal R).spanFinrank :=
        (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h0, h] at h5
      norm_cast at h5
    obtain ⟨x, hx, hx2, hxmin⟩ := exists_mem_maximalIdeal_avoid hm hmin
    haveI : IsLocalRing (R ⧸ span {x}) := isLocalRing_quotient_span hx
    obtain ⟨hreg, hcard⟩ := isRegularLocalRing_quotient hx hx2
    haveI := hreg
    have hdom : IsDomain (R ⧸ span {x}) := ih _ (by omega)
    haveI hprime : (span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ span {x})
    have hxP : x ∉ P := hxmin P hP
    have hPsm : P ≤ maximalIdeal R • P := by
      intro p hp
      obtain ⟨r, rfl⟩ := mem_span_singleton'.mp (hPle hp)
      have hr : r ∈ P := (hP.1.1.mem_or_mem hp).resolve_right hxP
      rw [mul_comm]
      exact Submodule.smul_mem_smul hx hr
    have hP0 : P = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      P.fg_of_isNoetherianRing hPsm (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
    haveI : (⊥ : Ideal R).IsPrime := hP0 ▸ hP.1.1
    exact IsDomain.of_bot_isPrime R

instance isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_eq _ R rfl

/-- For `x ∈ m \ m²` in a regular local ring, `(x)` is prime. -/
theorem isPrime_span_of_not_mem_sq [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) : (span {x}).IsPrime := by
  haveI : IsLocalRing (R ⧸ span {x}) := isLocalRing_quotient_span hx
  haveI := (isRegularLocalRing_quotient hx hx2).1
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end RamanujanPetersson.JacDivisors


