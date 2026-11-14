-- Prove2me | Definitions.Def_RPLib_S4_JacDivisorsC
-- name    : RPLib_S4_JacDivisorsC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:17:24.211553+00:00
-- url     : https://prove2.me/theorems/cf37735b-c4ed-4090-b782-452d89bc2cad
-- title:
--   Modules of finite projective dimension over a local ring of depth zero are free
-- statement:
--   Let $(R,\mathfrak m)$ be a Noetherian local ring and $s \ne 0$ with $s\,\mathfrak m = 0$ (so $\operatorname{depth} R = 0$). Then every finitely generated $R$-module of finite projective dimension is free; in particular, if $\operatorname{pd}_R(R/\mathfrak m) < \infty$ then $\mathfrak m = 0$ and $R$ is a field. Consequently, if $R$ is not a field and $\operatorname{pd}_R(R/\mathfrak m) < \infty$, there is a non-zero-divisor $x \in \mathfrak m \setminus \mathfrak m^2$. The proof uses a minimal presentation $0 \to K \to R^\mu \to M \to 0$ with $K \subseteq \mathfrak m R^\mu$ and induction on the projective dimension.
--
--   **Formalization note.** This file is a library module (namespace `RamanujanPetersson.JacDivisors`) of a formalization of the Ramanujan-Petersson conjecture; it is the regular-local-ring part of that library. It contains definitions together with proved lemmas (no `sorry`), stated with Mathlib's `IsRegularLocalRing`, `Ideal.spanFinrank` and the categorical `HasProjectiveDimensionLT` on `ModuleCat`, so that later solution files can import them.
-- source:
--   H. Matsumura, Commutative Ring Theory, Cambridge Stud. Adv. Math. 8, Cambridge University Press 1986, doi:10.1017/CBO9781139171762, Section 19 (proof of Theorem 19.2)

import Mathlib
import Definitions.Def_RPLib_S4_JacDivisorsB

/-!
# S4-JacDivisors C (O2 and helpers for Serre's hard direction)
* `coeff_mem_maximalIdeal_of_minimal`: relations among a minimal generating set have all
  coefficients in `m`.
* `free_of_depth_zero` (O2): if `s ≠ 0` kills `m`, every finite module of finite projective dimension
  is free; `maximalIdeal_eq_bot_of_depth_zero`: then `pd k < ∞` forces `m = 0`.
* `exists_nonZeroDivisor_not_mem_sq`: prime avoidance over the associated primes and `m²`.
* `spanFinrank_maximalIdeal_le_quotient_add_one`: lifting generators from `R ⧸ (x)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

theorem coeff_mem_maximalIdeal_of_minimal [IsLocalRing R] {M : Type u} [AddCommGroup M]
    [Module R M] (t : Finset M) (ht : Submodule.span R (t : Set M) = ⊤)
    (hmin : ∀ t' : Finset M, Submodule.span R (t' : Set M) = ⊤ → t.card ≤ t'.card)
    (c : t →₀ R) (hc : Finsupp.linearCombination R (Subtype.val : t → M) c = 0) (i : t) :
    c i ∈ maximalIdeal R := by
  classical
  by_contra hi
  have hu : IsUnit (c i) := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hi
  set N := Submodule.span R ((t.erase i : Finset M) : Set M)
  have h1 : Finsupp.linearCombination R (Subtype.val : t → M) (c.erase i) ∈ N := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have hji : j ≠ i := by
      rintro rfl
      simp at hj
    exact Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h), j.2⟩
  have h2 : c i • (i : M) ∈ N := by
    have hsplit : c = c.erase i + Finsupp.single i (c i) := (Finsupp.erase_add_single i c).symm
    rw [hsplit, map_add, Finsupp.linearCombination_single] at hc
    rw [eq_neg_of_add_eq_zero_right hc]
    exact N.neg_mem h1
  have h3 : (i : M) ∈ N := (Submodule.smul_mem_iff_of_isUnit N hu).mp h2
  have h4 : N = ⊤ := by
    rw [eq_top_iff, ← ht, Submodule.span_le]
    intro y hy
    by_cases hyi : y = i
    · rw [hyi]; exact h3
    · exact Submodule.subset_span (Finset.mem_erase.mpr ⟨hyi, hy⟩)
  have h5 := hmin _ h4
  rw [Finset.card_erase_of_mem i.2] at h5
  have : 0 < t.card := Finset.card_pos.mpr ⟨i, i.2⟩
  omega

/-- O2: over a local ring of depth zero, finite modules of finite projective dimension are free. -/
theorem free_of_depth_zero [IsLocalRing R] [IsNoetherianRing R] {s : R} (hs : s ≠ 0)
    (hsm : ∀ y ∈ maximalIdeal R, s * y = 0) : ∀ (n : ℕ) (M : ModuleCat.{u} R), Module.Finite R M →
      HasProjectiveDimensionLT M (n + 1) → Module.Free R M := by
  intro n
  induction n with
  | zero =>
    intro M _ hM
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
    have : Module.Projective R M := (IsProjective.iff_projective (R := R) M).mpr this
    exact Module.free_of_flat_of_isLocalRing
  | succ n ih =>
    intro M _ hM
    classical
    obtain ⟨t, hcard, ht⟩ :=
      (Module.Finite.fg_top (R := R) (M := M)).exists_span_finset_card_eq_spanFinrank
    let f : (t →₀ R) →ₗ[R] M := Finsupp.linearCombination R (Subtype.val : t → M)
    have surj : Function.Surjective f := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      simpa using ht
    have hmin : ∀ t' : Finset M, Submodule.span R (t' : Set M) = ⊤ → t.card ≤ t'.card := by
      intro t' ht'
      rw [hcard, ← ht']
      simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := R) t'.finite_toSet
    have hS := LinearMap.shortExact_shortComplexKer surj
    have : Projective (ModuleCat.of R (t →₀ R)) :=
      ModuleCat.projective_of_free Finsupp.basisSingleOne
    have hK := (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
    have hKf : Module.Free R (LinearMap.ker f) := ih _ inferInstance hK
    have hsK : ∀ k : LinearMap.ker f, s • k = 0 := by
      intro k
      refine Subtype.ext (Finsupp.ext fun i => ?_)
      simp [hsm _ (coeff_mem_maximalIdeal_of_minimal t ht hmin _ (LinearMap.mem_ker.mp k.2) i)]
    have hK0 : Subsingleton (LinearMap.ker f) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      let b := Module.Free.chooseBasis R (LinearMap.ker f)
      obtain ⟨i⟩ := b.index_nonempty
      apply hs
      simpa using congr_arg (fun v => b.repr v i) (hsK (b i))
    have inj : Function.Injective f := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr
      fun c hc => congr_arg Subtype.val (Subsingleton.elim (⟨c, hc⟩ : LinearMap.ker f) 0))
    exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨inj, surj⟩)

/-- Depth zero and `pd k < ∞` force `m = 0`. -/
theorem maximalIdeal_eq_bot_of_depth_zero [IsLocalRing R] [IsNoetherianRing R] {s : R}
    (hs : s ≠ 0) (hsm : ∀ y ∈ maximalIdeal R, s * y = 0) (n : ℕ)
    (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) n) :
    maximalIdeal R = ⊥ := by
  have hk' : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1) :=
    hasProjectiveDimensionLT_of_ge _ n (n + 1) (by omega)
  have : Module.Free R (R ⧸ maximalIdeal R) := free_of_depth_zero hs hsm n _ inferInstance hk'
  let b := Module.Free.chooseBasis R (R ⧸ maximalIdeal R)
  obtain ⟨i⟩ := b.index_nonempty
  rw [eq_bot_iff]
  intro y hy
  have h0 : y • b i = 0 := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hy,
      zero_mul]
  have := congr_arg (fun v => b.repr v i) h0
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact (Submodule.mem_bot R).mpr this

/-- Prime avoidance: a nonzerodivisor in `m \ m²`, unless `m` consists of zero divisors. -/
theorem exists_nonZeroDivisor_not_mem_sq [IsLocalRing R] [IsNoetherianRing R]
    (hm : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hd : ¬ Disjoint (maximalIdeal R : Set R) (nonZeroDivisors R)) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ x ∈ nonZeroDivisors R := by
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ insert (maximalIdeal R ^ 2) (associatedPrimes R R), id i := by
    intro y hy
    by_cases hy2 : y ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion (Set.mem_insert _ _) hy2
    · have : y ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by
        rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]; exact hcon y hy hy2
      obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp this
      exact Set.mem_biUnion (Set.mem_insert_of_mem _ hP) hyP
  obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite ((associatedPrimes.finite R R).insert _)
    (f := id) (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
    (fun P hP h1 _ => ((Set.mem_insert_iff.mp hP).resolve_left h1).1)).mp hsub
  rcases Set.mem_insert_iff.mp hP with rfl | hP
  · exact hm hle
  · apply hd
    rw [Set.disjoint_left]
    intro a ha hnz
    have : a ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := Set.mem_biUnion hP (hle ha)
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at this
    exact this hnz

theorem mem_maximalIdeal_iff_quotient [IsLocalRing R] {x : R} [IsLocalRing (R ⧸ span {x})]
    (y : R) : y ∈ maximalIdeal R ↔ Ideal.Quotient.mk (span {x}) y ∈ maximalIdeal (R ⧸ span {x}) := by
  have h := IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (span {x})) Ideal.Quotient.mk_surjective (K := maximalIdeal (R ⧸ span {x})))
  rw [← h, Ideal.mem_comap]

/-- Lifting generators: `μ(m) ≤ μ(m / x) + 1`. -/
theorem spanFinrank_maximalIdeal_le_quotient_add_one [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 := by
  classical
  obtain ⟨t, hcard, ht⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (Ideal.fg_of_isNoetherianRing (maximalIdeal (R ⧸ span {x})))
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := span {x}))
  have hg : ∀ s, Ideal.Quotient.mk (span {x}) (g s) = s := Function.surjInv_eq _
  let T : Finset R := insert x (t.image g)
  have hT : span (T : Set R) = maximalIdeal R := by
    apply le_antisymm
    · rw [span_le]
      intro y hy
      simp only [T, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
        Finset.mem_coe] at hy
      rcases hy with rfl | ⟨s, hs, rfl⟩
      · exact hx
      · rw [SetLike.mem_coe, mem_maximalIdeal_iff_quotient (x := x), hg, ← ht]
        exact subset_span hs
    · intro y hy
      have h1 : Ideal.Quotient.mk (span {x}) y ∈
          (span ((t.image g : Finset R) : Set R)).map (Ideal.Quotient.mk (span {x})) := by
        rw [Ideal.map_span, Finset.coe_image, ← Set.image_comp]
        have : (Ideal.Quotient.mk (span {x}) ∘ g) = id := funext hg
        rw [this, Set.image_id]
        change _ ∈ Submodule.span (R ⧸ span {x}) (t : Set (R ⧸ span {x}))
        rw [ht]
        exact (mem_maximalIdeal_iff_quotient (x := x) y).mp hy
      obtain ⟨z, hz, hzy⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
      have hyz : y - z ∈ span {x} := Ideal.Quotient.eq.mp hzy.symm
      have hTx : span (T : Set R) = span {x} ⊔ span ((t.image g : Finset R) : Set R) := by
        simp only [T, Finset.coe_insert]
        exact Submodule.span_insert _ _
      rw [hTx]
      exact Submodule.mem_sup.mpr ⟨y - z, hyz, z, hz, by ring⟩
  calc (maximalIdeal R).spanFinrank = (span (T : Set R)).spanFinrank := by rw [hT]
    _ ≤ (T : Set R).ncard := Submodule.spanFinrank_span_le_ncard_of_finite T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ (t.image g).card + 1 := Finset.card_insert_le _ _
    _ ≤ t.card + 1 := by have := Finset.card_image_le (s := t) (f := g); omega
    _ = _ := by rw [hcard]

end RamanujanPetersson.JacDivisors


