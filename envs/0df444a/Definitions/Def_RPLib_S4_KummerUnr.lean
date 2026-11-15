-- Prove2me | Definitions.Def_RPLib_S4_KummerUnr
-- name    : RPLib_S4_KummerUnr
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:15:46.487895+00:00
-- url     : https://prove2.me/theorems/bdc47067-1f69-4c9a-9593-c0e37ee1cf31
-- title:
--   Kummer roots of $N$-th-power ideal classes are unramified
-- statement:
--   Let $M$ be a finite Galois subextension of $\overline{K}/K$ unramified over $A$, $0 \ne a \in M$, $N$ invertible in $A$, and suppose that for every $\tau \in \operatorname{Gal}(M/K)$ there is a fractional ideal $I$ of the integral closure of $A$ in $M$ with $I^N \cdot (\tau a) = (1)$. The file proves that every $\gamma \in \overline{K}$ with $\gamma^N = a$ lies in $K_U$, the maximal extension of $K$ unramified over $A$. Along the way: an automorphism of $\overline{K}$ fixing $S$ fixes $K(S)$, and a lift to $\overline{K}$ of an inertia element of $\operatorname{Gal}(L/K)$ fixes every unramified Galois subextension of $L$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9; M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 10 (Kummer extensions)

import Mathlib
import Definitions.Def_RPLib_S4_KummerUnrCore

/-!
# S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified

* `mem_fixingSubgroup_adjoin`: an automorphism of `K̄` fixing `S` fixes `K(S)`.
* `lift_mem_fixingSubgroup`: a lift to `K̄` of an inertia element of `Gal(L/K)` fixes every unramified
  Galois subextension of `L` (the `key` step of `GalCover.sup_mem_unramSet`).
* `root_mem_maxUnram`: `M ∈ unramSet A K`, `0 ≠ a ∈ M`, `N` invertible in `A`, and for every `τ ∈ Gal(M/K)` a
  fractional ideal `I` of `integralClosure A M` with `I ^ N * (τ a) = 1`: every `γ ∈ K̄` with `γ ^ N = a` lies in
  `K_U = maxUnram A K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Kummer

noncomputable section

variable {K : Type} [Field K]

/-- An automorphism of `K̄` fixing a generating set fixes the intermediate field it generates. -/
theorem mem_fixingSubgroup_adjoin {S : Set (AlgebraicClosure K)}
    {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K} (h : ∀ x ∈ S, σ x = x) :
    σ ∈ (IntermediateField.adjoin K S).fixingSubgroup := by
  have hle : IntermediateField.adjoin K S ≤
      IntermediateField.fixedField (_root_.fixingSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (_root_.mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((_root_.mem_fixingSubgroup_iff _).2 h)

section Lift

variable (A : Type) [CommRing A] [Algebra A K]

/-- A lift `σ` to `K̄` of an inertia element `τ ∈ Gal(L/K)` fixes every unramified Galois subextension `L' ≤ L`. -/
theorem lift_mem_fixingSubgroup {L L' : IntermediateField K (AlgebraicClosure K)} (hle : L' ≤ L) [IsGalois K L']
    (uL : IsUnramifiedSub A K L') (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime] (τ : L ≃ₐ[K] L)
    (hτ : τ ∈ Q.inertia (L ≃ₐ[K] L)) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : ∀ y : L, σ (y : AlgebraicClosure K) = ((τ y : L) : AlgebraicClosure K)) : σ ∈ L'.fixingSubgroup := by
  have hP : (Q.comap (incl A K hle)).IsPrime := Ideal.IsPrime.comap _
  have hin : AlgEquiv.restrictNormalHom L' σ ∈ (Q.comap (incl A K hle)).inertia (L' ≃ₐ[K] L') := by
    intro y
    show (incl A K hle) (AlgEquiv.restrictNormalHom L' σ • y - y) ∈ Q
    have h : τ • incl A K hle y - incl A K hle y ∈ Q := hτ (incl A K hle y)
    convert h using 2
    apply Subtype.ext; apply Subtype.ext
    show ((AlgEquiv.restrictNormalHom L' σ (y : L') : L') : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
      = ((τ (incl A K hle y : L) : L) : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
    rw [AlgEquiv.restrictNormalHom_apply, ← hσ]
    rfl
  have h1 := uL _ hP
  rw [h1, Subgroup.mem_bot] at hin
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have := congrArg (fun e : L' ≃ₐ[K] L' => ((e ⟨x, hx⟩ : L') : AlgebraicClosure K)) hin
  simpa [AlgEquiv.restrictNormalHom_apply] using this

/-- **Kummer roots of `N`-th-power ideal classes are unramified.** -/
theorem root_mem_maxUnram {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N] (hN : IsUnit (N : A)) {a : M} (ha : a ≠ 0)
    (hI : ∀ τ : M ≃ₐ[K] M, ∃ I : FractionalIdeal (nonZeroDivisors (integralClosure A M)) M,
      I ^ N * FractionalIdeal.spanSingleton _ (τ a) = 1)
    {γ : AlgebraicClosure K} (hγ : γ ^ N = (a : AlgebraicClosure K)) : γ ∈ maxUnram A K := by
  obtain ⟨fM, gM, uM⟩ := hM
  have hNK : (N : K) ≠ 0 := by
    have h := hN.map (algebraMap A K)
    rw [map_natCast] at h
    exact h.ne_zero
  have hNM : (N : M) ≠ 0 := by
    rw [← map_natCast (algebraMap K M)]
    exact (_root_.map_ne_zero _).2 hNK
  have haint : IsIntegral K (a : AlgebraicClosure K) := Algebra.IsIntegral.isIntegral _
  set P : K[X] := (minpoly K (a : AlgebraicClosure K)).comp (X ^ N) with hPdef
  have hP0 : P ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
    rw [hPdef, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
    exact Nat.mul_pos (minpoly.natDegree_pos haint) (NeZero.pos N)
  -- every root of `P` is an `N`-th root of a Galois conjugate of `a`
  have hroot : ∀ y ∈ P.rootSet (AlgebraicClosure K), ∃ τ : M ≃ₐ[K] M,
      y ^ N = ((τ a : M) : AlgebraicClosure K) := by
    intro y hy
    have hy0 : aeval (y ^ N) (minpoly K (a : AlgebraicClosure K)) = 0 := by
      have h := (Polynomial.mem_rootSet.1 hy).2
      rwa [hPdef, Polynomial.aeval_comp, Polynomial.aeval_X_pow] at h
    have hsplit : ((minpoly K a).map (algebraMap K M)).Splits := Normal.splits inferInstance a
    rw [IntermediateField.minpoly_eq] at hsplit
    have hmem : y ^ N ∈ M := by
      refine (IntermediateField.splits_iff_mem (IsAlgClosed.splits _)).1 hsplit _ ?_
      exact Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero haint, hy0⟩
    have hmin : minpoly K (⟨y ^ N, hmem⟩ : M) = minpoly K a := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hy0 (minpoly.monic haint)).symm
    obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.1 ((Normal.minpoly_eq_iff_mem_orbit (F := K) (E := ↥M)).1 hmin)
    exact ⟨τ, by rw [← AlgEquiv.smul_def, hτ]⟩
  have hsep : ∀ y ∈ P.rootSet (AlgebraicClosure K), IsSeparable K y := by
    intro y hy
    obtain ⟨τ, hτ⟩ := hroot y hy
    have hb : τ a ≠ 0 := (_root_.map_ne_zero τ).2 ha
    have hpol : (X ^ N - C (τ a) : M[X]).Separable := separable_X_pow_sub_C (τ a) hNM hb
    have hay : aeval y (X ^ N - C (τ a) : M[X]) = 0 := by
      rw [map_sub, aeval_X_pow, aeval_C, hτ]
      exact sub_eq_zero.2 rfl
    have hsepM : IsSeparable M y := hpol.of_dvd (minpoly.dvd M y hay)
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable (F := K) (E := M) hsepM
  set E : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))
    with hEdef
  have hspl : IsSplittingField K E P := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional K E := IsSplittingField.finiteDimensional E P
  have : Normal K E := Normal.of_isSplittingField P
  have : Algebra.IsSeparable K E := (IntermediateField.isSeparable_adjoin_iff_isSeparable K (AlgebraicClosure K)).2 hsep
  have : IsGalois K E := ⟨⟩
  have hL : M ⊔ E ∈ unramSet A K := by
    refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
    rw [eq_bot_iff]
    intro τ hτ
    rw [Subgroup.mem_bot]
    obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ y : ↥(M ⊔ E),
        σ (y : AlgebraicClosure K) = ((τ y : ↥(M ⊔ E)) : AlgebraicClosure K) :=
      ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
    have hσM : σ ∈ M.fixingSubgroup := lift_mem_fixingSubgroup A le_sup_left uM Q τ hτ σ hσ
    have hτM : ∀ x : M, τ (IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) x) =
        IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) x := by
      intro x
      apply Subtype.ext
      rw [← hσ]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσM _ x.2
    have hσE : σ ∈ E.fixingSubgroup := by
      apply mem_fixingSubgroup_adjoin
      intro y hy
      obtain ⟨τ', hτ'⟩ := hroot y hy
      obtain ⟨I, hI'⟩ := hI τ'
      have hyL : y ∈ M ⊔ E := (le_sup_right : E ≤ M ⊔ E) (IntermediateField.subset_adjoin K _ hy)
      have hpow : (⟨y, hyL⟩ : ↥(M ⊔ E)) ^ N = IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) (τ' a) :=
        Subtype.ext (by simpa using hτ')
      have hfix := fixed_of_inertia (le_sup_left : M ≤ M ⊔ E) hN Q τ hτ hτM I hI' ⟨y, hyL⟩ hpow
      have := hσ ⟨y, hyL⟩
      rw [hfix] at this
      exact this
    have hfix : σ ∈ (M ⊔ E).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hσM, hσE⟩
    ext y
    rw [AlgEquiv.one_apply, ← hσ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix _ y.2
  have hγE : γ ∈ E := by
    apply IntermediateField.subset_adjoin
    refine Polynomial.mem_rootSet.2 ⟨hP0, ?_⟩
    rw [hPdef, Polynomial.aeval_comp, Polynomial.aeval_X_pow, hγ]
    exact minpoly.aeval K _
  exact le_iSup (fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K))) ⟨_, hL⟩
    ((le_sup_right : E ≤ M ⊔ E) hγE)

end Lift

end

end Kummer
end RamanujanPetersson


