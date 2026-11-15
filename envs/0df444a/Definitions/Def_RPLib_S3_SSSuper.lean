-- Prove2me | Definitions.Def_RPLib_S3_SSSuper
-- name    : RPLib_S3_SSSuper
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:25:52.494658+00:00
-- url     : https://prove2.me/theorems/497f958a-f930-498e-a29e-7dcde8d75daa
-- title:
--   Weight-two Ramanujan-Petersson library: boundedly many supersingular pairs (`DWSSuper`)
-- statement:
--   Boundedly many supersingular pairs (`DWSSuper`).
--
--   Over `F_{p^m}`, a pair `(E(b,c), P) ∈ Y₁(M)` with `p ∣ a_E` has `j ∈ jSet p`, a set of at most `deg HZ_p + 2`
--   elements (`jv_mem_jSet`: the Hasse invariant for `p` odd, the `2`-torsion point for `p = 2`). Each `j`-fibre of
--   `Y₁(M)(F)` has at most `M²` points (`card_fibre_le`), so `Σ_{p ∣ t} pairCount F M t ≤ (deg HZ_p + 2) M²`,
--   uniformly in `m` (`dwsSuper : DWSSuper`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_SSHasseC

/-!
# S3-DWS-Supersingular, part B6: boundedly many supersingular pairs (`DWSSuper`)

Over `F_{p^m}`, a pair `(E(b,c), P) ∈ Y₁(M)` with `p ∣ a_E` has `j ∈ jSet p`, a set of at most `deg HZ_p + 2`
elements (`jv_mem_jSet`: the Hasse invariant for `p` odd, the `2`-torsion point for `p = 2`). Each `j`-fibre of
`Y₁(M)(F)` has at most `M²` points (`card_fibre_le`), so `Σ_{p ∣ t} pairCount F M t ≤ (deg HZ_p + 2) M²`,
uniformly in `m` (`dwsSuper : DWSSuper`).
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve RPLib RPLib.TateNF

namespace RamanujanPetersson.S3.DWSS

section Super

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The candidate supersingular `j`-values: `{0, 1728} ∪ {1728 + 1/t : HF(t) = 0}`. -/
noncomputable def jSet (p : ℕ) : Finset F :=
  {0, 1728} ∪ (HF F p).roots.toFinset.image (fun t => 1728 + 1 / t)

omit [Fintype F] in
lemma card_jSet_le (p : ℕ) : (jSet (F := F) p).card ≤ (HZ p).natDegree + 2 := by
  have h1 := Finset.card_union_le ({0, 1728} : Finset F) ((HF F p).roots.toFinset.image (fun t => 1728 + 1 / t))
  have h2 : ({0, 1728} : Finset F).card ≤ 2 := Finset.card_le_two
  have h3 := (Finset.card_image_le (s := (HF F p).roots.toFinset) (f := fun t => 1728 + 1 / t)).trans
    ((Multiset.toFinset_card_le _).trans ((card_roots' (HF F p)).trans (natDegree_HF_le (F := F) p)))
  rw [jSet]; omega

theorem jv_mem_jSet (p : ℕ) [Fact p.Prime] [CharP F p] {m : ℕ} (hq : Fintype.card F = p ^ m) {b c : F}
    (hD : tateDisc b c ≠ 0) (h : (p : ℤ) ∣ EllFq.trace (tate b c)) : jv b c ∈ jSet (F := F) p := by
  have hp : p.Prime := Fact.out
  rcases hp.eq_two_or_odd with h2 | hpo
  · subst h2
    have hF : ringChar F = 2 := ringChar.eq F 2
    rw [jv_of_c₄ (c₄_eq_zero_of_two_dvd_trace hF hD (by exact_mod_cast h))]
    simp [jSet]
  · have hp2 : p ≠ 2 := by omega
    have : (tate b c).IsElliptic := isElliptic_tate hD
    have hA := hasseA_eq_zero_of_dvd_trace p hp2 hq (tate b c) h
    rcases jv_mem_of_hasseA p hD hA with h0 | h1 | ⟨t, ht, hj⟩
    · simp [jSet, h0]
    · simp [jSet, h1]
    · rw [hj]; unfold jSet
      apply Finset.mem_union_right
      apply Finset.mem_image_of_mem
      rw [Multiset.mem_toFinset, mem_roots (HF_ne_zero p hpo)]; exact ht

/-- **B6.** The pairs with `p ∣ a_E` (any set `T` of traces divisible by `p`). -/
theorem sum_pairCount_le (p : ℕ) [Fact p.Prime] [CharP F p] {m M : ℕ} (hM : 4 ≤ M) (hMF : (M : F) ≠ 0)
    (hq : Fintype.card F = p ^ m) (T : Finset ℤ) (hT : ∀ t ∈ T, (p : ℤ) ∣ t) :
    ∑ t ∈ T, pairCount F M t ≤ ((HZ p).natDegree + 2) * M ^ 2 := by
  classical
  set A := Finset.univ.filter (fun bc : F × F => bc ∈ Y1 F M ∧ EllFq.trace (tate bc.1 bc.2) ∈ T) with hA
  have HT : ∀ x ∈ A, EllFq.trace (tate x.1 x.2) ∈ T := fun x hx => (Finset.mem_filter.mp hx).2.2
  have hsum : ∑ t ∈ T, pairCount F M t = A.card := by
    rw [Finset.card_eq_sum_card_fiberwise (s := A) (t := T) (f := fun bc : F × F => EllFq.trace (tate bc.1 bc.2)) HT]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [pairCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext bc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
    constructor
    · rintro ⟨hY, rfl⟩; exact ⟨⟨hY, ht⟩, rfl⟩
    · rintro ⟨⟨hY, -⟩, rfl⟩; exact ⟨hY, rfl⟩
  have HS : ∀ x ∈ A, jv x.1 x.2 ∈ jSet (F := F) p := fun x hx => by
    have hx' := Finset.mem_filter.mp hx
    exact jv_mem_jSet p hq hx'.2.1.1 (hT _ hx'.2.2)
  rw [hsum, Finset.card_eq_sum_card_fiberwise (s := A) (t := jSet (F := F) p)
    (f := fun bc : F × F => jv bc.1 bc.2) HS]
  calc ∑ s ∈ jSet (F := F) p, (A.filter (fun bc => jv bc.1 bc.2 = s)).card
        ≤ ∑ s ∈ jSet (F := F) p, M ^ 2 := by
          refine Finset.sum_le_sum fun s _ => ?_
          have h := (card_fibre_le hM hMF s).2
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
          refine le_trans (Finset.card_le_card ?_) h
          intro bc hbc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA] at hbc ⊢
          exact ⟨hbc.1.1, hbc.2⟩
    _ = (jSet (F := F) p).card * M ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_jSet_le p)

/-- **`DWSSuper`.** Boundedly many pairs `(E, P)/F_{p^m}` with `p ∣ a_E`, uniformly in `m`. -/
theorem dwsSuper : DWSSuper := by
  intro M _ hM p _ hpM
  refine ⟨((HZ p).natDegree + 2) * M ^ 2, fun m F _ _ _ hq => ?_⟩
  have : CharP F p := charP_of_card_eq_prime_pow hq
  have hMF : (M : F) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff F p M).mp h)
  exact sum_pairCount_le p hM hMF hq _ (fun t ht => (Finset.mem_filter.mp ht).2)

end Super

end RamanujanPetersson.S3.DWSS


