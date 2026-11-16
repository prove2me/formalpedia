-- Prove2me | Definitions.Def_RPLib_S4_EtShGenChart
-- name    : RPLib_S4_EtShGenChart
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:14:43.189953+00:00
-- url     : https://prove2.me/theorems/3e501a9e-a25b-4477-93a0-c0d24d5f6f4b
-- title:
--   Standard etale charts with one generic point
-- statement:
--   Let $B$ be an integrally closed domain and $S$ a noetherian standard etale $B$-algebra. For every prime $\mathfrak q$ of $S$ there is $f \notin \mathfrak q$ such that the open set $D(f) \subseteq \mathrm{Spec}\,S$ contains at most one prime lying over $(0) \subset B$; that is, $\mathrm{Spec}\,S_f$ has at most one point over the generic point of $\mathrm{Spec}\,B$. The element $f$ is a product of elements $f_{\mathfrak p} \in \mathfrak p \setminus \mathfrak q$, one for each of the finitely many minimal primes $\mathfrak p \not\subseteq \mathfrak q$, and the unibranch property of standard etale algebras over normal domains finishes the proof.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Raynaud, Anneaux locaux henseliens, Lecture Notes in Math. 169, Springer (1970), Chapters V and VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 3

import Mathlib
import Definitions.Def_RPLib_S4_EtShUnibranch

/-!
# S4-EtSheaves, O10f part d: standard etale charts with one generic point

Let `B` be an integrally closed domain and `S` a standard etale `B`-algebra which is noetherian. For every prime `q` of
`S` there is `f ∉ q` such that `D(f) ⊆ Spec S` contains at most one prime over `(0) ⊆ B` (`exists_away`), i.e.
`Spec S_f` has at most one point over the generic point of `Spec B` (`exists_away_uniq`).

Proof: `S` has finitely many minimal primes; let `f` be a product of elements `f_p ∈ p \ q`, one for each minimal
prime `p ⊄ q`. A prime `p₁` over `(0)` missing `f` contains a minimal prime `p`, which must lie in `q`; `p` is also over
`(0)`, so `p = p₁` by the unibranch property at `p₁`, hence `p₁ ⊆ q`. Two such primes lie in `q` and coincide by the
unibranch property at `q`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtSheaves.GenChart

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S] [IsDomain B] [IsIntegrallyClosed B]

open Classical in
/-- A chosen element of `p \ q` when `p ⊄ q` (and `1` otherwise). -/
def sep (q p : Ideal S) : S :=
  if h : ¬ p ≤ q then Classical.choose (SetLike.not_le_iff_exists.1 h) else 1

theorem sep_mem {q p : Ideal S} (h : ¬ p ≤ q) : sep q p ∈ p ∧ sep q p ∉ q := by
  rw [sep, dif_pos h]
  exact Classical.choose_spec (SetLike.not_le_iff_exists.1 h)

theorem sep_notMem (q : Ideal S) [q.IsPrime] (p : Ideal S) : sep q p ∉ q := by
  by_cases h : ¬ p ≤ q
  · exact (sep_mem h).2
  · rw [sep, dif_neg h]
    exact fun h1 => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one q).2 h1)

/-- A prime over `(0)` missing the product of the `sep q p` over the minimal primes lies in `q`. -/
theorem le_of_notMem (P : StandardEtalePresentation B S) (q : Ideal S) [q.IsPrime] (s : Finset (Ideal S))
    (hs : ∀ p ∈ minimalPrimes S, p ∈ s) (p₁ : Ideal S) [p₁.IsPrime]
    (hf : ∏ p ∈ s, sep q p ∉ p₁) (h0 : p₁.comap (algebraMap B S) = ⊥) : p₁ ≤ q := by
  obtain ⟨p, hp, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S) ≤ p₁)
  have : p.IsPrime := hp.1.1
  have hpq : p ≤ q := by
    by_contra h
    exact hf (Ideal.IsPrime.prod_mem_iff.2 ⟨p, hs p hp, hle (sep_mem h).1⟩)
  have hp0 : p.comap (algebraMap B S) = ⊥ := eq_bot_iff.2 ((Ideal.comap_mono hle).trans h0.le)
  rw [← Unibranch.unibranch P hle le_rfl hp0 h0]
  exact hpq

/-- **One generic prime near `q`**: some `f ∉ q` is outside at most one prime over `(0)`. -/
theorem exists_away (P : StandardEtalePresentation B S) [IsNoetherianRing S] (q : Ideal S) [q.IsPrime] :
    ∃ f ∉ q, ∀ p₁ p₂ : Ideal S, p₁.IsPrime → p₂.IsPrime → f ∉ p₁ → f ∉ p₂ →
      p₁.comap (algebraMap B S) = ⊥ → p₂.comap (algebraMap B S) = ⊥ → p₁ = p₂ := by
  let s : Finset (Ideal S) := (minimalPrimes.finite_of_isNoetherianRing S).toFinset
  have hs : ∀ p ∈ minimalPrimes S, p ∈ s := fun p hp => (Set.Finite.mem_toFinset _).2 hp
  refine ⟨∏ p ∈ s, sep q p, fun h => ?_, fun p₁ p₂ h₁ h₂ hf₁ hf₂ h₁0 h₂0 => ?_⟩
  · obtain ⟨p, -, hp⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact sep_notMem q p hp
  · exact Unibranch.unibranch P (le_of_notMem P q s hs p₁ hf₁ h₁0) (le_of_notMem P q s hs p₂ hf₂ h₂0) h₁0 h₂0

/-- **The same on `Spec S_f`**: at most one point of `Spec S_f` lies over the generic point of `Spec B`. -/
theorem exists_away_uniq (P : StandardEtalePresentation B S) [IsNoetherianRing S] (q : Ideal S) [q.IsPrime] :
    ∃ f ∉ q, ∀ P₁ P₂ : PrimeSpectrum (Localization.Away f),
      P₁.asIdeal.comap (algebraMap B (Localization.Away f)) = ⊥ →
      P₂.asIdeal.comap (algebraMap B (Localization.Away f)) = ⊥ → P₁ = P₂ := by
  obtain ⟨f, hfq, hf⟩ := exists_away P q
  refine ⟨f, hfq, fun P₁ P₂ h₁ h₂ => ?_⟩
  have hnm : ∀ Q : PrimeSpectrum (Localization.Away f), f ∉ Q.asIdeal.comap (algebraMap S _) := fun Q h =>
    Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.1 h) (IsLocalization.Away.algebraMap_isUnit f))
  have hc : ∀ Q : PrimeSpectrum (Localization.Away f),
      Q.asIdeal.comap (algebraMap B (Localization.Away f)) = ⊥ →
      (Q.asIdeal.comap (algebraMap S (Localization.Away f))).comap (algebraMap B S) = ⊥ := fun Q h => by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact h
  apply PrimeSpectrum.localization_comap_injective (Localization.Away f) (Submonoid.powers f)
  apply PrimeSpectrum.ext
  exact hf _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) (hnm P₁) (hnm P₂) (hc P₁ h₁) (hc P₂ h₂)

omit [IsDomain B] [IsIntegrallyClosed B] in
/-- The noetherian hypothesis holds when `B` is noetherian. -/
theorem isNoetherianRing (P : StandardEtalePresentation B S) [IsNoetherianRing B] : IsNoetherianRing S := by
  have : Algebra.IsStandardEtale B S := ⟨⟨P⟩⟩
  exact Algebra.FiniteType.isNoetherianRing B S

end RamanujanPetersson.EtSheaves.GenChart


