-- Prove2me | Definitions.Def_RPLib_S4_EtShChartAlg
-- name    : RPLib_S4_EtShChartAlg
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:16:54.981449+00:00
-- url     : https://prove2.me/theorems/0619386d-c2c4-4f9e-a151-4b869d522540
-- title:
--   Etale charts with one generic point (algebra)
-- statement:
--   Let $A$ be a noetherian integrally closed domain, $R$ an etale $A$-algebra and $\mathfrak q$ a prime of $R$. There are $f_0 \in R$ and $f_1 \in R_{f_0}$ such that $\mathrm{Spec}\,(R_{f_0})_{f_1}$ contains a point over $\mathfrak q$ and at most one point over the generic point of $\mathrm{Spec}\,A$: $f_0$ makes $R_{f_0}$ standard etale (local structure of etale algebras) and $f_1$ separates the generic points of the standard etale chart.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Raynaud, Anneaux locaux henseliens, Lecture Notes in Math. 169, Springer (1970), Chapters V and VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 3

import Mathlib
import Definitions.Def_RPLib_S4_EtShGenChart

/-!
# S4-EtSheaves, O10f part e1: etale charts with one generic point (algebra)

Let `A` be a noetherian integrally closed domain, `R` an etale `A`-algebra and `q` a prime of `R`. There are
`f₀ ∈ R` and `f₁ ∈ R_{f₀}` such that `Spec (R_{f₀})_{f₁}` contains a point over `q` and at most one point over the
generic point of `Spec A` (`exists_chartAlg`): `f₀` makes `R_{f₀}` standard etale (`IsEtaleAt.exists_isStandardEtale`)
and `f₁` comes from `GenChart.exists_away_uniq`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtSheaves.ChartAlg

variable {A R : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing R] [Algebra A R] [Algebra.Etale A R]

/-- **Etale charts with one generic point**, algebraic form. -/
theorem exists_chartAlg (q : Ideal R) [q.IsPrime] :
    ∃ (f₀ : R) (f₁ : Localization.Away f₀) (P₀ : PrimeSpectrum (Localization.Away f₁)),
      (P₀.asIdeal.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁))).comap
        (algebraMap R (Localization.Away f₀)) = q ∧
      ∀ P₁ P₂ : PrimeSpectrum (Localization.Away f₁),
        ((P₁.asIdeal.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁))).comap
          (algebraMap R (Localization.Away f₀))).comap (algebraMap A R) = ⊥ →
        ((P₂.asIdeal.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁))).comap
          (algebraMap R (Localization.Away f₀))).comap (algebraMap A R) = ⊥ → P₁ = P₂ := by
  have : Algebra.IsEtaleAt A q := Algebra.FormallyEtale.comp A R (Localization.AtPrime q)
  obtain ⟨f₀, hf₀, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) q
  have hdisj : Disjoint (Submonoid.powers f₀ : Set R) q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf₀
  have hq' : (q.map (algebraMap R (Localization.Away f₀))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) _ q ‹_› hdisj
  have h1 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f₀) (Localization.Away f₀)
    ‹q.IsPrime› hdisj
  rw [Ideal.under] at h1
  let P := hstd.nonempty_standardEtalePresentation.some
  have : IsNoetherianRing (Localization.Away f₀) := GenChart.isNoetherianRing P
  obtain ⟨f₁, hf₁, huniq⟩ := GenChart.exists_away_uniq P (q.map (algebraMap R (Localization.Away f₀)))
  have hdisj' : Disjoint (Submonoid.powers f₁ : Set (Localization.Away f₀))
      (q.map (algebraMap R (Localization.Away f₀))) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf₁
  have h2 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f₁) (Localization.Away f₁) hq' hdisj'
  rw [Ideal.under] at h2
  refine ⟨f₀, f₁, ⟨(q.map (algebraMap R (Localization.Away f₀))).map (algebraMap _ (Localization.Away f₁)),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₁) _ _ hq' hdisj'⟩, ?_,
    fun P₁ P₂ e₁ e₂ => huniq P₁ P₂ ?_ ?_⟩
  · change (((q.map (algebraMap R (Localization.Away f₀))).map _).comap _).comap _ = q
    rw [h2, h1]
  · rw [IsScalarTower.algebraMap_eq A (Localization.Away f₀) (Localization.Away f₁), ← Ideal.comap_comap,
      IsScalarTower.algebraMap_eq A R (Localization.Away f₀), ← Ideal.comap_comap]
    exact e₁
  · rw [IsScalarTower.algebraMap_eq A (Localization.Away f₀) (Localization.Away f₁), ← Ideal.comap_comap,
      IsScalarTower.algebraMap_eq A R (Localization.Away f₀), ← Ideal.comap_comap]
    exact e₂

end RamanujanPetersson.EtSheaves.ChartAlg


