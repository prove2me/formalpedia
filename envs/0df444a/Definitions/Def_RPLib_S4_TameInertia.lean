-- Prove2me | Definitions.Def_RPLib_S4_TameInertia
-- name    : RPLib_S4_TameInertia
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T06:02:46.048439+00:00
-- url     : https://prove2.me/theorems/e6bd7d0e-63c5-4868-b6ec-5eb3eff67043
-- title:
--   Tame inertia at a boundary place: $\mathrm{Hom}_{cont}(I(Q), M) \cong M(-1)$
-- statement:
--   Let $Q$ be a nonzero prime of the integral closure of $R_0$ in $K_U$ (the maximal extension of $K$ unramified over the affine ring $A$) lying over a place $x$ of $R_0$ where some $a \in A$ has a pole, $N$ a unit in $A$ and $R_0$, and $\zeta \in K_U$ a primitive $N$-th root of unity fixed by $I(Q) \le \operatorname{Gal}(K_U/K)$. There are a locally constant homomorphism $\theta : I(Q) \to \mathbb{Z}/N$ and $\sigma_0 \in I(Q)$ with $\theta(\sigma_0) = 1$ such that $\theta(\sigma) = w\,\theta(\varphi^{-1}\sigma\varphi)$ for $\varphi$ in the decomposition group with $\varphi\zeta = \zeta^w$, and for every abelian group $M$ killed by $N$ evaluation at $\sigma_0$ is a bijection $$\mathrm{Hom}_{cont}(I(Q), M) \cong M, \qquad \chi \mapsto \chi(\sigma_0),$$ i.e. $\mathrm{Hom}_{cont}(I(Q), M) \cong M(-1)$ as a module over the decomposition group.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter IV, Section 2; A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose XIII; A. Grothendieck, J. P. Murre, The Tame Fundamental Group of a Formal Neighbourhood of a Divisor with Normal Crossings on a Scheme, Lecture Notes in Math. 208, Springer (1971); J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5 and Chapter V, Section 2

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaMain
import Definitions.Def_RPLib_S4_TameInertiaCoef

/-!
# Tame inertia (S4-PD item (2)): `Hom(I_x, M) = M(-1)` at a boundary place

Let `Q` be a boundary prime of the pro-chart of `K_U / K` (the maximal extension unramified over the affine ring `A`)
lying over a place `x` of `R0` where some `a ∈ A` has a pole, let `N` be a unit in `A` and `R0`, and let `ζ ∈ K_U` be a
primitive `N`-th root of unity fixed by the inertia group `I(Q) ≤ Pi1 A K`. Then (`tame_inertia`) there are a locally
constant homomorphism `θ : I(Q) → ℤ/N` (the tame character) and `σ₀ ∈ I(Q)` with `θ σ₀ = 1` such that

* (twist) for every `φ ∈ Pi1` stabilising `Q` (the decomposition group) with `φ ζ = ζ ^ w`,
  `θ σ = w * θ (φ⁻¹ σ φ)`: `θ` transforms by the cyclotomic character, i.e. `Hom(I(Q), ℤ/N) ≅ ℤ/N(-1)`;
* (coefficients) for every abelian group `M` killed by `N` (e.g. any `Λ`-module with `N Λ = 0`, such as `O/λ^n`),
  every locally constant homomorphism `χ : I(Q) → M` is `σ ↦ (θ σ).val • χ σ₀`, and every `m ∈ M` arises this way;
  so evaluation at `σ₀` is a bijection `Hom_cont(I(Q), M) ≅ M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- **Tame inertia (S4-PD item (2)).** `Hom_cont(I(Q), M) ≅ M(-1)` for every `N`-torsion coefficient group `M`,
with the twist by the cyclotomic character of the decomposition group. -/
theorem tame_inertia {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N : ℕ} [NeZero N]
    (hNA : IsUnit (N : A)) (hNR : IsUnit (N : R0)) {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
    (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : IsDedekindDomain.HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a)) :
    ∃ θ : Q.inertia (Pi1 A K) → ZMod N, ∃ σ₀ : Q.inertia (Pi1 A K),
      IsLocallyConstant θ ∧ (∀ σ τ, θ (σ * τ) = θ σ + θ τ) ∧ θ σ₀ = 1 ∧
      (∀ φ : Pi1 A K, ∀ hφ : (∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q), ∀ w : ZMod N, φ ζ = epow ζ w →
        ∀ σ (hσ : σ ∈ Q.inertia (Pi1 A K)), θ ⟨σ, hσ⟩ = w * θ ⟨φ⁻¹ * σ * φ, inertia_conj hφ hσ⟩) ∧
      ∀ (M : Type) [AddCommGroup M], (∀ m : M, N • m = 0) →
        (∀ χ : Q.inertia (Pi1 A K) → M, IsLocallyConstant χ → (∀ σ τ, χ (σ * τ) = χ σ + χ τ) →
          ∀ σ, χ σ = (θ σ).val • χ σ₀) ∧
        ∀ m : M, IsLocallyConstant (fun σ => (θ σ).val • m) ∧
          (∀ σ τ, (θ (σ * τ)).val • m = (θ σ).val • m + (θ τ).val • m) ∧ (θ σ₀).val • m = m := by
  obtain ⟨θ, hθc, hθm, ⟨σ₀, hθ1⟩, huniq, htw⟩ := exists_tame_char (p := p) hQ hNA hNR hζ hζI x hx ha
  refine ⟨θ, σ₀, hθc, hθm, hθ1, htw, fun M _ hM => ⟨fun χ hχc hχ σ => ?_, fun m => ⟨?_, ?_, ?_⟩⟩⟩
  · exact eq_val_nsmul_of_gen hM hθ1 (fun χ' hc' h' => (huniq χ' hc' h').exists) χ hχc hχ σ
  · exact isLocallyConstant_val_nsmul hθc m
  · exact val_nsmul_mul hM hθm m
  · rw [hθ1]
    exact one_val_nsmul hM m

end

end TameInertia
end RamanujanPetersson


