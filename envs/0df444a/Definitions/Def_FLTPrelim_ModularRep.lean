-- Prove2me | Definitions.Def_FLTPrelim_ModularRep
-- name    : FLTPrelim_ModularRep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/36eae137-d50f-53f0-8651-d08d0db7a7d4
-- title:
--   Residual modularity: congruences of Hecke eigenvalues with a curve
-- statement:
--   The module fixes the ring $\overline{\mathbb Z} =$ `integralClosure ℤ ℂ` of all algebraic integers and two facts about it: for $p$ prime, $p$ is not a unit there (otherwise $1/p$ would be integral over $\mathbb Z$, contradicting integral closedness of $\mathbb Z$ in $\mathbb Q$), hence some maximal ideal $\mathfrak m$ contains $p$.
--
--   The central predicates express "the mod-$p$ representation of a curve comes from a weight-$2$ eigenform" as a congruence of Hecke eigenvalues with traces of Frobenius, not as an isomorphism of representations. [`FreyPackage.ModularRepOfLevel P N`](../def/FLTPrelim_ModularRep.html#L62) asserts the existence of $f \in S_2(\Gamma_0(N))$ with `IsNormalizedEigenform` (a structure whose fields are coefficient identities for $q$-expansion coefficients: $a_1 = 1$, multiplicativity at coprime indices, and the two prime-power recursions, with $-p\,a_{p^r}$ present exactly when $p \nmid N$ — Hecke operators do not appear), a Weierstrass model $W$ over $\mathbb Z$ which is an integral model of `P.freyCurve` (some $\mathbb Q$-variable change carries the Frey curve to $W \otimes \mathbb Q$), and a maximal ideal $\mathfrak m \ni P.p$ of $\overline{\mathbb Z}$, such that for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid N$, $\ell \neq P.p$, the coefficient $a_\ell(f)$ is an algebraic integer congruent mod $\mathfrak m$ to $a_\ell(W) = \ell + 1 - \#W_{/\mathbb F_\ell}$. `IsResiduallyModularOfLevel W p M` is the same condition for an arbitrary integral model $W$ and prime $p$, without the Frey data; `IsResiduallyModular W p` existentially quantifies over levels $M > 0$. `IsModularModelOfConductorLevel W` strengthens `IsModularModel` by requiring a level $N > 0$ divisible by every prime dividing the discriminant $\Delta_W$ of the chosen model (no squarefreeness or minimality), and the projection to `IsModularModel` is recorded. `ModRepIsIrreducible W n` is `GaloisRepIsIrreducible` for $W \otimes \mathbb Q$ over $\mathbb Q$ with $K$ the algebraic closure: the $n$-torsion of the point group is nontrivial and its only Galois-stable $\mathbb Z/n$-submodules are $\bot$ and $\top$. Finally, a normalised eigenform is nonzero, since $a_1 = 1$.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, `CongruenceSubgroup.Gamma0`, `qExpansion` and `integralClosure ℤ ℂ`; the notions of normalised eigenform, of a modular or residually modular integral Weierstrass model, and of irreducibility of the mod-$n$ Galois representation are the project's own, all phrased on a chosen integral model rather than on an isomorphism class.
--
--   **Where it is used.** These predicates carry the modularity input through the Frey–Serre–Ribet route: the assembly of modularity at $3$ and the lifting theorems produce `IsResiduallyModularOfLevel W 3 M`, the entry point of level lowering is [`FreyPackage.modularRepOfConductorLevel`](../thm.html#FreyPackage.modularRepOfConductorLevel), stating that the Frey package's representation arises from a squarefree level supported on the primes dividing $abc$, and `ModRepIsIrreducible` is the irreducibility hypothesis needed both for level lowering and for surjectivity onto $\mathrm{GL}_2(\mathbb F_3)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FLTPrelim_ModularRep.lean

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open WeierstrassCurve CuspForm

namespace FLTPrelim

lemma not_isUnit_natCast_integralClosure {p : ℕ} (hp : p.Prime) :
    ¬ IsUnit (p : integralClosure ℤ ℂ) := by
  intro h
  obtain ⟨u, hu⟩ := h

  set x : integralClosure ℤ ℂ := ((u⁻¹ : (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ) with hx
  have h1 : (p : integralClosure ℤ ℂ) * x = 1 := by
    rw [hx, ← hu]; exact u.mul_inv

  have h2 : (p : ℂ) * (x : ℂ) = 1 := by
    have := congrArg (fun z : integralClosure ℤ ℂ => (z : ℂ)) h1
    push_cast at this; simpa using this
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hxval : (x : ℂ) = (p : ℂ)⁻¹ := by field_simp; linear_combination h2
  have hint : IsIntegral ℤ ((p : ℂ)⁻¹) := by rw [← hxval]; exact x.2

  have hmap : (algebraMap ℚ ℂ) ((p : ℚ)⁻¹) = (p : ℂ)⁻¹ := by
    rw [eq_ratCast (algebraMap ℚ ℂ)]; push_cast; rfl
  rw [← hmap] at hint
  have hintQ : IsIntegral ℤ ((p : ℚ)⁻¹) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hint

  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintQ
  rw [eq_intCast] at hm
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmul : ((p * m : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    push_cast; rw [hm]; field_simp
  have hdvd : (p : ℤ) ∣ 1 := ⟨m, (Int.cast_injective hmul).symm⟩
  have hple : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have := hp.two_le; omega

lemma exists_maximalIdeal_natCast_prime_mem {p : ℕ} (hp : p.Prime) :
    ∃ 𝔪 : Ideal (integralClosure ℤ ℂ), 𝔪.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪 := by
  have hne : Ideal.span {(p : integralClosure ℤ ℂ)} ≠ ⊤ := fun htop =>
    not_isUnit_natCast_integralClosure hp (Ideal.span_singleton_eq_top.mp htop)
  obtain ⟨𝔪, h𝔪max, h𝔪le⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨𝔪, h𝔪max, h𝔪le (Ideal.subset_span rfl)⟩

end FLTPrelim

namespace FreyPackage

open FLTPrelim

def ModularRepOfLevel (P : FreyPackage) (N : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

end FreyPackage

namespace WeierstrassCurve

def IsResiduallyModularOfLevel (W : WeierstrassCurve ℤ) (p M : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ 𝔪.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def IsResiduallyModular (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ W.IsResiduallyModularOfLevel p M

def IsModularModelOfConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N

theorem IsModularModelOfConductorLevel.isModularModel {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfConductorLevel) : W.IsModularModel := by
  obtain ⟨N, hN, hmod, -⟩ := h
  exact ⟨N, hN, hmod⟩

def ModRepIsIrreducible (W : WeierstrassCurve ℤ) (n : ℕ) : Prop :=
  Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ
    (W.map (Int.castRingHom ℚ)) n

end WeierstrassCurve

namespace CuspForm

open ModularFormClass

open UpperHalfPlane in

theorem IsNormalizedEigenform.ne_zero {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) :
    f ≠ 0 := by
  rintro rfl
  have h0 : qCoeff (0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) 1 = 0 := by
    have hcoe : ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℍ → ℂ) = (0 : ℍ → ℂ) := rfl
    rw [qCoeff, hcoe, qExpansion_zero]
    simp
  exact zero_ne_one (h0 ▸ hf.qCoeff_one)

end CuspForm

end


