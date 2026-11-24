-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_ModelSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_ModelSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:46.23402+00:00
-- url     : https://prove2.me/theorems/57d73293-161e-4097-bc20-cdee3603dc0f
-- title:
--   Model St
-- statement:
--   Definitions and structural lemmas for Model St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/ModelSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AmpleSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Filter Asymptotics
def mConeMapOver (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) : MRingOver S ι →ₐ[S] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1
def mIdealOver (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) : Ideal (MRingOver S ι) :=
  RingHom.ker (mConeMapOver S y)
def chartRingOver (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra S Ω :=
  Algebra.adjoin S (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
def secOver (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : K → ℤ) : Submodule S Ω :=
  ⨅ (c : ∀ k, ι k) (_ : ∀ k, y ⟨k, c k⟩ ≠ 0),
    (Subalgebra.toSubmodule (chartRingOver S y c)).comap
      (LinearMap.mulRight S (∏ k, y ⟨k, c k⟩ ^ (-n k)))
def secMOver (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (d : K → ℕ) : Submodule S Ω :=
  Submodule.span S {s | ∃ g : MRingOver S ι, IsMultiHomog g d ∧ aeval y g = s}
def GeneratesOver (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
    [Algebra S Ω] {ι' : Type*} [Fintype ι'] (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ u : ι' → Ω, (∀ j, u j ∈ chartRingOver S y c) ∧
    ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = 1
def GlobalSectionsComparisonStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ φ : ↥(cechZc ι (quotPart S (mIdealOver S y)) n 0) →ₗ[S] Ω,
      Function.Injective φ ∧ LinearMap.range φ = secOver S y n ∧
      ∀ (z : ↥(cechZc ι (quotPart S (mIdealOver S y)) n 0)) (d : K → ℕ) (g : MRingOver S ι),
        (fun k => (d k : ℤ)) = n → IsMultiHomog g d →
        (∀ I, (z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0) I =
          LocalizedModule.mk (Ideal.Quotient.mk _ g) 1) →
        φ z = aeval y g
def IdealModelStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (V : Ideal (MRingOver S ι)) [V.IsPrime],
    IsMultiHomogIdeal V → IsRelevant V →
    V = mIdealOver S (fun p => algebraMap (MRingOver S ι ⧸ V) (FractionRing (MRingOver S ι ⧸ V))
      (Ideal.Quotient.mk V (X p)))
def SecEqOverStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    IsNoetherianRing S → (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ τ₀ : ℕ, ∀ τ : ℕ, τ₀ ≤ τ → secOver S y (fun k => ((τ * a k : ℕ) : ℤ)) = secMOver S y (fun k => τ * a k)
def HilbStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (I : IFamily F ι) (e : ℕ) (γ : K → ℤ) (a : ℕ)
    (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    IsFieldIntersection I → IsProjVarF (mIdealOver F y) e → (∀ j, x' j ∈ secOver F y γ) →
    GeneratesOver F y γ x' → 1 ≤ a →
    0 < I (mIdealOver F y) e (fun _ => γ + fun _ => (a : ℤ)) ∧
    (fun n : ℕ => (Module.finrank F (secOver F y (n • (γ + fun _ => (a : ℤ)))) : ℝ) -
        (I (mIdealOver F y) e (fun _ => γ + fun _ => (a : ℤ)) : ℝ) * (n : ℝ) ^ e / (e.factorial : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((e : ℤ) - 1)) ∧
    ∀ ε : K → ℤ, ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (Module.finrank F (secOver F y (n • (γ + fun _ => (a : ℤ)) + ε)) : ℝ) ≤
        (I (mIdealOver F y) e (fun _ => γ + fun _ => (a : ℤ)) : ℝ) * (n : ℝ) ^ e / (e.factorial : ℝ) +
          C * (n : ℝ) ^ ((e : ℤ) - 1)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


