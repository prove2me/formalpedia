-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:12.950199+00:00
-- url     : https://prove2.me/theorems/01916010-67bf-4505-b27f-0de8a5c0bc30
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial TensorProduct
noncomputable section
universe u v w
def CechExact.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M' M M'' : Type v)
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M''] [Module (Poly S N) M''] [Module S M''] [IsScalarTower S (Poly S N) M'']
    (𝓜' : GradedPMod S N M') (𝓜 : GradedPMod S N M) (𝓜'' : GradedPMod S N M'')
    (f : GradedHom 𝓜' 𝓜) (g : GradedHom 𝓜 𝓜''),
    Function.Injective f.toLin → Function.Surjective g.toLin → Function.Exact f.toLin g.toLin →
    ∀ c : ℤ, Function.Injective (cohomMap f 0 c) ∧
      ∀ i : ℕ, Function.Exact (cohomMap f i c) (cohomMap g i c) ∧
        ∃ δ : cohom 𝓜'' i c →ₗ[S] cohom 𝓜' (i + 1) c,
          Function.Exact (cohomMap g i c) δ ∧ Function.Exact δ (cohomMap f (i + 1) c)
def CechTop.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M) (i : ℕ) (c : ℤ), N < i → Subsingleton (cohom 𝓜 i c)
def CechFlat.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (S' : Type u) [CommRing S']
    [Algebra S S'] [Module.Flat S S'] (M M' : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M'] [IsScalarTower S' (Poly S' N) M']
    [Module S M'] [IsScalarTower S S' M']
    (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M') (f : M →ₗ[S] M'),
    IsBaseChange S' f → (∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m) →
    (∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c) →
    ∀ (i : ℕ) (c : ℤ), Nonempty (cohom 𝓜' i c ≃ₗ[S'] S' ⊗[S] cohom 𝓜 i c)
def Extension.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (F : SubFamily S x E), (∀ I, (F.sub I).FG) →
    ∃ M : FinGradedSub (S := S) (x := x) E, (∀ c, M.piece c ≤ F.gam c) ∧ ∀ I, M.tilde 0 I = F.sub I
def Generated.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x),
    ∃ c₀ : ℤ, ∀ c ≥ c₀, (Q.twist (twistSys S x c)).Generated
def GeneratedAmple.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x), AmpleData S x H → ∀ Q : LineBundle S x,
    ∃ c₀ : ℕ, ∀ c ≥ c₀, (Q.twist (H.pow c)).Generated
def PrimeFiltration.Exists.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M → (∀ p ∈ primeOf (S := S) x, ∀ m : M, p • m = 0) →
    Nonempty (PrimeFilt 𝓜) ∧
      ∀ (F : PrimeFilt 𝓜) (pp : Ideal (Poly S N)) [pp.IsPrime],
        pp ∈ (Module.annihilator (Poly S N) M).minimalPrimes →
        (((Finset.univ.filter fun k => F.prime k = pp).card : ℕ) : ℕ∞) =
          Module.length (Localization.AtPrime pp) (LocalizedModule pp.primeCompl M)
def PrimeFiltration.Irrelevant.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → (∀ i, (X i : Poly S N) ∈ pp) →
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∀ f : Poly S N, f.IsHomogeneous c → f ∈ pp
def PrimeFiltration.Point.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → primeOf (S := S) x ≤ pp →
    ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly S N) ∉ pp →
    (chartPrime pp hj).IsPrime ∧
      ∀ (K' : Type w) [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K'),
        RingHom.ker ψ = chartPrime pp hj → primeOf (S := S) (fun i => ψ (ratio hj i)) = pp
def PrimeFiltration.Restrict.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → primeOf (S := S) x ≤ pp →
    ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly S N) ∉ pp →
    ∀ (K' : Type w) [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K'),
      RingHom.ker ψ = chartPrime pp hj →
      ∀ (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0) (Q : LineBundle S x),
        ∃ (Q' : LineBundle S (fun i => ψ (ratio hj i))) (r : Ω → K'),
          ∀ I : Chart (fun i => ψ (ratio hj i)),
            (∀ q ∈ Q.sub (liftChart hxy I), r q ∈ Q'.sub I) ∧
            (∀ q ∈ Q.sub (liftChart hxy I), ∀ q' ∈ Q.sub (liftChart hxy I), r (q + q') = r q + r q') ∧
            (∀ q ∈ Q.sub (liftChart hxy I), ∀ (f s : Poly S N) (e : ℕ), s ∈ monos I.1 →
              f.IsHomogeneous e → s.IsHomogeneous e →
              r (aeval x f / aeval x s * q) =
                aeval (fun i => ψ (ratio hj i)) f / aeval (fun i => ψ (ratio hj i)) s * r q) ∧
            Submodule.span (chartRing S (fun i => ψ (ratio hj i)) I) (r '' Q.sub (liftChart hxy I)) =
              Q'.sub I
def PrimeFiltration.Statement : Prop :=
  PrimeFiltration.Exists.Statement.{u, v, w} ∧ PrimeFiltration.Irrelevant.Statement.{u} ∧
    PrimeFiltration.Point.Statement.{u, w} ∧ PrimeFiltration.Restrict.Statement.{u, w}
def SerrePoly.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ),
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (cohom (polyGraded S N) i c)) ∧
    ∀ c : ℤ, 0 ≤ c → (∀ i, 1 ≤ i → Subsingleton (cohom (polyGraded S N) i c)) ∧
      Function.Bijective (toH0 (polyGraded S N) c)
def SerreFree.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M) (r : ℕ) (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ),
    (∀ j, b j ∈ 𝓜.piece (d j)) →
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (cohom 𝓜 i c)) ∧
    ∀ c : ℤ, (∀ j, d j ≤ c) → (∀ i, 1 ≤ i → Subsingleton (cohom 𝓜 i c)) ∧
      Function.Bijective (toH0 𝓜 c)
def SerreFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∀ (i : ℕ) (c : ℤ), Module.Finite S (cohom 𝓜 i c)
def SerreVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ i, 1 ≤ i → ∀ c ≥ c₀, Subsingleton (cohom 𝓜 i c)
def SerreOnto.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ c ≥ c₀, Function.Surjective (toH0 𝓜 c)
def SerreTail.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M → ∀ c₁ : ℤ,
    ∃ t : Finset (Cech.Cochain (locSys S N M) 0), (∀ z ∈ t, z ∈ H0tail 𝓜 c₁) ∧
      H0tail 𝓜 c₁ ≤ (Submodule.span (Poly S N) (t : Set (Cech.Cochain (locSys S N M) 0))).restrictScalars S
def TwistFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (G B : LineBundle S x) (r : ℕ) (η : Fin (r + 1) → Ω), x ≠ 0 →
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ (n : ℕ) (deg : Fin n → ℕ) (gen : Fin n → Ω),
      (∀ k, gen k ∈ (G.twist (B.pow (deg k))).secs) ∧
      ∀ b : ℕ, (G.twist (B.pow b)).secs ≤ Submodule.span S {z | ∃ (k : Fin n)
        (f : MvPolynomial (Fin (r + 1)) S) (e : ℕ), f.IsHomogeneous e ∧ e + deg k = b ∧
        z = aeval η f * gen k}
def TwistVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (G B : LineBundle S x) (r : ℕ) (η : Fin (r + 1) → Ω),
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c →
      Subsingleton (((G.twist (B.pow b)).twist (twistSys S x c)).H 1)
section Hypotheses
variable (k : Type u) [Field k] (N : ℕ)
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


