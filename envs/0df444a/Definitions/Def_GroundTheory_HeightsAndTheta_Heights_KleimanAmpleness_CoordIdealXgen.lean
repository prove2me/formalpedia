-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealXgen
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealXgen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:44.889708+00:00
-- url     : https://prove2.me/theorems/88c311dc-488f-4052-a330-b4753bf3d865
-- title:
--   Coord Ideal Xgen
-- statement:
--   Definitions and structural lemmas for Coord Ideal Xgen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealXgen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def CechExact.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [Module (Poly S N) M₁] [Module S M₁] [IsScalarTower S (Poly S N) M₁]
    [AddCommGroup M₂] [Module (Poly S N) M₂] [Module S M₂] [IsScalarTower S (Poly S N) M₂]
    [AddCommGroup M₃] [Module (Poly S N) M₃] [Module S M₃] [IsScalarTower S (Poly S N) M₃]
    (G₁ : GradedMod S N M₁) (G₂ : GradedMod S N M₂) (G₃ : GradedMod S N M₃)
    (f : M₁ →ₗ[Poly S N] M₂) (g : M₂ →ₗ[Poly S N] M₃)
    (hf : IsGradedHom S N G₁ G₂ f) (hg : IsGradedHom S N G₂ G₃ g),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    ∀ c : ℤ,
      (∀ i : ℕ,
        (∀ v ∈ cechC (gradedSys S N M₁ G₁ c) i, gradedCmap S N hf c v = 0 → v = 0) ∧
        (∀ v ∈ cechC (gradedSys S N M₂ G₂ c) i, gradedCmap S N hg c v = 0 →
          ∃ u ∈ cechC (gradedSys S N M₁ G₁ c) i, gradedCmap S N hf c u = v) ∧
        (cechC (gradedSys S N M₂ G₂ c) i).map (gradedCmap S N hg c) = cechC (gradedSys S N M₃ G₃ c) i) ∧
      Function.Injective (gradedHmap S N hf 0 c) ∧
      ∃ δ : ∀ i, gradedH S N M₃ G₃ i c →ₗ[S] gradedH S N M₁ G₁ (i + 1) c,
        ∀ i, Function.Exact (gradedHmap S N hf i c) (gradedHmap S N hg i c) ∧
          Function.Exact (gradedHmap S N hg i c) (δ i) ∧
          Function.Exact (δ i) (gradedHmap S N hf (i + 1) c)
def CechTop.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M) (i : ℕ), N < i → ∀ c : ℤ, Subsingleton (gradedH S N M G i c)
def CechFlat.Statement : Prop :=
  ∀ (S S' : Type) [CommRing S] [IsNoetherianRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S'] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M)
    (M' : Type) [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M'] [IsScalarTower S' (Poly S' N) M']
    [Module S M'] [IsScalarTower S S' M']
    (G' : GradedMod S' N M') (φ : M →ₗ[S] M'),
    IsBaseChange S' φ →
    (∀ (i : Fin (N + 1)) (m : M), φ ((X i : Poly S N) • m) = (X i : Poly S' N) • φ m) →
    (∀ c, ∀ m ∈ G.piece c, φ m ∈ G'.piece c) →
    ∀ (i : ℕ) (c : ℤ), Nonempty (gradedH S' N M' G' i c ≃ₗ[S'] TensorProduct S S' (gradedH S N M G i c))
def Extension.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S E x), F.IsFinite →
    ∃ (n : ℕ) (c : Fin n → ℤ) (e : Fin n → E), IsExtensionOf S x F.mods c e
def Generated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (Q : LineBundle (S := S) x),
    ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IsGenerated S x (twistA S x Q.mods c)
def GeneratedAmple.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (H : LineBundle (S := S) x), AmpleData S x H.mods →
    ∀ Q : LineBundle (S := S) x, ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → IsGenerated S x (lmul S Q.mods (lpow S H.mods c))
def PrimeFiltration.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω),
    (∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
      (G : GradedMod S N M), Module.Finite (Poly S N) M → (∀ f ∈ coordIdeal S x, ∀ m : M, f • m = 0) →
      ∃ F : PrimeFiltration S N G,
        (∀ (pp : Ideal (Poly S N)) (hpp : pp ∈ (Module.annihilator (Poly S N) M).minimalPrimes),
          haveI : pp.IsPrime := hpp.1.1
          ((PrimeFiltration.count S N F pp : ℕ) : ℕ∞) =
            Module.length (Localization.AtPrime pp) (LocalizedModule pp.primeCompl M)) ∧
        (∀ k, (∀ i, (X i : Poly S N) ∈ F.prime k) →
          ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → ∀ f ∈ polyPiece S N c, f ∈ F.prime k)) ∧
    (∀ (pp : Ideal (Poly S N)) [pp.IsPrime], IsHomogIdeal S pp → coordIdeal S x ≤ pp →
      (∃ j, (X j : Poly S N) ∉ pp) →
      coordIdeal S (ptCoord pp) = pp ∧
      ∀ Q : LineBundle (S := S) x, ∃ QW : Fin (N + 1) → Submodule S (FractionRing (Poly S N ⧸ pp)),
        IsRestrictionOf x pp Q QW ∧
        ∀ (n : ℕ) (c : ℤ), Nonempty (cechH (quotTwistSys S x pp Q.mods c) n ≃ₗ[S]
          famH S (ptCoord pp) (twistA S (ptCoord pp) QW c) n))
def SerrePoly.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ),
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (gradedH S N (Poly S N) (polyGraded S N) i c)) ∧
    ∀ c : ℤ, 0 ≤ c →
      (∀ i : ℕ, 1 ≤ i → Subsingleton (gradedH S N (Poly S N) (polyGraded S N) i c)) ∧
      (∀ m ∈ polyPiece S N c, unitCochain S N (Poly S N) m ∈ gradedZ S N (Poly S N) (polyGraded S N) 0 c) ∧
      (∀ z ∈ gradedZ S N (Poly S N) (polyGraded S N) 0 c,
        ∃! m, m ∈ polyPiece S N c ∧ unitCochain S N (Poly S N) m = z)
def SerreFree.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M) (r : ℕ) (d : Fin r → ℤ) (b : Module.Basis (Fin r) (Poly S N) M),
    (∀ j, b j ∈ G.piece (d j)) →
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (gradedH S N M G i c)) ∧
    ∀ c : ℤ, (∀ j, d j ≤ c) →
      (∀ i : ℕ, 1 ≤ i → Subsingleton (gradedH S N M G i c)) ∧
      (∀ m ∈ G.piece c, unitCochain S N M m ∈ gradedZ S N M G 0 c) ∧
      (∀ z ∈ gradedZ S N M G 0 c, ∃! m, m ∈ G.piece c ∧ unitCochain S N M m = z)
def SerreFinite.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∀ (i : ℕ) (c : ℤ), Module.Finite S (gradedH S N M G i c)
def SerreVanish.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ (i : ℕ), 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH S N M G i c)
def SerreOnto.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → ∀ z ∈ gradedZ S N M G 0 c, ∃ m ∈ G.piece c, unitCochain S N M m = z
def SerreTail.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∀ c₁ : ℤ, ∃ (n : ℕ) (e : Fin n → ℤ) (z : Fin n → ∀ I, LocM S N M I),
      (∀ k, c₁ ≤ e k ∧ z k ∈ gradedZ S N M G 0 (e k)) ∧
      ∀ c : ℤ, c₁ ≤ c → ∀ z' ∈ gradedZ S N M G 0 c,
        z' ∈ ⨆ k, Submodule.span S ((fun f : Poly S N => f • z k) '' (polyPiece S N (c - e k) : Set (Poly S N)))
def TwistFinite.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (G B : LineBundle (S := S) x) (r : ℕ) (η : Fin (r + 1) → Ω),
    IsGeneratedBy S x B.mods η →
    ∃ (n : ℕ) (bk : Fin n → ℕ) (s : Fin n → Ω),
      (∀ k, s k ∈ secs S x (lmul S G.mods (lpow S B.mods (bk k)))) ∧
      ∀ b : ℕ, secs S x (lmul S G.mods (lpow S B.mods b)) =
        ⨆ k, Submodule.span S (Set.image2 (· * ·) (secZ S η ((b : ℤ) - bk k) : Set Ω) {s k})
def TwistVanish.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (G B : LineBundle (S := S) x) (r : ℕ) (η : Fin (r + 1) → Ω),
    IsGeneratedBy S x B.mods η →
    ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c → Subsingleton (famH S x (sumGBA S x G B b c) 1)
section Inhabitants
variable (k : Type) [Field k]
noncomputable def xgen (N : ℕ) : Fin (N + 1) → FractionRing (Poly k N) :=
  fun i => algebraMap (Poly k N) (FractionRing (Poly k N)) (X i)
noncomputable def GeneratedAmple.hyps : AmpleData k (lineX k) (bundleA k (lineX k)).mods := ampleA (lineX k)
noncomputable def PrimeFiltration.example : PrimeFiltration k 1 (polyGraded k 1) := polyFiltration k 1
end Inhabitants
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman


