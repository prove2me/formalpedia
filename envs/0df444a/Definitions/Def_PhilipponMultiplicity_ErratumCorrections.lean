-- Prove2me | Definitions.Def_PhilipponMultiplicity_ErratumCorrections
-- name    : PhilipponMultiplicity_ErratumCorrections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-10T15:26:45.130499+00:00
-- url     : https://prove2.me/theorems/2f328215-6573-42e2-b9a4-c47a866e4f56
-- title:
--   Philippon erratum — connectedness, addition degree, corrected statements
-- statement:
--   This bundle extends the existing embedded-group definitions without changing their coordinate rings, topology, Hilbert functions, degree forms, tangent codimension, or contact order.
--
--   A map has a degree-conditioned regular presentation if, at every source point and for each target projective factor, an open neighborhood carries a nonvanishing tuple of multihomogeneous coordinate polynomials representing the map, whose common source multidegree satisfies the specified predicate. Addition has first-input degree at most $c$ when this presentation applies to the existing pair embedding and addition map, with degree in the first coordinate block at most $c$; the second block has no bound. An ambient group is connected when its whole point set is connected in its existing induced Zariski topology.
--
--   The bundle also defines two propositions, without asserting or proving them: the corrected forward estimate for connected ambient groups with one shift shared by all sampled cosets, and the converse for connected ambient groups whose factors have first-input addition degree at most two. These definitions provide the exact statements for the separately published open targets.
-- source:
--   User-authorized corrected formulation of Philippon, Errata et addenda, 1987, printed p. 398, https://numdam.org/item/10.24033/bsmf.2084.pdf; addition-degree condition: Philippon 1986, section 4.1, printed p. 372, https://numdam.org/item/10.24033/bsmf.2060.pdf. The forward common-shift conclusion is an explicit correction, not an exact transcription.

import Definitions.Def_PhilipponMultiplicity_SourceStatements

/-! Explicit geometric predicates and corrected erratum propositions.
The original published definitions are imported unchanged. No estimates are
assumed or proved here; the final two declarations are proposition definitions. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

namespace MultiProjectiveSpace
def IsRegularAlongWithDegreeCondition (M Q : MultiProjectiveSpace K) {X : Type u}
    (e : X → M.Point) (f : X → Q.Point)
    (allowedDegree : (M.FactorIndex → ℕ) → Prop) : Prop :=
  ∀ x : X, ∀ b : Q.FactorIndex,
    ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ e x ∈ U ∧
      ∃ D : M.FactorIndex → ℕ, allowedDegree D ∧
      ∃ P : Fin (Q.ambientDimension b + 1) → M.CoordinateRing,
        (∀ j, M.IsHomogeneous (P j) D) ∧
        ∀ y : X, e y ∈ U →
          ∃ h : (fun j => M.eval (P j) (e y)) ≠ 0,
            Projectivization.mk K (fun j => M.eval (P j) (e y)) h = f y b
end MultiProjectiveSpace

namespace EmbeddedCommutativeGroup
def HasAdditionDegreeAtMost (E : EmbeddedCommutativeGroup K) (c : ℕ) : Prop :=
  MultiProjectiveSpace.IsRegularAlongWithDegreeCondition
    (projectiveSquare K E.ambientDimension) (projectiveSpace K E.ambientDimension)
    (fun xy : E.Point × E.Point => fun i => if i.val = 0 then xy.1.val else xy.2.val)
    (fun xy : E.Point × E.Point => fun _ => (xy.1 + xy.2).val)
    (fun D => D (0 : Fin 2) ≤ c)
end EmbeddedCommutativeGroup

namespace EmbeddedGroupProduct
def IsConnected (G : EmbeddedGroupProduct K) : Prop :=
  @_root_.IsConnected _ G.zariskiTopology (Set.univ : Set G.Point)
end EmbeddedGroupProduct

namespace CorrectedErratumStatements
/-- Corrected forward variant with one common shift; not a literal transcription. -/
def addendum_strengthened_vanishing : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K),
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), G.IsConnected → 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∃ v : G.Point,
            ∀ g ∈ sample,
              translate (g + v) H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i))

/-- Converse with connected ambient group and first-input addition degree at most two. -/
def addendum_converse : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (hadd : ∀ i : G.FactorIndex, (G.factor i).HasAdditionDegreeAtMost 2)
    (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D),
    ∃ P : G.CoordinateRing,
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P D ∧
      (∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) ∧
      (∃ x : G.Point, x ∉ zeroLocusOnGroup G P)
end CorrectedErratumStatements
end PhilipponMultiplicity


