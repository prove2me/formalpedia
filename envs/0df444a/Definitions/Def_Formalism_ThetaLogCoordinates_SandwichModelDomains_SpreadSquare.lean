-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
-- name    : Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:28.397523+00:00
-- url     : https://prove2.me/theorems/055576c1-fca3-4150-86fa-8d91fafaa600
-- title:
--   Spread Square
-- statement:
--   Definitions and structural lemmas for Spread Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SpreadSquare.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
def Spread (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ) : Prop :=
  ∀ f ∈ dualWeyl R r n ν, ∀ g ∈ dualWeyl R r n ν, ∀ m ∈ f.support, ∀ m' ∈ g.support, ∀ a : Fin r,
    rowDeg m a ≤ rowDeg m' a + l
def SpreadTop : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ), (∀ t, ν t ≤ l) → Spread R r n ν l
def SpreadSquare : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ν : Fin n → ℕ) (l : ℕ), (∀ s t, ν s ≤ ν t + l) → Spread R n n ν l
def vecL {n : ℕ} (ν : Fin n → ℕ) : Letters n := ⟨fun _ => true, ν⟩
def swp (R : Type) [CommRing R] (r n : ℕ) :
    MvPolynomial (Fin r × Fin n) R ≃ₐ[R] MvPolynomial (Fin n × Fin r) R :=
  renameEquiv R (Equiv.prodComm (Fin r) (Fin n))
def GR (p : ℕ) [Fact p.Prime] (r : ℕ) {n : ℕ} (ν : Fin n → ℕ) :
    GlW ℚ_[p] (MvPolynomial (Fin n × Fin r) ℚ_[p]) r :=
  GAe p (vecL ν) n (OrderIso.refl (Fin r)).toOrderEmbedding
def RowGlOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    swp ℚ_[p] r n (rowDiv ℚ_[p] a b 1 f) = (GR p r ν).E a b (swp ℚ_[p] r n f)
def RowGlDiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (a b : Fin r), a ≠ b →
    ∀ (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
      swp ℚ_[p] r n (rowDiv ℚ_[p] a b k f) =
        ((k.factorial : ℚ_[p]))⁻¹ • (((GR p r ν).E a b) ^ k) (swp ℚ_[p] r n f)
def SwpWt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (μ : Fin r → ℤ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    (GR p r ν).IsWt μ (swp ℚ_[p] r n f) ↔ ∀ m ∈ f.support, ∀ a, (rowDeg m a : ℤ) = μ a
def SwpPol : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    IsWeightedHomogeneous (colW r n) f ν → swp ℚ_[p] r n f ∈ Pol p r (vecL ν)
def SwpInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    swp ℚ_[p] r n f ∈ IntPol p (Fin n × Fin r) ↔
      ∃ f0 : MvPolynomial (Fin r × Fin n) ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) f0 = f
def CoreQp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, Spread ℚ_[p] r n ν l →
    ∀ x ∈ dualWeyl ℤ_[p] r n ν, ((p : ℤ_[p]) ^ sExp p r l) • x ∈ weyl ℤ_[p] r n hn ν
def DescentZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ e : ℕ,
    (∀ x ∈ dualWeyl ℤ_[p] r n ν, ((p : ℤ_[p]) ^ e) • x ∈ weyl ℤ_[p] r n hn ν) →
    ∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (c * (p : ℤ) ^ e) • f ∈ weyl ℤ r n hn ν
def AscentDomain : Prop :=
  ∀ (p : ℕ) (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ),
    (∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (c * (p : ℤ) ^ e) • f ∈ weyl ℤ r n hn ν) →
    ∀ (O : Type) [CommRing O] [IsDomain O], PrimeToPUnits p O →
      ∀ x ∈ dualWeyl O r n ν, ((p : O) ^ e) • x ∈ weyl O r n hn ν
end Formalism.InvariantFactorPaths.INST


