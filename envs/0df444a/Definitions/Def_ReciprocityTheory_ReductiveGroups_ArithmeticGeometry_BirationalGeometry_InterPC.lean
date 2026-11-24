-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:07.275262+00:00
-- url     : https://prove2.me/theorems/190ff12f-d7b1-446f-876e-4a34eb85097e
-- title:
--   Inter PC
-- statement:
--   Definitions and structural lemmas for Inter PC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterPC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def pC (P : Ideal (MRing ι)) : Ideal (MRingOver ℂ ι) :=
  Ideal.span (map (Int.castRingHom ℂ) '' (P : Set (MRing ι)))
def PCRadicalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → (pC P).IsRadical
def PCEquidimStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ Q ∈ (pC P).minimalPrimes,
      ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
def PCContractStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P
def PCMinContractStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ Q ∈ (pC P).minimalPrimes, Q.comap (map (Int.castRingHom ℂ)) = P
def jacMinors {s : ℕ} (G : Fin s → MRing ι) (c : ℕ) : Set (MRing ι) :=
  {d | ∃ (a : Fin c → Fin s) (b : Fin c → Σ k, ι k),
    d = Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))}
def JacNotInPStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∃ (s : ℕ) (G : Fin s → MRing ι), (∀ i, ∃ a, IsMultiHomog (G i) a) ∧
      Ideal.span (Set.range G) = P ∧
      ¬ Ideal.span (jacMinors G (Fintype.card (Σ k, ι k) - (e + Fintype.card K))) ≤ P
end ReciprocityTheory.ChartRestriction.G.Geo


