-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_localLaws
-- name    : LiuHelsenDesigns_OneD_localLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:57.04339+00:00
-- url     : https://prove2.me/theorems/6b92b536-8a3f-4b4d-a75f-bfc06a2f2d7a
-- title:
--   Finite local-generator laws and the CPZPC convolution
-- statement:
--   The Clifford step is uniform on the actual finite set of generators with identity adjoined. The permutation step is uniform on its actual finite set. All samples in the convolution are independent.
--
--   $$\widetilde\nu=\nu_{Cl}^{*r_C}*\nu_P^{*r_P}*\delta_Z*\nu_P^{*r_P}*\nu_{Cl}^{*r_C}.$$
--
--   The central gate is Pauli Z on the first physical wire. Implementation predicates compare evaluated circuit matrices with the actual group elements, without assuming expansion. For a representation with no invariant vectors, its invariant projector is zero; the Clifford norm therefore averages the represented generators directly.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), pp.28–30, Eq.(163), Lemmas 11–12, Eqs.(165)–(173). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_groups
import Definitions.Def_LiuHelsenDesigns_OneD_permutations

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise ENNReal

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.decEq Classical.propDecidable

def permutationCircuit (C : Circuit) : Prop :=
  ∀ layer ∈ C, ∀ o ∈ layer, o.1 = 2 ∨ o.1 = 4 ∨ o.1 = 8

def clLaw {n : ℕ} (S : Finset (Cl n)) : Measure (Mat n) :=
  ((S.card : ℝ≥0∞)⁻¹) • ∑ U ∈ S, Measure.dirac (((U.val : Unitary n) : Mat n))
def permLaw {n : ℕ} (S : Finset (Equiv.Perm (Basis n))) : Measure (Mat n) :=
  ((S.card : ℝ≥0∞)⁻¹) • ∑ p ∈ S, Measure.dirac (DepthOneQExp.permToMatrix p)
def multiplyLaws {n : ℕ} (ν μ : Measure (Mat n)) : Measure (Mat n) :=
  (ν.prod μ).map (fun p => p.1*p.2)

def cpzpc (n : ℕ) (S : Finset (Cl n)) (P : Finset (Equiv.Perm (Basis n)))
    (rC rP : ℕ) : Measure (Mat n) :=
  multiplyLaws (powerLaw (clLaw (insert 1 S)) rC)
    (multiplyLaws (powerLaw (permLaw P) rP)
      (multiplyLaws (Measure.dirac (circuitMatrix n [[(3,[0])]]))
        (multiplyLaws (powerLaw (permLaw P) rP) (powerLaw (clLaw (insert 1 S)) rC))))

def ImplementsClSet {n : ℕ} (cs : List Circuit) (S : Finset (Cl n)) : Prop :=
  (∀ C ∈ cs, ∃ U ∈ S, RepresentsCl n C U) ∧
    ∀ U ∈ S, ∃ C ∈ cs, RepresentsCl n C U
def ImplementsPermSet {n : ℕ} (cs : List Circuit) (S : Finset (Equiv.Perm (Basis n))) : Prop :=
  (∀ C ∈ cs, LegalCircuit n C ∧ permutationCircuit C ∧
    ∃ p ∈ S, circuitMatrix n C = DepthOneQExp.permToMatrix p) ∧
    ∀ p ∈ S, ∃ C ∈ cs, circuitMatrix n C = DepthOneQExp.permToMatrix p

def permutationEssential {n : ℕ} (S : Finset (Equiv.Perm (Basis n))) (k : ℕ) : ℝ :=
  matrixNorm (finiteAverage S (fun p => tensorPower (DepthOneQExp.permToMatrix p) k) -
    permutationAverage (Basis n) k true)

def NoInvariant {G : Type} [Group G] {d : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  ∀ v : EuclideanSpace ℂ (Fin d),
    (∀ g : G, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ g : Matrix (Fin d) (Fin d) ℂ) v = v) → v = 0

def clRepresentationNorm {n d : ℕ} (S : Finset (Cl n))
    (ρ : Cl n →* Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  matrixNorm (finiteAverage (insert 1 S) (fun g => (ρ g : Matrix (Fin d) (Fin d) ℂ)))

end LiuHelsenDesigns.OneD


