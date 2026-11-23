-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
-- name    : Formalism_PieriBlockIdeals_StatementLA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:14.807607+00:00
-- url     : https://prove2.me/theorems/53397d03-6059-4b50-9bc7-adfcb233b07b
-- title:
--   Statement LA
-- statement:
--   Definitions and structural lemmas for Statement LA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementLA.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RankGapBounds_CloudMinFalse
import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementJ
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
namespace Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
def lamU (r n : ℕ) (ν : Fin n → ℕ) : Fin r → ℤ :=
  fun a => (rowNu (r := r) ν a : ℤ) + ((r : ℤ) - 1 - (a.val : ℤ))
def InclZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) : Prop :=
  ∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ dualWeyl ℤ r n ν, ((m * l ^ e : ℕ) : ℤ) • x ∈ weyl ℤ r n hn ν
def LemmaAZ : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)
def LemmaAR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ l : ℕ, l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    ∀ x ∈ dualWeyl R r n ν, (l : R) ^ Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l • x ∈ weyl R r n hn ν
def LemmaAROfZ : Prop := LemmaAZ → LemmaAR
def LemmaAZOfR : Prop := LemmaAR → LemmaAZ
def InclZIffR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (l : ℕ), l.Prime →
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    (∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ),
      InclZ r n hn ν l e ↔ ∀ x ∈ dualWeyl R r n ν, (l : R) ^ e • x ∈ weyl R r n hn ν
def exZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l : ℕ) : ℕ := sInf {e : ℕ | InclZ r n hn ν l e}
def MaxValEq : Prop := ∀ l n : ℕ, Formalism.CohomologicalDescent.maxVal l n = Formalism.RankGapBounds.JumpSetsAlt.maxVal l n
def LamUStrictAnti : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), Antitone ν → StrictAnti (lamU r n ν)
def InclZMono : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e e' : ℕ), e ≤ e' →
    InclZ r n hn ν l e → InclZ r n hn ν l e'
def ExZSpec : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (exZ r n hn ν l)
def ExactExponentRankTwo : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℕ) (l : ℕ),
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 n ν) l =
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l (rowNu (r := 2) ν 0 - rowNu (r := 2) ν 1)
def binForm (R : Type) [CommRing R] (d : ℕ) :
    (Fin (d + 1) → R) →ₗ[R] MvPolynomial (Fin 2 × Fin 1) R :=
  ∑ i : Fin (d + 1), (LinearMap.proj i : (Fin (d + 1) → R) →ₗ[R] R).smulRight
    ((X ((0 : Fin 2), (0 : Fin 1)) : MvPolynomial (Fin 2 × Fin 1) R) ^ (d - i.val) *
      X ((1 : Fin 2), (0 : Fin 1)) ^ i.val)
def BinFormInj : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ), Function.Injective (binForm R d)
def DualWeylBinaryForms : Prop :=
  ∀ (R : Type) [CommRing R] (ν : Fin 1 → ℕ),
    dualWeyl R 2 1 ν = LinearMap.range (binForm R (ν 0))
def WeylRankTwoOneColumnImage : Prop :=
  ∀ (R : Type) [CommRing R] (hn : 1 ≤ 2) (ν : Fin 1 → ℕ),
    weyl R 2 1 hn ν =
      (LinearMap.range (Formalism.CohomologicalDescent.diagBinom R (ν 0))).map (binForm R (ν 0))
def LatticeInclusionTrivialWeight : Prop :=
  ∀ (r : ℕ) (hn : 0 ≤ r) (ν : Fin 0 → ℕ) (l : ℕ), l.Prime →
    InclZ r 0 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r 0 ν) l)
def LatticeInclusionRankOne : Prop :=
  ∀ (n : ℕ) (hn : n ≤ 1) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 1 n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 1 n ν) l)
def LemmaAZ_r2n1 : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    InclZ 2 1 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l)
def LemmaAZ_r2n2 : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 2 2 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l)
def LatticeInclusionRankLeTwo : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r), r ≤ 2 → ∀ ν : Fin n → ℕ, Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)
def LemmaAR_r2n1 : Prop :=
  ∀ (R : Type) [CommRing R] (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    ∀ x ∈ dualWeyl R 2 1 ν, (l : R) ^ Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l • x ∈ weyl R 2 1 hn ν
def SharpInclusionRankTwoOneColumn : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l e : ℕ), l.Prime →
    (InclZ 2 1 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e)
def ExZR2N1 : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    exZ 2 1 hn ν l = Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l
def SharpInclusionRankTwoTwoColumns : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l e : ℕ, l.Prime →
    (InclZ 2 2 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e)
def ExZR2N2 : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    exZ 2 2 hn ν l = Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l
def JointExZ : Prop :=
  LemmaAZ → ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    exZ r n hn ν l ≤ Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l
def nuOf {r : ℕ} (U : Fin r → ℤ) : Fin r → ℕ :=
  fun a => (U a - ((r : ℤ) - 1 - (a.val : ℤ))).toNat
def NuOfSpec : Prop :=
  ∀ (r : ℕ) (U : Fin r → ℤ), StrictAnti U → (∀ a, 0 ≤ U a) →
    Antitone (nuOf U) ∧ lamU r r (nuOf U) = U
def ExLeExact {ι : Type} {D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι} (W : Formalism.CohomologicalDescent.Joint.Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ, D.ex τ l ≤ exZ D.Nr D.Nr le_rfl (nuOf (W.U τ)) l
def JointLemmaAFull : Prop :=
  ∀ (ι : Type) (D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι) (W : Formalism.CohomologicalDescent.Joint.Weights D),
    LemmaAZ → ExLeExact W → Formalism.CohomologicalDescent.Joint.LemmaAFull W
def ExLeExactParts {ι : Type} {D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι} (W : Formalism.CohomologicalDescent.Joint.Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ ∈ D.T2,
    D.ecl τ l ≤ exZ D.k D.k le_rfl (nuOf (W.cloud τ)) l ∧
    D.erest τ l ≤ exZ (D.Nr - D.k) (D.Nr - D.k) le_rfl (nuOf (W.rest τ)) l
def JointLemmaAInputs : Prop :=
  ∀ (ι : Type) (D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι) (W : Formalism.CohomologicalDescent.Joint.Weights D),
    LemmaAZ → ExLeExact W → ExLeExactParts W → Formalism.CohomologicalDescent.Joint.LemmaAInputs W
def JointLatIncl : Prop :=
  LemmaAR → ∀ (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
    Antitone ν → ∀ l : ℕ, l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    Formalism.RankGapBounds.FormsTensorLocalization.LatIncl (l : R) ((weyl R r n hn ν).comap (dualWeyl R r n ν).subtype)
      (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)
end Formalism.CohomologicalDescent.LA


