-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_RoundingData
-- name    : BeyondConvexity_APTAS_RoundingData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:16:28.897064+00:00
-- url     : https://prove2.me/theorems/8e6e300e-a230-453a-abb9-961029b0e894
-- title:
--   Labeled containment groups and rounded supplies
-- statement:
--   Representative-rounding output consists of selected occurrence labels, a finite list of containment groups with level indices and chosen maximum labels, and a rational packing of the selected objects. The correctness relation is parameterized by a group bound $K$, loss $\eta$, and additive allowance $\delta$. The selected labels together with all group members form exactly a permutation of the input labels. Each group's maximum belongs to that group and contains a translate of every member, and no level has more than $K$ groups. The rounded supply has one separately labeled maximum copy per retained occurrence.
--
--   For every feasible input bin count $m$, correctness requires
--
--   $$
--   \operatorname{Packable}(I,m)\Longrightarrow \bigl(\operatorname{Packable}(\widehat S,m)\land \operatorname{bins}(E_{\rm grp})\le\eta m+\delta\bigr).
--   $$
--
--   The separate packing is checked against the actual selected polygonal regions. The optimum or a feasible comparison packing is never an algorithm input. These finite output data and fixed encoders support the rational-input operational restriction of Definition 5; this definition alone does not assert uniform representative roundability or polynomial-time computation.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Definition 5, printed p.7 / PDF p.8; Section 4, printed pp.10–11 / PDF pp.11–12; Appendix B.3, printed pp.20–22 / PDF pp.21–23.

import Definitions.Def_BeyondConvexity_APTAS_LevelPartition

noncomputable section

namespace BeyondConvexity.APTAS

/-- One containment group, retaining original occurrence labels and its chosen member. -/
structure ContainmentGroup where
  level : ℕ
  members : List ℕ
  maximum : ℕ

/-- Finite output data of a representative-rounding routine, without any assumed
algorithm or correctness certificate. This is not Definition 5's effective interface. -/
structure RoundingData where
  separate : List ℕ
  groups : List ContainmentGroup
  separatePacking : Packing ℚ

def selectedInstance (I : Instance) (labels : List ℕ) : Instance :=
  labels.map (fun i => I.getD i default)

def RoundingData.retainedLabels (R : RoundingData) : List ℕ :=
  R.groups.flatMap ContainmentGroup.members

def RoundingData.roundedSupply (R : RoundingData) (I : Instance) : Instance :=
  R.groups.flatMap (fun g => g.members.map (fun _ => I.getD g.maximum default))

/-- The mathematical output guarantees of Definition 5. This specifies the finite
groups and their geometric meaning, without replacing the required effective interface. -/
def RoundingData.Correct (R : RoundingData) (I : Instance)
    (p : LevelPartition ℝ) (K : ℕ) (η δ : ℝ) : Prop :=
  (R.separate ++ R.retainedLabels).Perm (List.range I.length) ∧
  (∀ g ∈ R.groups, g.level ≤ p.J ∧ g.maximum ∈ g.members ∧
    ∀ i ∈ g.members, i < I.length ∧ p.level i = g.level ∧
      (I.getD i default).ContainsTranslate (I.getD g.maximum default)) ∧
  (∀ j ≤ p.J, (R.groups.filter (fun g => g.level = j)).length ≤ K) ∧
  RationalPacking (selectedInstance I R.separate) R.separatePacking ∧
  ∀ m : ℕ, Packable I m → Packable (R.roundedSupply I) m ∧
    (R.separatePacking.bins : ℝ) ≤ η * m + δ

open RSListDecodingCapacity.AllRates (encNat encList)

def encContainmentGroup (g : ContainmentGroup) : List Bool :=
  encNat g.level ++ encList encNat g.members ++ encNat g.maximum

def encRoundingData (R : RoundingData) : List Bool :=
  encList encNat R.separate ++ encList encContainmentGroup R.groups ++
    encPacking R.separatePacking

end BeyondConvexity.APTAS


