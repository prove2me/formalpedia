-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Supplement_RepresentativeData
-- name    : BeyondConvexity_APTAS_Supplement_RepresentativeData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:14:36.977973+00:00
-- url     : https://prove2.me/theorems/c1279da8-4da8-4376-8c86-506c7cd54c0f
-- title:
--   Dimensional labeled representative-rounding data
-- statement:
--   Representative data contain selected labels $E_{\rm grp}$, containment groups with chosen member maxima, and a separate packing of the selected objects. The published group record is reused; the separate packing and all geometric predicates are dimensional. Correctness requires the selected labels together with all group members to be a permutation of the input occurrence labels. Each group lies in one valid level, its maximum belongs to the group and contains a real translate of every member, and each level has at most $K$ groups. The rounded supply has one maximum copy per retained occurrence.
--
--   The separate packing is feasible, and for every feasible input comparison count $m$,
--
--   $$\operatorname{Packable}(I,m)\Longrightarrow\bigl(\operatorname{Packable}(\widehat S,m)\land\operatorname{bins}(E_{\rm grp})\le\eta m+\delta\bigr).$$
--
--   Real data express the analytic service; rational data have an explicit finite encoder and an exact real interpretation. No comparison packing or optimal solution is stored in these data. Defaults on out-of-range labels are irrelevant because correctness requires an exact permutation and maximum membership.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), Definition 5, printed p.7 / PDF p.8; Section 7, printed p.16 / PDF p.17

import Definitions.Def_BeyondConvexity_APTAS_Supplement_TranslationPacking
import Definitions.Def_BeyondConvexity_APTAS_Supplement_LevelValidity
import Definitions.Def_BeyondConvexity_APTAS_RoundingData

noncomputable section

namespace BeyondConvexity.APTAS.Supplement

/-- Pure output data, reusing the published geometry-independent group record. -/
structure RepresentativeData (d : ℕ) (F : Type) where
  separate : List ℕ
  groups : List ContainmentGroup
  separatePacking : TranslationPacking d F

def selected {d : ℕ} (I : Instance d) (labels : List ℕ) : Instance d :=
  labels.map fun i => I.getD i default

def RepresentativeData.rounded {d : ℕ} {F : Type} (R : RepresentativeData d F)
    (I : Instance d) : Instance d :=
  R.groups.flatMap fun g => g.members.map fun _ => I.getD g.maximum default

def RepresentativeData.Correct {d : ℕ} (R : RepresentativeData d ℝ)
    (I : Instance d) (p : LevelPartition ℝ) (K : ℕ) (η δ : ℝ) : Prop :=
  (R.separate ++ R.groups.flatMap ContainmentGroup.members).Perm (List.range I.length) ∧
  (∀ g ∈ R.groups, g.level ≤ p.J ∧ g.maximum ∈ g.members ∧
    ∀ i ∈ g.members, i < I.length ∧ p.level i = g.level ∧
      (I.getD i default).ContainsTranslate (I.getD g.maximum default)) ∧
  (∀ j ≤ p.J, (R.groups.filter fun g => g.level = j).length ≤ K) ∧
  Feasible (selected I R.separate) R.separatePacking ∧
  ∀ m : ℕ, Packable I m → Packable (R.rounded I) m ∧
    (R.separatePacking.bins : ℝ) ≤ η * m + δ

def RepresentativeData.realize {d : ℕ} (R : RepresentativeData d ℚ) : RepresentativeData d ℝ :=
  ⟨R.separate, R.groups, realizePacking R.separatePacking⟩

open RSListDecodingCapacity.AllRates (encNat encList)

def encRepresentativeData {d : ℕ} (R : RepresentativeData d ℚ) : List Bool :=
  encList encNat R.separate ++ encList encContainmentGroup R.groups ++
    encPacking R.separatePacking

end BeyondConvexity.APTAS.Supplement


