-- Prove2me | Definitions.Def_OAIQ042S003
-- name    : OAIQ042S003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:34:26.744303+00:00
-- url     : https://prove2.me/theorems/78d46c3c-d54e-4d34-9b9b-ae03b6eed04f
-- title:
--   Definitions bundle OAIQ042S003 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 190 declarations of OpenAI's Lean: 47 definitions, 2 inductive types or structures, 9 instances and 132 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.BoundaryErase.keep`, `OAI.CriticalStrip.Diagram.BoundaryErase.left`, `OAI.CriticalStrip.Diagram.BoundaryErase.right`, `OAI.CriticalStrip.Diagram.BoundaryInsert.boundary`, `OAI.CriticalStrip.Diagram.BoundaryInsert.equiv`, `OAI.CriticalStrip.Diagram.BoundaryInsert.gauge`, `OAI.CriticalStrip.Diagram.BoundarySew.tile`, `OAI.CriticalStrip.Diagram.LastDegree`, `OAI.CriticalStrip.Diagram.LaurentBox`, `OAI.CriticalStrip.Diagram.LaurentMatrixBox`, `OAI.CriticalStrip.Diagram.Pairing.flipStep`, `OAI.CriticalStrip.Diagram.Program`, `OAI.CriticalStrip.Diagram.Program.Choices`, `OAI.CriticalStrip.Diagram.ThreeBox.Adj`, `OAI.CriticalStrip.Diagram.ThreeBox.BoundaryData`, `OAI.CriticalStrip.Diagram.ThreeBox.Clean`, `OAI.CriticalStrip.Diagram.ThreeBox.Compatible`, `OAI.CriticalStrip.Diagram.ThreeBox.Config`, `OAI.CriticalStrip.Diagram.ThreeBox.Realizes`, `OAI.CriticalStrip.Diagram.ThreeBox.atRow`, `OAI.CriticalStrip.Diagram.ThreeBox.boundaryOccupied`, `OAI.CriticalStrip.Diagram.ThreeBox.coefficient`, `OAI.CriticalStrip.Diagram.ThreeBox.fiber`, `OAI.CriticalStrip.Diagram.ThreeBox.mirrorConfig`, `OAI.CriticalStrip.Diagram.ThreeBox.patchTest`, `OAI.CriticalStrip.Diagram.ThreeBox.rootTable`, `OAI.CriticalStrip.Diagram.ThreeBox.tileEdge`, `OAI.CriticalStrip.Diagram.ThreeBox.tileNumerator`, `OAI.CriticalStrip.Diagram.Tile.lowerUsed`, `OAI.CriticalStrip.Diagram.Tile.mirror`, `OAI.CriticalStrip.Diagram.Tile.mirrorEquiv`, `OAI.CriticalStrip.Diagram.Tile.representative`, `OAI.CriticalStrip.Diagram.Tile.upperUsed`, `OAI.CriticalStrip.Diagram.TriplePosition.Outside`, `OAI.CriticalStrip.Diagram.TriplePosition.active`, `OAI.CriticalStrip.Diagram.TriplePosition.attached`, `OAI.CriticalStrip.Diagram.TriplePosition.exterior`, `OAI.CriticalStrip.Diagram.TriplePosition.output`, `OAI.CriticalStrip.Diagram.TriplePosition.patch`, `OAI.CriticalStrip.Diagram.TriplePosition.reachTest` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_AugmentedTail`, `StripMass_CramerBounds`, `StripMass_FiniteEnds`, `StripMass_HoneycombDictionary`, `StripMass_HoneycombTiles`, `StripMass_LastRow`, `StripMass_LaurentBox`, `StripMass_LaurentNumerator`, `StripMass_LocalPadding`, `StripMass_MirrorExterior`, `StripMass_PatchReplacement`, `StripMass_PhaseAlgebra`, `StripMass_ReversedConvergence`, `StripMass_SewnAssignment`, `StripMass_SpecializationPolynomial`, `StripMass_StepComplete`, `StripMass_SwapVacancy`, `StripMass_ThreeBoxCertificates`, `StripMass_ThreeBoxProfiles`, `StripMass_ThreeBoxSplitPolynomial`, `StripMass_ThreeBoxWeights`, `StripMass_TopPadding`, `StripMass_TripleCircuit`, `StripMass_TriplePatch`, `StripMass_TurnDisk`, `StripMass_TurnGate`, `StripMass_TurnWideGate`, `StripMass_VacuumClosure`, `StripMass_VacuumDegree`.
--
--   **Imports.** It imports the published bundle `Def_CriticalStripMass`; the bundles `OAIQ042S000` and `OAIQ042S001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S005`, `OAIQ042S006`, `OAIQ042S007` and `OAIQ042S008`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S000
import Definitions.Def_OAIQ042S001

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset


theorem Pairing.eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1) (p : Pairing n) :
    p = empty n := by
  apply Subtype.ext
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hlt := p.property.1 e he
  have hi := e.1.isLt
  have hj := e.2.isLt
  change e.1.val < e.2.val at hlt
  omega

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LastRow
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset

 
def lastTile {n : ℕ} (p q : Pairing (n+1)) : Tile := by
  classical
  exact if p.Occupied (Fin.last n) then
    if q.Occupied (Fin.last n) then .diagonal₁ else .cap
  else if q.Occupied (Fin.last n) then .vertical₀ else .vacant

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentBox
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical Pointwise

 
def LaurentBox {n : ℕ} (f : Laurent n) (b : Fin n → ℕ) : Prop :=
  ∀ e, f.coeff e≠0 → ∀ i, -(b i:ℤ)≤e i ∧ e i≤b i

lemma LaurentBox.zero {n : ℕ} (b : Fin n → ℕ) : LaurentBox 0 b := by
  intro e he
  exact (he rfl).elim

lemma LaurentBox.mono {n : ℕ} {f : Laurent n} {b c : Fin n → ℕ}
    (hf : LaurentBox f b) (hbc : ∀ i,b i ≤ c i) : LaurentBox f c := by
  intro e he i
  have := hf e he i
  have := hbc i
  constructor <;> omega

lemma LaurentBox.add {n : ℕ} {f g : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) (hg : LaurentBox g b) : LaurentBox (f+g) b := by
  intro e he i
  by_cases hh:f.coeff e=0
  · exact hg e (by simpa [AddMonoidAlgebra.coeff_add,hh] using he) i
  · exact hf e hh i

lemma LaurentBox.neg {n : ℕ} {f : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) : LaurentBox (-f) b := by
  intro e he i
  exact hf e (by simpa using he) i

lemma LaurentBox.sub {n : ℕ} {f g : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) (hg : LaurentBox g b) : LaurentBox (f-g) b := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma LaurentBox.mul {n : ℕ} {f g : Laurent n} {b c : Fin n → ℕ}
    (hf : LaurentBox f b) (hg : LaurentBox g c) : LaurentBox (f*g) (b+c) := by
  intro e he i
  have hs := AddMonoidAlgebra.support_coeff_mul_subset f g (Finsupp.mem_support_iff.mpr he)
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.mem_add.mp hs
  have hx := hf x (Finsupp.mem_support_iff.mp hx) i
  have hy := hg y (Finsupp.mem_support_iff.mp hy) i
  have hh := congrFun hxy i
  simp only [Pi.add_apply] at hh ⊢
  push_cast
  constructor <;> omega

lemma LaurentBox.single {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (b : Fin n → ℕ)
    (h : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) : LaurentBox (monomialL e z) b := by
  intro f hf i
  have hh:f=e := by
    by_contra hh
    exact hf (by simp [monomialL,AddMonoidAlgebra.coeff_single,Ne.symm hh])
  subst f
  exact h i

lemma LaurentBox.constant {n : ℕ} (z : ℂ) : LaurentBox (constantL n z) 0 :=
  LaurentBox.single 0 z 0 (by simp)

lemma LaurentBox.one {n : ℕ} : LaurentBox (1:Laurent n) 0 := by
  rw [←monomialL_zero_one]
  exact LaurentBox.single 0 1 0 (by simp)

lemma LaurentBox.sine {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (b : Fin n → ℕ)
    (h : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) : LaurentBox (sineL e z) b := by
  unfold sineL
  have hf:=LaurentBox.single e z b h
  have hg:=LaurentBox.single (-e) z⁻¹ b (by intro i; have :=h i; simp only [Pi.neg_apply]; omega)
  simpa using (hf.sub hg).mul (LaurentBox.constant ((2*Complex.I)⁻¹))

lemma LaurentBox.sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Laurent n)
    (b : Fin n → ℕ) (h : ∀ i∈s,LaurentBox (f i) b) : LaurentBox (∑ i∈s,f i) b := by
  induction s using Finset.induction_on with
  | empty => simpa using LaurentBox.zero b
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

lemma LaurentBox.prod {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Laurent n)
    (b : ι → Fin n → ℕ) (h : ∀ i∈s,LaurentBox (f i) (b i)) :
    LaurentBox (∏ i∈s,f i) (∑ i∈s,b i) := by
  induction s using Finset.induction_on with
  | empty => simpa using LaurentBox.one (n:=n)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

end





noncomputable section
open scoped Classical LaurentPolynomial

lemma peelLaurentEquiv_coeff_coeff {n : ℕ} (i : Fin (n+1)) (f:Laurent (n+1))
    (k : ℤ) (e : Fin n → ℤ) :
    ((peelLaurentEquiv i f).coeff k).coeff e=f.coeff (Fin.insertNth i k e) := by
  change (AddMonoidAlgebra.mapDomainRingEquiv ℂ (peelExponent i) f).coeff (k,e)=_
  rw [AddMonoidAlgebra.coeff_mapDomainRingEquiv]
  rfl

lemma peelLaurent_coeff {n : ℕ} (i : Fin (n+1)) (f:Laurent (n+1)) (k : ℤ) :
    (peelLaurent i f).coeff k=evalLaurent ((peelLaurentEquiv i f).coeff k) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

lemma peelLaurent_coeff_ne_zero_iff {n : ℕ} (i : Fin (n+1)) (f:Laurent (n+1)) (k : ℤ) :
    (peelLaurent i f).coeff k≠0 ↔ ∃ e : Fin n → ℤ,f.coeff (Fin.insertNth i k e)≠0 := by
  rw [peelLaurent_coeff]
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have hz:(peelLaurentEquiv i f).coeff k=0 := by
      ext e
      simpa only [peelLaurentEquiv_coeff_coeff,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hh e
    exact h (by rw [hz]; exact map_zero _)
  · rintro ⟨e,he⟩ hz
    have hh:(peelLaurentEquiv i f).coeff k=0 :=
      (IsFractionRing.injective (SpectralRing n) (SpectralField n)) (hz.trans (map_zero _).symm)
    have :=congrArg (fun g:Laurent n => g.coeff e) hh
    rw [peelLaurentEquiv_coeff_coeff] at this
    exact he this

lemma LaurentBox.peel {n : ℕ} {f : Laurent (n+1)} {b : Fin (n+1) → ℕ}
    (hf:LaurentBox f b) (i:Fin (n+1)) : LaurentInterval (peelLaurent i f) (-(b i:ℤ)) (b i) := by
  intro k hk
  obtain ⟨e,he⟩:=(peelLaurent_coeff_ne_zero_iff i f k).mp hk
  simpa only [Fin.insertNth_apply_same] using hf _ he i

lemma LaurentBox.of_peel {n : ℕ} {f : Laurent (n+1)} {b : Fin (n+1) → ℕ}
    (hf:∀ i:Fin (n+1),LaurentInterval (peelLaurent i f) (-(b i:ℤ)) (b i)) : LaurentBox f b := by
  intro e he i
  apply hf i (e i)
  apply (peelLaurent_coeff_ne_zero_iff i f (e i)).mpr
  exact ⟨Fin.removeNth i e,by simpa only [Fin.insertNth_removeNth,Function.update_eq_self] using he⟩

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section






open Finset
open scoped Classical

 

def LastDegree {K : Type*} [CommRing K] {n : ℕ} (m : ℕ)
    (P : Pairing (n+1) → Polynomial K) : Prop :=
  ∀ p k, (if p.Occupied (Fin.last n) then m ≤ k else m < k) → (P p).coeff k = 0

theorem Pairing.padTop_injective {n : ℕ} : Function.Injective (@Pairing.padTop n) := by
  intro p q h
  have := congrArg (fun r => r.restrict Fin.castSuccOrderEmb) h
  simpa [Pairing.padTop, Pairing.restrict_map] using this



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PatchReplacement
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundaryAdjDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundarySupportDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/







namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset

abbrev Config := Tile × Tile × Tile

def atRow (t : Config) : Fin 3 → Tile := ![t.1,t.2.1,t.2.2]

def tileEdge (t : Config) (v w : Fin 12) : Prop :=
  row v = row w ∧ (atRow t (row v)).Adj (port v) (port w)

def Adj (t : Config) (v w : Fin 12) : Prop :=
  tileEdge t v w ∨
  (wireEdge 2 5 v w ∧ t.1.Occupied 2) ∨
  (wireEdge 3 9 v w ∧ t.1.Occupied 3) ∨
  (wireEdge 7 8 v w ∧ t.2.1.Occupied 3)

instance tileEdgeDecidable (t : Config) : DecidableRel (tileEdge t) := by
  intro v w; unfold tileEdge; infer_instance
instance adjDecidable (t : Config) : DecidableRel (Adj t) := by
  intro v w; unfold Adj; infer_instance

theorem tileEdge_symm (t : Config) {v w : Fin 12} (h : tileEdge t v w) : tileEdge t w v := by
  rcases h with ⟨he,he'⟩
  refine ⟨he.symm, ?_⟩
  rw [← he]
  exact (Tile.adj_symm _).mp he'

theorem adj_symm (t : Config) : Std.Symm (Adj t) := by
  constructor
  intro v w h
  rcases h with h | ⟨h,ho⟩ | ⟨h,ho⟩ | ⟨h,ho⟩
  · exact Or.inl (tileEdge_symm t h)
  · exact Or.inr (Or.inl ⟨wireEdge_symm h,ho⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨wireEdge_symm h,ho⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨wireEdge_symm h,ho⟩))

 
def Compatible (t : Config) : Prop :=
  (t.1.Occupied 2 ↔ t.2.1.Occupied 1) ∧
  (t.1.Occupied 3 ↔ t.2.2.Occupied 1) ∧
  (t.2.1.Occupied 3 ↔ t.2.2.Occupied 0)
instance compatibleDecidable (t : Config) : Decidable (Compatible t) := by
  unfold Compatible; infer_instance


def boundaryOccupied (t : Config) (i : Fin 6) : Prop :=
  (atRow t (row (boundary i))).Occupied (port (boundary i))
instance boundaryOccupiedDecidable (t : Config) (i : Fin 6) : Decidable (boundaryOccupied t i) := by
  unfold boundaryOccupied; infer_instance



structure Realizes (t : Config) (d : Finset (Fin 6 × Fin 6)) : Prop where
  compatible : Compatible t
  occupied : ∀ i, boundaryOccupied t i ↔ boundarySupport d i
  no_loop : ∀ v w, Adj t v w → ∃ i, boundaryOccupied t i ∧
    Relation.ReflTransGen (Adj t) v (boundary i)
  output : ∀ i j, i ≠ j → (boundaryAdj d i j ↔
    Relation.ReflTransGen (Adj t) (boundary i) (boundary j))

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StepComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open Finset
open scoped Classical

variable {K : Type*} [CommRing K]

inductive Program (n : ℕ) (K : Type*) where
  | nil : Program n K
  | snoc : Program n K → Position n → Weights K → Program n K

namespace Program
variable {n : ℕ}

def Choices : Program n K → Type
  | .nil => PUnit
  | .snoc p _ _ => p.Choices × Tile

instance choicesFinite (p : Program n K) : Fintype p.Choices := by
  induction p with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | snoc p _ _ ih => letI := ih; exact inferInstanceAs (Fintype (p.Choices × Tile))

end Program
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

 

def rootTable : Config → Fin 12 → Fin 12
  | (.vacant,.vacant,.vacant) => ![0,1,2,3,4,5,6,7,8,9,10,11]
  | (.vacant,.vacant,.cup) => ![0,1,2,3,4,5,6,7,8,9,10,10]
  | (.vacant,.vertical₀,.vacant) => ![0,1,2,3,4,5,4,7,8,9,10,11]
  | (.vacant,.vertical₀,.cup) => ![0,1,2,3,4,5,4,7,8,9,10,10]
  | (.vacant,.diagonal₀,.vertical₀) => ![0,1,2,3,4,5,6,4,4,9,4,11]
  | (.vacant,.diagonal₀,.diagonal₀) => ![0,1,2,3,4,5,6,4,4,9,10,4]
  | (.vacant,.cup,.vertical₀) => ![0,1,2,3,4,5,6,6,6,9,6,11]
  | (.vacant,.cup,.diagonal₀) => ![0,1,2,3,4,5,6,6,6,9,10,6]
  | (.vertical₀,.vertical₁,.vertical₀) => ![0,1,0,3,4,0,6,0,0,9,0,11]
  | (.vertical₀,.vertical₁,.diagonal₀) => ![0,1,0,3,4,0,6,0,0,9,10,0]
  | (.vertical₀,.diagonal₁,.vacant) => ![0,1,0,3,4,0,0,7,8,9,10,11]
  | (.vertical₀,.diagonal₁,.cup) => ![0,1,0,3,4,0,0,7,8,9,10,10]
  | (.vertical₀,.cap,.vacant) => ![0,1,0,3,0,0,6,7,8,9,10,11]
  | (.vertical₀,.cap,.cup) => ![0,1,0,3,0,0,6,7,8,9,10,10]
  | (.vertical₀,.verticalPair,.vertical₀) => ![0,1,0,3,4,0,4,0,0,9,0,11]
  | (.vertical₀,.verticalPair,.diagonal₀) => ![0,1,0,3,4,0,4,0,0,9,10,0]
  | (.vertical₀,.capCup,.vertical₀) => ![0,1,0,3,0,0,6,6,6,9,6,11]
  | (.vertical₀,.capCup,.diagonal₀) => ![0,1,0,3,0,0,6,6,6,9,10,6]
  | (.vertical₁,.vacant,.vertical₁) => ![0,1,2,1,4,5,6,7,8,1,10,1]
  | (.vertical₁,.vacant,.diagonal₁) => ![0,1,2,1,4,5,6,7,8,1,1,11]
  | (.vertical₁,.vertical₀,.vertical₁) => ![0,1,2,1,4,5,4,7,8,1,10,1]
  | (.vertical₁,.vertical₀,.diagonal₁) => ![0,1,2,1,4,5,4,7,8,1,1,11]
  | (.vertical₁,.diagonal₀,.cap) => ![0,1,2,1,1,5,6,1,1,1,10,11]
  | (.vertical₁,.diagonal₀,.verticalPair) => ![0,1,2,1,4,5,6,4,4,1,4,1]
  | (.vertical₁,.diagonal₀,.capCup) => ![0,1,2,1,1,5,6,1,1,1,10,10]
  | (.vertical₁,.cup,.cap) => ![0,1,2,1,4,5,1,1,1,1,10,11]
  | (.vertical₁,.cup,.verticalPair) => ![0,1,2,1,4,5,6,6,6,1,6,1]
  | (.vertical₁,.cup,.capCup) => ![0,1,2,1,4,5,1,1,1,1,10,10]
  | (.diagonal₀,.vacant,.vertical₁) => ![0,1,2,0,4,5,6,7,8,0,10,0]
  | (.diagonal₀,.vacant,.diagonal₁) => ![0,1,2,0,4,5,6,7,8,0,0,11]
  | (.diagonal₀,.vertical₀,.vertical₁) => ![0,1,2,0,4,5,4,7,8,0,10,0]
  | (.diagonal₀,.vertical₀,.diagonal₁) => ![0,1,2,0,4,5,4,7,8,0,0,11]
  | (.diagonal₀,.diagonal₀,.cap) => ![0,1,2,0,0,5,6,0,0,0,10,11]
  | (.diagonal₀,.diagonal₀,.verticalPair) => ![0,1,2,0,4,5,6,4,4,0,4,0]
  | (.diagonal₀,.diagonal₀,.capCup) => ![0,1,2,0,0,5,6,0,0,0,10,10]
  | (.diagonal₀,.cup,.cap) => ![0,1,2,0,4,5,0,0,0,0,10,11]
  | (.diagonal₀,.cup,.verticalPair) => ![0,1,2,0,4,5,6,6,6,0,6,0]
  | (.diagonal₀,.cup,.capCup) => ![0,1,2,0,4,5,0,0,0,0,10,10]
  | (.diagonal₁,.vertical₁,.vertical₀) => ![0,1,1,3,4,1,6,1,1,9,1,11]
  | (.diagonal₁,.vertical₁,.diagonal₀) => ![0,1,1,3,4,1,6,1,1,9,10,1]
  | (.diagonal₁,.diagonal₁,.vacant) => ![0,1,1,3,4,1,1,7,8,9,10,11]
  | (.diagonal₁,.diagonal₁,.cup) => ![0,1,1,3,4,1,1,7,8,9,10,10]
  | (.diagonal₁,.cap,.vacant) => ![0,1,1,3,1,1,6,7,8,9,10,11]
  | (.diagonal₁,.cap,.cup) => ![0,1,1,3,1,1,6,7,8,9,10,10]
  | (.diagonal₁,.verticalPair,.vertical₀) => ![0,1,1,3,4,1,4,1,1,9,1,11]
  | (.diagonal₁,.verticalPair,.diagonal₀) => ![0,1,1,3,4,1,4,1,1,9,10,1]
  | (.diagonal₁,.capCup,.vertical₀) => ![0,1,1,3,1,1,6,6,6,9,6,11]
  | (.diagonal₁,.capCup,.diagonal₀) => ![0,1,1,3,1,1,6,6,6,9,10,6]
  | (.cap,.vacant,.vacant) => ![0,0,2,3,4,5,6,7,8,9,10,11]
  | (.cap,.vacant,.cup) => ![0,0,2,3,4,5,6,7,8,9,10,10]
  | (.cap,.vertical₀,.vacant) => ![0,0,2,3,4,5,4,7,8,9,10,11]
  | (.cap,.vertical₀,.cup) => ![0,0,2,3,4,5,4,7,8,9,10,10]
  | (.cap,.diagonal₀,.vertical₀) => ![0,0,2,3,4,5,6,4,4,9,4,11]
  | (.cap,.diagonal₀,.diagonal₀) => ![0,0,2,3,4,5,6,4,4,9,10,4]
  | (.cap,.cup,.vertical₀) => ![0,0,2,3,4,5,6,6,6,9,6,11]
  | (.cap,.cup,.diagonal₀) => ![0,0,2,3,4,5,6,6,6,9,10,6]
  | (.cup,.vertical₁,.cap) => ![0,1,2,2,4,2,6,2,2,2,10,11]
  | (.cup,.vertical₁,.verticalPair) => ![0,1,2,2,4,2,6,2,2,2,2,2]
  | (.cup,.vertical₁,.capCup) => ![0,1,2,2,4,2,6,2,2,2,10,10]
  | (.cup,.diagonal₁,.vertical₁) => ![0,1,2,2,4,2,2,7,8,2,10,2]
  | (.cup,.diagonal₁,.diagonal₁) => ![0,1,2,2,4,2,2,7,8,2,2,11]
  | (.cup,.cap,.vertical₁) => ![0,1,2,2,2,2,6,7,8,2,10,2]
  | (.cup,.cap,.diagonal₁) => ![0,1,2,2,2,2,6,7,8,2,2,11]
  | (.cup,.verticalPair,.cap) => ![0,1,2,2,4,2,4,2,2,2,10,11]
  | (.cup,.verticalPair,.verticalPair) => ![0,1,2,2,4,2,4,2,2,2,2,2]
  | (.cup,.verticalPair,.capCup) => ![0,1,2,2,4,2,4,2,2,2,10,10]
  | (.cup,.capCup,.cap) => ![0,1,2,2,2,2,2,2,2,2,10,11]
  | (.cup,.capCup,.verticalPair) => ![0,1,2,2,2,2,6,6,6,2,6,2]
  | (.cup,.capCup,.capCup) => ![0,1,2,2,2,2,2,2,2,2,10,10]
  | (.verticalPair,.vertical₁,.cap) => ![0,0,0,0,4,0,6,0,0,0,10,11]
  | (.verticalPair,.vertical₁,.verticalPair) => ![0,1,0,1,4,0,6,0,0,1,0,1]
  | (.verticalPair,.vertical₁,.capCup) => ![0,0,0,0,4,0,6,0,0,0,10,10]
  | (.verticalPair,.diagonal₁,.vertical₁) => ![0,1,0,1,4,0,0,7,8,1,10,1]
  | (.verticalPair,.diagonal₁,.diagonal₁) => ![0,1,0,1,4,0,0,7,8,1,1,11]
  | (.verticalPair,.cap,.vertical₁) => ![0,1,0,1,0,0,6,7,8,1,10,1]
  | (.verticalPair,.cap,.diagonal₁) => ![0,1,0,1,0,0,6,7,8,1,1,11]
  | (.verticalPair,.verticalPair,.cap) => ![0,0,0,0,4,0,4,0,0,0,10,11]
  | (.verticalPair,.verticalPair,.verticalPair) => ![0,1,0,1,4,0,4,0,0,1,0,1]
  | (.verticalPair,.verticalPair,.capCup) => ![0,0,0,0,4,0,4,0,0,0,10,10]
  | (.verticalPair,.capCup,.cap) => ![0,1,0,1,0,0,1,1,1,1,10,11]
  | (.verticalPair,.capCup,.verticalPair) => ![0,1,0,1,0,0,6,6,6,1,6,1]
  | (.verticalPair,.capCup,.capCup) => ![0,1,0,1,0,0,1,1,1,1,10,10]
  | (.capCup,.vertical₁,.cap) => ![0,0,2,2,4,2,6,2,2,2,10,11]
  | (.capCup,.vertical₁,.verticalPair) => ![0,0,2,2,4,2,6,2,2,2,2,2]
  | (.capCup,.vertical₁,.capCup) => ![0,0,2,2,4,2,6,2,2,2,10,10]
  | (.capCup,.diagonal₁,.vertical₁) => ![0,0,2,2,4,2,2,7,8,2,10,2]
  | (.capCup,.diagonal₁,.diagonal₁) => ![0,0,2,2,4,2,2,7,8,2,2,11]
  | (.capCup,.cap,.vertical₁) => ![0,0,2,2,2,2,6,7,8,2,10,2]
  | (.capCup,.cap,.diagonal₁) => ![0,0,2,2,2,2,6,7,8,2,2,11]
  | (.capCup,.verticalPair,.cap) => ![0,0,2,2,4,2,4,2,2,2,10,11]
  | (.capCup,.verticalPair,.verticalPair) => ![0,0,2,2,4,2,4,2,2,2,2,2]
  | (.capCup,.verticalPair,.capCup) => ![0,0,2,2,4,2,4,2,2,2,10,10]
  | (.capCup,.capCup,.cap) => ![0,0,2,2,2,2,2,2,2,2,10,11]
  | (.capCup,.capCup,.verticalPair) => ![0,0,2,2,2,2,6,6,6,2,6,2]
  | (.capCup,.capCup,.capCup) => ![0,0,2,2,2,2,2,2,2,2,10,10]
  | _ => fun i => i

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset



def Clean (t : Config) : Prop :=
  ∀ v w, Adj t v w → ∃ i, boundaryOccupied t i ∧ rootTable t v = rootTable t (boundary i)

def BoundaryData (t : Config) (d : Finset (Fin 6 × Fin 6)) : Prop :=
  (∀ i, boundaryOccupied t i ↔ boundarySupport d i) ∧
  (∀ i j, i ≠ j → (boundaryAdj d i j ↔ rootTable t (boundary i) = rootTable t (boundary j)))

instance cleanDecidable (t : Config) : Decidable (Clean t) := by
  unfold Clean; infer_instance
instance boundaryDataDecidable (t : Config) (d : Finset (Fin 6 × Fin 6)) :
    Decidable (BoundaryData t d) := by unfold BoundaryData; infer_instance

theorem realizes_unique {t : Config} {i j : Fin 51}
    (hi : Realizes t (diagram i)) (hj : Realizes t (diagram j)) : i = j := by
  apply diagram_injective
  have hadj : ∀ a b, a ≠ b → (boundaryAdj (diagram i) a b ↔ boundaryAdj (diagram j) a b) :=
    fun a b hab => (hi.output a b hab).trans (hj.output a b hab).symm
  apply Finset.ext
  intro e
  constructor
  · intro he
    have hu := diagram_upper i e he
    have hh := (hadj e.1 e.2 (ne_of_lt hu)).mp (Or.inl he)
    rcases hh with he' | he'
    · exact he'
    · exact (lt_asymm hu (diagram_upper j _ he')).elim
  · intro he
    have hu := diagram_upper j e he
    have hh := (hadj e.1 e.2 (ne_of_lt hu)).mpr (Or.inl he)
    rcases hh with he' | he'
    · exact he'
    · exact (lt_asymm hu (diagram_upper i _ he')).elim



end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset
open scoped Classical

def fiber : Fin 51 → Finset Config := ![
  {(.vacant,.vacant,.vacant)},
  {(.vertical₀,.cap,.vacant),(.diagonal₀,.diagonal₀,.cap)},
  {(.verticalPair,.capCup,.cap)},
  {(.verticalPair,.capCup,.capCup)},
  {(.verticalPair,.cap,.diagonal₁)},
  {(.verticalPair,.cap,.vertical₁)},
  {(.verticalPair,.capCup,.verticalPair)},
  {(.vertical₀,.capCup,.vertical₀)},
  {(.vertical₀,.capCup,.diagonal₀)},
  {(.vertical₀,.cap,.cup),(.diagonal₀,.diagonal₀,.capCup)},
  {(.vertical₁,.diagonal₀,.cap),(.diagonal₁,.cap,.vacant)},
  {(.diagonal₁,.capCup,.vertical₀)},
  {(.diagonal₁,.capCup,.diagonal₀)},
  {(.vertical₁,.diagonal₀,.capCup),(.diagonal₁,.cap,.cup)},
  {(.vacant,.vertical₀,.vacant),(.cup,.capCup,.cap)},
  {(.cap,.vertical₀,.vacant),(.verticalPair,.verticalPair,.cap),(.capCup,.capCup,.cap)},
  {(.cap,.vertical₀,.cup),(.verticalPair,.verticalPair,.capCup),(.capCup,.verticalPair,.verticalPair),(.capCup,.capCup,.capCup)},
  {(.vertical₀,.verticalPair,.vertical₀),(.diagonal₀,.vertical₀,.diagonal₁)},
  {(.verticalPair,.verticalPair,.verticalPair)},
  {(.vertical₀,.verticalPair,.diagonal₀),(.diagonal₀,.vertical₀,.vertical₁)},
  {(.vertical₁,.vertical₀,.diagonal₁),(.diagonal₁,.verticalPair,.vertical₀)},
  {(.vertical₁,.vertical₀,.vertical₁),(.diagonal₁,.verticalPair,.diagonal₀)},
  {(.vacant,.vertical₀,.cup),(.cup,.verticalPair,.verticalPair),(.cup,.capCup,.capCup)},
  {(.vacant,.diagonal₀,.vertical₀),(.cup,.cap,.diagonal₁)},
  {(.cap,.diagonal₀,.vertical₀),(.capCup,.cap,.diagonal₁)},
  {(.diagonal₀,.diagonal₀,.verticalPair)},
  {(.vertical₁,.diagonal₀,.verticalPair)},
  {(.vacant,.diagonal₀,.diagonal₀),(.cup,.cap,.vertical₁)},
  {(.cap,.diagonal₀,.diagonal₀),(.capCup,.cap,.vertical₁)},
  {(.capCup,.capCup,.verticalPair)},
  {(.cup,.capCup,.verticalPair)},
  {(.cap,.vacant,.vacant),(.verticalPair,.vertical₁,.cap)},
  {(.cap,.cup,.vertical₀),(.capCup,.diagonal₁,.diagonal₁)},
  {(.cap,.cup,.diagonal₀),(.capCup,.diagonal₁,.vertical₁)},
  {(.cap,.vacant,.cup),(.verticalPair,.vertical₁,.capCup),(.capCup,.vertical₁,.verticalPair)},
  {(.vertical₀,.diagonal₁,.vacant),(.diagonal₀,.cup,.cap)},
  {(.verticalPair,.diagonal₁,.diagonal₁)},
  {(.verticalPair,.diagonal₁,.vertical₁)},
  {(.vertical₀,.diagonal₁,.cup),(.diagonal₀,.cup,.capCup)},
  {(.vertical₀,.vertical₁,.vertical₀),(.diagonal₀,.vacant,.diagonal₁)},
  {(.verticalPair,.vertical₁,.verticalPair)},
  {(.vertical₀,.vertical₁,.diagonal₀),(.diagonal₀,.vacant,.vertical₁)},
  {(.diagonal₀,.cup,.verticalPair)},
  {(.vertical₁,.cup,.cap),(.diagonal₁,.diagonal₁,.vacant)},
  {(.vertical₁,.cup,.capCup),(.diagonal₁,.diagonal₁,.cup)},
  {(.vertical₁,.vacant,.diagonal₁),(.diagonal₁,.vertical₁,.vertical₀)},
  {(.vertical₁,.vacant,.vertical₁),(.diagonal₁,.vertical₁,.diagonal₀)},
  {(.vertical₁,.cup,.verticalPair)},
  {(.vacant,.cup,.vertical₀),(.cup,.diagonal₁,.diagonal₁)},
  {(.vacant,.cup,.diagonal₀),(.cup,.diagonal₁,.vertical₁)},
  {(.vacant,.vacant,.cup),(.cup,.vertical₁,.verticalPair)}]

def coefficient {K : Type*} [CommSemiring K] (a b c : Tile → K) (k : Fin 51) : K :=
  ∑ t ∈ fiber k, a t.1 * b t.2.1 * c t.2.2



def tileNumerator {K : Type*} [CommRing K] (q I z : K) : Tile → K
  | .vacant => (q^4*z^2-1)*(q^6*z^2-1)
  | .vertical₀ | .vertical₁ => I*(q^4+1)*z*(q^6-z^2)
  | .diagonal₀ | .diagonal₁ => q^2*(z^2-1)*(q^6-z^2)
  | .cap | .cup => I*(q^4+1)*q^3*z*(z^2-1)
  | .verticalPair => (q^6-z^2)*(q^4-z^2)
  | .capCup => q^4*(z^2-q^2)*(z^2-1)

theorem coefficient_0 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 0 = a .vacant * b .vacant * c .vacant := by
  simp [coefficient, fiber]

theorem coefficient_14 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 14 = a .vacant * b .vertical₀ * c .vacant + a .cup * b .capCup * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_22 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 22 = a .vacant * b .vertical₀ * c .cup + a .cup * b .verticalPair * c .verticalPair + a .cup * b .capCup * c .capCup := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_23 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 23 = a .vacant * b .diagonal₀ * c .vertical₀ + a .cup * b .cap * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_27 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 27 = a .vacant * b .diagonal₀ * c .diagonal₀ + a .cup * b .cap * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_30 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 30 = a .cup * b .capCup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_43 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 43 = a .vertical₁ * b .cup * c .cap + a .diagonal₁ * b .diagonal₁ * c .vacant := by
  simp [coefficient, fiber]

theorem coefficient_44 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 44 = a .vertical₁ * b .cup * c .capCup + a .diagonal₁ * b .diagonal₁ * c .cup := by
  simp [coefficient, fiber]

theorem coefficient_45 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 45 = a .vertical₁ * b .vacant * c .diagonal₁ + a .diagonal₁ * b .vertical₁ * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_46 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 46 = a .vertical₁ * b .vacant * c .vertical₁ + a .diagonal₁ * b .vertical₁ * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_47 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 47 = a .vertical₁ * b .cup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_48 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 48 = a .vacant * b .cup * c .vertical₀ + a .cup * b .diagonal₁ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_49 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 49 = a .vacant * b .cup * c .diagonal₀ + a .cup * b .diagonal₁ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_50 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 50 = a .vacant * b .vacant * c .cup + a .cup * b .vertical₁ * c .verticalPair := by
  simp [coefficient, fiber]

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxSplitPolynomial
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Patch.glued_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

theorem split3_numerator_0 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 0 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 0 := by
  rw [coefficient_0, coefficient_0]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_14 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 14 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 46 := by
  rw [coefficient_14, coefficient_46]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_22 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 22 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 47 := by
  rw [coefficient_22, coefficient_47]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_28 hq]
  all_goals ring

theorem split3_numerator_23 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 23 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 45 := by
  rw [coefficient_23, coefficient_45]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_27 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 27 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 43 := by
  rw [coefficient_27, coefficient_43]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem split3_numerator_30 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 30 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 44 := by
  rw [coefficient_30, coefficient_44]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_32 hq]
  all_goals ring

theorem split3_numerator_48 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 48 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 50 := by
  rw [coefficient_48, coefficient_50]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem split3_numerator_49 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 49 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 49 := by
  rw [coefficient_49, coefficient_49]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf

theorem split3_numerator_50 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) 50 =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile 48 := by
  rw [coefficient_50, coefficient_48]
  simp only [tileNumerator, deletionTile, swapTile, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_17 hq, eighthRoot_power_23 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring






open Finset



theorem realizes_boundary_reach {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (i j : Fin 6) :
    Relation.ReflTransGen (Adj t) (boundary i) (boundary j) ↔ i=j ∨ boundaryAdj d i j := by
  by_cases he : i=j
  · subst j
    simp only [true_or, iff_true]
    exact .refl
  · simp only [he, false_or]
    exact (h.output i j he).symm

theorem realizes_compressed {B : Type*} {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop) :
    Patch.compressed (Adj t) s boundary b active = diagramExterior d s b active := by
  funext x y
  apply propext
  simp only [Patch.compressed, diagramExterior, realizes_boundary_reach h]

theorem substitute_reach {B : Type*} {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop)
    (x y : B) :
    Relation.ReflTransGen (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y) ↔
      Relation.ReflTransGen (diagramExterior d s b active) x y := by
  rw [Patch.exterior_reach_iff, realizes_compressed h]

theorem substitute_drains {B : Type*} {t : Config} {d : Finset (Fin 6 × Fin 6)}
    (h : Realizes t d) (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop)
    (ha : ∀ i, active i ↔ boundaryOccupied t i) (out : B → Prop) :
    Patch.drains (Patch.glued (Adj t) s boundary b active) (Patch.exteriorOutput out) ↔
      Patch.drains (diagramExterior d s b active) out := by
  rw [Patch.drains_glued_iff, realizes_compressed h]
  apply and_iff_right
  intro x y hxy
  obtain ⟨i,hi,hr⟩ := h.no_loop x y hxy
  exact ⟨i,(ha i).mpr hi,hr⟩



def patchTest {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop)
    (test : (B → B → Prop) → Prop) (t : Config) : Prop :=
  Compatible t ∧ (∀ i, active i ↔ boundaryOccupied t i) ∧
  Patch.drains (Patch.glued (Adj t) s boundary b active) (Patch.exteriorOutput out) ∧
  test (fun x y => Relation.ReflTransGen (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y))

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhaseAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

theorem phase_four : phase^(4:ℕ) = Complex.I := by
  have h := phase_pow 4
  norm_num only [zpow_ofNat, Int.cast_ofNat] at h
  rw [h]
  have he : (4:ℂ)*lambda*Complex.I = (Real.pi / 2 : ℝ)*Complex.I := by
    simp [lambda]
    ring
  rw [he, Complex.exp_mul_I]
  simp

theorem constF_phase_four (n : ℕ) : constF n phase ^ 4 = constF n Complex.I := by
  rw [constF, ← map_pow, phase_four]
  rfl

theorem constF_d_eq (n : ℕ) :
    constF n d = ((constF n phase)^4+1)/(2*(constF n phase)^2) := by
  change constF n (Real.cos ((2:ℝ)*lambda)) = _
  have h := torusCos_phase_pow n 2
  norm_num only [Nat.cast_ofNat] at h
  rw [← h]
  unfold torusCos
  field_simp [constF_phase_ne_zero]


 

 


def torusCommon {n : ℕ} (z : SpectralField n) : SpectralField n :=
  (constF n phase^4*z^2-1)*(constF n phase^6*z^2-1)

theorem torusCommon_eq {n : ℕ} (z : SpectralField n) (hz : z ≠ 0) :
    torusCommon z = 4*(constF n Complex.I)^2*(constF n phase)^5*z^2*torusL z := by
  unfold torusCommon torusL torusSin
  have hq := constF_phase_ne_zero n
  have hI : constF n Complex.I ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  field_simp
  ring

theorem torusCommon_ne_zero {n : ℕ} (z : SpectralField n) (hz : z ≠ 0)
    (hL : torusL z ≠ 0) : torusCommon z ≠ 0 := by
  rw [torusCommon_eq z hz]
  have hI : constF n Complex.I ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ hI)) (pow_ne_zero _ (constF_phase_ne_zero n))) (pow_ne_zero _ hz)) hL

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset

 

theorem torusWeights_cleared {n : ℕ} (z : SpectralField n) (hz : z ≠ 0)
    (hL : torusL z ≠ 0) (t : Tile) :
    torusCommon z * (torusWeights z).tile t =
      tileNumerator (constF n phase) (constF n phase^4) z t := by
  have hq := constF_phase_ne_zero n
  have hI : constF n Complex.I ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  cases t
  · simp [Weights.tile, tileNumerator, torusCommon]
  all_goals
    rw [torusCommon_eq z hz]
    simp only [torusWeights, Weights.tile, tileNumerator]
    try rw [constF_d_eq]
    simp only [torusSin]
    rw [← constF_phase_four n]
    field_simp [hL]
    ring


 

 


theorem coefficient_scale {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (r s u : K) (k : Fin 51) :
    coefficient (fun t => r*a t) (fun t => s*b t) (fun t => u*c t) k =
      (r*s*u) * coefficient a b c k := by
  unfold coefficient
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  ring



end





noncomputable section
open scoped Classical

theorem split3_numerator {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1)
    (k : Fin 51) (h₁ : ¬ boundarySupport (diagram k) 1) (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) k =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile (mirrorIndex k) := by
  fin_cases k
  · exact split3_numerator_0 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_14 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_22 q z hq
  · exact split3_numerator_23 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_27 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact split3_numerator_30 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_48 q z hq
  · exact split3_numerator_49 q z hq
  · exact split3_numerator_50 q z hq

end
end CriticalStrip.Diagram.ThreeBox

 

 

namespace CriticalStrip.Diagram
noncomputable section


namespace ThreeBox
lemma coefficient_scale₂₃ {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (r s : K) (k : Fin 51) :
    coefficient a (fun t => r*b t) (fun t => s*c t) k =
      (r*s) * coefficient a b c k := by
  simpa using coefficient_scale a b c 1 r s k

lemma coefficient_deletion {n : ℕ} (z : SpectralField n)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF n phase^3*z)≠0)
    (k : Fin 51) (h₁ : ¬ boundarySupport (diagram k) 1)
    (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient deletionWeights.tile (torusWeights (constF n phase^3*z)).tile
        (torusWeights z).tile k =
      coefficient swapWeights.tile swapWeights.tile deletionWeights.tile (mirrorIndex k) := by
  have hN (v : SpectralField n) (hv : v≠0) (hLv : torusL v≠0) :
      (fun t => torusCommon v*(torusWeights v).tile t) =
        tileNumerator (constF n phase) (constF n phase^4) v :=
    funext (torusWeights_cleared v hv hLv)
  have hz3 := mul_ne_zero (pow_ne_zero 3 (constF_phase_ne_zero n)) hz
  have h := split3_numerator (constF n phase) z (constF_phase_eight n) k h₁ h₂
  change coefficient deletionTile _ _ k =
    torusCommon (constF n phase^3*z)*torusCommon z *
      coefficient swapTile swapTile deletionTile (mirrorIndex k) at h
  rw [←hN _ hz3 hL3,←hN _ hz hL,coefficient_scale₂₃] at h
  simpa only [deletionWeights_tile,swapWeights_tile] using
    mul_left_cancel₀ (mul_ne_zero (torusCommon_ne_zero _ hz3 hL3)
      (torusCommon_ne_zero _ hz hL)) h

end ThreeBox






end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TripleCircuit
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundaryDataDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.cleanDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def wiring (p : Pairing n) (t : ThreeBox.Config) : (Fin n ⊕ Fin 12) → (Fin n ⊕ Fin 12) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inr v,.inr w => ThreeBox.Adj t v w
  | .inl i,.inr v | .inr v,.inl i =>
      (i=s.a ∧ v=4 ∧ p.Occupied s.a) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨
      (i=s.c ∧ v=1 ∧ p.Occupied s.c)

end TriplePosition





namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

instance wiring_symm (p : Pairing n) (t : ThreeBox.Config) : Std.Symm (s.wiring p t) := by
  constructor
  rintro (i|v) (j|w) h
  · exact Pairing.adj_symm h
  · exact h
  · exact h
  · exact (ThreeBox.adj_symm t).symm _ _ h

def support (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) : Prop :=
  if i=s.a then t.2.1.Occupied 2 else if i=s.b then t.2.2.Occupied 2
    else if i=s.c then t.2.2.Occupied 3 else p.Occupied i

end TriplePosition
end
end CriticalStrip.Diagram





namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def active (p q : Pairing n) : Fin 6 → Prop :=
  ![p.Occupied s.a,p.Occupied s.b,p.Occupied s.c,
    q.Occupied s.a,q.Occupied s.b,q.Occupied s.c]

def exterior (p q : Pairing n) : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inl i,.inr j | .inr j,.inl i => i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c ∧ q.Occupied i
  | .inr _,.inr _ => False

def Outside (p q : Pairing n) : Prop :=
  ∀ i, i≠s.a → i≠s.b → i≠s.c → (p.Occupied i ↔ q.Occupied i)

def attached (p q : Pairing n) (t : ThreeBox.Config) :=
  Graph.Attached.wiring (s.wiring p t) s.boundary q.Occupied

def patch (p q : Pairing n) (t : ThreeBox.Config) :=
  Patch.glued (ThreeBox.Adj t) (s.exterior p q) ThreeBox.boundary s.interface (s.active p q)

end TriplePosition
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TriplePatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def output (q : Pairing n) : Fin n ⊕ Fin n → Prop
  | .inl _ => False
  | .inr i => q.Occupied i

def reachTest (q : Pairing n) (r : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → Prop) : Prop :=
  ∀ i j, r (.inr i) (.inr j) ↔ i=j ∨ q.Adj i j

lemma active_iff (p q : Pairing n) (t : ThreeBox.Config) :
    (∀ i, s.active p q i ↔ ThreeBox.boundaryOccupied t i) ↔
      (p.Occupied s.a ↔ t.2.1.Occupied 0) ∧
      (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.c ↔ t.1.Occupied 1) ∧
      (q.Occupied s.a ↔ t.2.1.Occupied 2) ∧
      (q.Occupied s.b ↔ t.2.2.Occupied 2) ∧ (q.Occupied s.c ↔ t.2.2.Occupied 3) := by
  simp [Fin.forall_fin_succ,active,ThreeBox.boundaryOccupied,ThreeBox.boundary,
    ThreeBox.atRow,ThreeBox.row,ThreeBox.port]

end TriplePosition

 

 

namespace Tile

def mirror : Tile → Tile
  | .vacant => .vacant
  | .vertical₀ => .vertical₁
  | .vertical₁ => .vertical₀
  | .diagonal₀ => .diagonal₁
  | .diagonal₁ => .diagonal₀
  | .cap => .cap
  | .cup => .cup
  | .verticalPair => .verticalPair
  | .capCup => .capCup

lemma mirror_involutive : Function.Involutive mirror := by intro t; cases t <;> rfl

def mirrorEquiv : Tile ≃ Tile := ⟨mirror,mirror,mirror_involutive,mirror_involutive⟩

end Tile





end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MirrorExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram





noncomputable section





open scoped Classical
open Finset

variable {K : Type*} [CommRing K] {n : ℕ}

namespace ThreeBox

def mirrorConfig : Config ≃ Config :=
  Equiv.prodCongr Tile.mirrorEquiv (Equiv.prodCongr Tile.mirrorEquiv Tile.mirrorEquiv)

end ThreeBox

end

 

 

noncomputable section
open scoped Classical






namespace Pairing
variable {n m : ℕ} (f : Fin n ↪o Fin m)

lemma map_omit_adj (p : Pairing n) (a b : Fin n) (x y : Fin m) :
    ((p.map f).omitTwo (f a) (f b)).Adj x y ↔
      ∃ i j, (p.omitTwo a b).Adj i j ∧ f i=x ∧ f j=y := by
  simp only [omitTwo_adj,map_adj]
  constructor
  · rintro ⟨⟨i,j,h,rfl,rfl⟩,hia,hib,hja,hjb⟩
    exact ⟨i,j,⟨h,fun he => hia (congrArg f he),fun he => hib (congrArg f he),
      fun he => hja (congrArg f he),fun he => hjb (congrArg f he)⟩,rfl,rfl⟩
  · rintro ⟨i,j,⟨h,hia,hib,hja,hjb⟩,rfl,rfl⟩
    exact ⟨⟨i,j,h,rfl,rfl⟩,fun he => hia (f.injective he),fun he => hib (f.injective he),
      fun he => hja (f.injective he),fun he => hjb (f.injective he)⟩

end Pairing
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LocalPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
open Finset

namespace Pairing
lemma map_injective {n m : ℕ} (f : Fin n ↪o Fin m) : Function.Injective (Pairing.map f) := by
  intro p q h
  simpa only [restrict_map] using congrArg (Pairing.restrict f) h
end Pairing

end





end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SwapVacancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
open Finset
namespace Pairing

lemma map_not_occupied_omit {n : ℕ} (p : Pairing n) (a : Fin (n+1)) :
    ¬(p.map (Fin.succAboveOrderEmb a)).Occupied a := by
  rintro ⟨_,h⟩
  obtain ⟨i,j,_,hi,_⟩ := (map_adj _ p _ _).mp h
  exact Fin.succAbove_ne a i hi

end Pairing

end

 

 

noncomputable section
open scoped Classical





namespace Pairing

lemma map_map {n m l : ℕ} (f : Fin n ↪o Fin m) (g : Fin m ↪o Fin l) (p : Pairing n) :
    (p.map f).map g=p.map (f.trans g) := by
  apply Subtype.ext
  change (p.val.map _).map _=p.val.map _
  rw [Finset.map_map]
  rfl

lemma map_empty {n m : ℕ} (f : Fin n ↪o Fin m) : (empty n).map f=empty m := by
  apply Subtype.ext
  exact Finset.map_empty _

lemma omit_padBottom {n : ℕ} (r : Fin (n+1)) (p : Pairing n) :
    (p.map (Fin.succAboveOrderEmb r)).padBottom =
      p.padBottom.map (Fin.succAboveOrderEmb r.succ) := by
  unfold padBottom
  rw [map_map,map_map]
  congr 1
  apply DFunLike.ext
  intro i
  change (r.succAbove i).succ=r.succ.succAbove i.succ
  by_cases hi : i.val < r.val <;> simp [Fin.succAbove,Fin.lt_def,hi]

lemma omit_padTop {n : ℕ} (r : Fin (n+1)) (p : Pairing n) :
    (p.map (Fin.succAboveOrderEmb r)).padTop =
      p.padTop.map (Fin.succAboveOrderEmb r.castSucc) := by
  unfold padTop
  rw [map_map,map_map]
  congr 1
  apply DFunLike.ext
  intro i
  change (r.succAbove i).castSucc=r.castSucc.succAbove i.castSucc
  by_cases hi : i.val < r.val <;> simp [Fin.succAbove,Fin.lt_def,hi]

lemma omit_eq_padTop_exists {n : ℕ} (r : Fin (n+1)) (t : Pairing (n+1))
    (q : Pairing (n+1)) (h : t.map (Fin.succAboveOrderEmb r.castSucc)=q.padTop) :
    ∃ p : Pairing n, p.padTop=t := by
  apply Exists.intro (t.restrict Fin.castSuccOrderEmb)
  apply padTop_restrict
  intro ht
  have hh : (t.map (Fin.succAboveOrderEmb r.castSucc)).Occupied (Fin.last (n+1)) := by
    rw [←omit_last r]
    exact (map_occupied _ t _).mpr ht
  rw [h] at hh
  exact q.padTop_not_occupied_last hh

end Pairing
end





noncomputable section
open scoped Classical
open Finset







lemma Pairing.map_eq_empty_iff {n m : ℕ} (e : Fin n ↪o Fin m) (p : Pairing n) :
    p.map e=empty m ↔ p=empty n := by
  rw [←Pairing.map_empty e]
  exact (Pairing.map_injective e).eq_iff

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

def LaurentMatrixBox {n : ℕ} {α β : Type*} (A : Matrix α β (Laurent n)) (b : Fin n → ℕ) : Prop :=
  ∀ p q,LaurentBox (A p q) b

lemma LaurentMatrixBox.one {n : ℕ} {α : Type*} [DecidableEq α] :
    LaurentMatrixBox (1:Matrix α α (Laurent n)) 0 := by
  intro p q
  by_cases h:p=q
  · subst p; simp only [Matrix.one_apply_eq]; exact LaurentBox.one
  · simp only [Matrix.one_apply_ne h]; exact LaurentBox.zero _

lemma LaurentMatrixBox.mul {n : ℕ} {α β γ : Type*} [Fintype β]
    {A : Matrix α β (Laurent n)} {B : Matrix β γ (Laurent n)}
    {a b : Fin n → ℕ} (hA : LaurentMatrixBox A a) (hB : LaurentMatrixBox B b) :
    LaurentMatrixBox (A*B) (a+b) := by
  intro p q
  rw [Matrix.mul_apply]
  exact LaurentBox.sum _ _ _ (fun i _ => (hA p i).mul (hB i q))

lemma LaurentMatrixBox.smul {n : ℕ} {α β : Type*} {A : Matrix α β (Laurent n)}
    {c : Laurent n} {a b : Fin n → ℕ} (hc : LaurentBox c a) (hA : LaurentMatrixBox A b) :
    LaurentMatrixBox (c • A) (a+b) := by
  intro p q
  exact hc.mul (hA p q)







lemma LaurentBox.cosine {n : ℕ} (e:Fin n → ℤ) (z:ℂ) (b:Fin n → ℕ)
    (he:∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) : LaurentBox (cosineL e z) b := by
  apply LaurentBox.add
  · exact LaurentBox.single e _ b he
  · exact LaurentBox.single (-e) _ b (by intro i; have :=he i; simp only [Pi.neg_apply]; omega)

lemma LaurentBox.pow {n : ℕ} {f:Laurent n} {b:Fin n → ℕ} (hf:LaurentBox f b) (k:ℕ) :
    LaurentBox (f^k) (fun i => k*b i) := by
  induction k with
  | zero =>
    rw [pow_zero]
    intro e he i
    simpa only [Nat.zero_mul,Pi.zero_apply] using LaurentBox.one e he i
  | succ k ih =>
    rw [pow_succ]
    convert ih.mul hf using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    simp [Nat.succ_mul]

lemma LaurentBox.insert {n : ℕ} (i:Fin (n+1)) {f:Laurent n} {b:Fin n → ℕ}
    (hf:LaurentBox f b) : LaurentBox (insertLaurent i f) (Fin.insertNth i 0 b) := by
  intro e he k
  have hs : e∈f.coeff.support.image (insertExponent i) :=
    (Finsupp.mapDomain_support (s:=f.coeff) (f:=insertExponent i)) (Finsupp.mem_support_iff.mpr he)
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hs
  refine Fin.succAboveCases i ?_ (fun j => ?_) k
  · simp [insertExponent]
  · simpa only [insertExponent,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Fin.insertNth_apply_succAbove] using
      hf a (Finsupp.mem_support_iff.mp ha) j

lemma LaurentMatrixBox.mulVec {n:ℕ} {α β:Type*} [Fintype β]
    {A:Matrix α β (Laurent n)} {v:β → Laurent n} {a b:Fin n → ℕ}
    (hA:LaurentMatrixBox A a) (hv:∀ q,LaurentBox (v q) b) :
    ∀ p,LaurentBox (A.mulVec v p) (a+b) := by
  intro p
  exact LaurentBox.sum _ _ _ (fun q _ => (hA p q).mul (hv q))

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CramerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma LaurentMatrixBox.det_terms {n m:ℕ} (A:Matrix (Fin m) (Fin m) (Laurent n))
    (b:Fin m → Fin m → Fin n → ℕ) (c:Fin n → ℕ)
    (hA:∀ i j,LaurentBox (A i j) (b i j))
    (hc:∀ σ:Equiv.Perm (Fin m),∀ k,(∑ j,b (σ j) j k) ≤ c k) : LaurentBox A.det c := by
  rw [Matrix.det_apply']
  apply LaurentBox.sum
  intro σ _
  have hp:LaurentBox (∏ j,A (σ j) j) c :=
    (LaurentBox.prod Finset.univ (fun j => A (σ j) j) (fun j => b (σ j) j)
      (fun j _ => hA (σ j) j)).mono (by simpa only [Finset.sum_apply] using hc σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs|hs
  · simpa only [hs,Units.val_one,Int.cast_one,one_mul] using hp
  · simpa only [hs,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul] using hp.neg



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpecializationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma LastDegree.map {R K:Type*} [CommRing R] [CommRing K] {n m:ℕ}
    {P:Pairing (n+1) → Polynomial R} (hP:LastDegree m P) (φ:R →+* K) :
    LastDegree m (fun p => (P p).map φ) := by
  intro p k hk
  rw [Polynomial.coeff_map,hP p k hk,map_zero]

lemma LastDegree.of_map {R K:Type*} [CommRing R] [CommRing K] {n m:ℕ}
    {P:Pairing (n+1) → Polynomial R} (φ:R →+* K) (hφ:Function.Injective φ)
    (hP:LastDegree m (fun p => (P p).map φ)) : LastDegree m P := by
  intro p k hk
  apply hφ
  simpa only [Polynomial.coeff_map,map_zero] using hP p k hk







end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram




noncomputable section
open scoped Classical BigOperators

namespace Graph


lemma DrainsAt.mono_root {V : Type*} {r : V → V → Prop} {a b : V}
    (h : DrainsAt r a) (hab : Relation.ReflTransGen r a b) : DrainsAt r b :=
  fun _ _ hvw => (h _ _ hvw).trans hab



end Graph
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

namespace Pairing


def flipStep {n : ℕ} : StepVertex n → StepVertex n
  | .old i => .out i
  | .out i => .old i
  | .box i => .box (Tile.transposePort i)

@[simp] lemma flipStep_involutive {n : ℕ} (v : StepVertex n) : flipStep (flipStep v)=v := by
  cases v <;> simp [flipStep]

end Pairing



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombTiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators


namespace Tile



def upperUsed : Tile → Bool
  | .vacant | .cup => false
  | _ => true

def lowerUsed : Tile → Bool
  | .vacant | .cap => false
  | _ => true

lemma upperUsed_iff (t : Tile) (h : t ≠ .verticalPair) :
    t.upperUsed ↔ t.Occupied 0 ∨ t.Occupied 1 ∨ t.middle := by
  revert t
  decide

lemma lowerUsed_iff (t : Tile) (h : t ≠ .verticalPair) :
    t.lowerUsed ↔ t.Occupied 2 ∨ t.Occupied 3 ∨ t.middle := by
  revert t
  decide

end Tile
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombDictionary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph






namespace Diagram



lemma Tile.nonvacant_iff_used (t : Tile) : t ≠ .vacant ↔ t.upperUsed ∨ t.lowerUsed := by
  revert t
  decide

lemma Tile.upperUsed_internal (t : Tile) (ht : t ≠ .verticalPair) :
    t.upperUsed → t.Occupied 1 ∨ t.middle := by
  revert t
  decide

lemma Tile.lowerUsed_internal (t : Tile) (ht : t ≠ .verticalPair) :
    t.lowerUsed → t.Occupied 2 ∨ t.middle := by
  revert t
  decide

end Diagram

namespace HoneycombAssignment
variable {N : ℕ}

lemma up_support_iff (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) :
    up i j ∈ D.graph.support ↔ (D.tile (i,j)).upperUsed := by
  change (∃ w, D.graph.Adj (up i j) w) ↔ _
  constructor
  · rintro ⟨w,hw⟩
    apply (Tile.upperUsed_iff _ (D.physical (i,j))).mpr
    rcases (D.up_neighbors i j w).mp hw with ⟨_,h⟩
    rcases h with ⟨_,hm⟩ | ⟨_,he⟩ | ⟨_,_,hs⟩
    · exact Or.inr (Or.inr hm)
    · exact Or.inr (Or.inl he)
    · exact Or.inl hs
  · intro hu
    have hj : j<N := by
      by_contra hn
      rw [D.outside i j (by omega)] at hu
      exact Bool.false_ne_true hu
    rcases Tile.upperUsed_internal _ (D.physical (i,j)) hu with hw | hm
    · exact ⟨down (i-1) j,(D.up_neighbors i j _).mpr ⟨hj,Or.inr (Or.inl ⟨rfl,hw⟩)⟩⟩
    · exact ⟨down i j,(D.up_neighbors i j _).mpr ⟨hj,Or.inl ⟨rfl,hm⟩⟩⟩

def tileSupport (D : HoneycombAssignment N) : Set Cell := {q | D.tile q ≠ .vacant}

end HoneycombAssignment

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReversedConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
namespace Tile



lemma horizontal_adj (t : Tile) (a b : Fin 4) :
    t.horizontal.Adj (horizontalPort a) (horizontalPort b) ↔ t.Adj a b := by
  revert t a b
  decide



lemma physical_horizontal (t : Tile) : t.horizontal≠.verticalPair ↔ t≠.capCup := by
  cases t <;> decide

end Tile
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Tile
 

def representative (t : Tile) (upper : Bool) : Fin 4 :=
  if upper then if t.Occupied 0 then 0 else 1
  else if t.Occupied 2 then 2 else 3

lemma representative_side (t : Tile) (b : Bool) :
    decide ((t.representative b).val<2)=b := by
  cases b <;> simp [representative] <;> split <;> decide

lemma representative_occupied (t : Tile) (ht : t≠.verticalPair) (b : Bool) :
    t.Occupied (t.representative b) ↔ if b then t.upperUsed else t.lowerUsed := by
  revert t b
  decide

lemma occupied_triangle (t : Tile) (ht : t≠.verticalPair) (p : Fin 4) (hp : t.Occupied p) :
    if decide (p.val<2) then t.upperUsed = true else t.lowerUsed = true := by
  revert t p
  decide

lemma reach_representative (t : Tile) (ht : t≠.verticalPair) (p : Fin 4) (hp : t.Occupied p) :
    Relation.ReflTransGen t.Adj p (t.representative (decide (p.val<2))) := by
  cases t <;> fin_cases p <;>
    simp_all [representative,Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals first | exact .refl | exact .single (by decide)

lemma reach_middle (t : Tile) (ht : t≠.verticalPair) (hm : t.middle) :
    Relation.ReflTransGen t.Adj (t.representative true) (t.representative false) := by
  cases t <;> simp_all [middle,representative,Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals exact .single (by decide)

lemma adjacent_projects (t : Tile) (ht : t≠.verticalPair) (a b : Fin 4) (h : t.Adj a b) :
    decide (a.val<2)=decide (b.val<2) ∨ t.middle := by
  revert t a b
  decide
end Diagram.Tile

abbrev HoneycombPort := Cell × Fin 4

def portTriangle (v : HoneycombPort) : Triangle :=
  (v.1.1,v.1.2,decide (v.2.val<2))

namespace HoneycombAssignment
variable {N : ℕ}

 

def portWiring (D : HoneycombAssignment N) (v w : HoneycombPort) : Prop :=
  (v.1=w.1 ∧ (D.tile v.1).Adj v.2 w.2) ∨
  (v.1.2=w.1.2 ∧ v.1.1+1=w.1.1 ∧ v.2=2 ∧ w.2=1 ∧ (D.tile v.1).Occupied 2) ∨
  (w.1.2=v.1.2 ∧ w.1.1+1=v.1.1 ∧ w.2=2 ∧ v.2=1 ∧ (D.tile w.1).Occupied 2) ∨
  (v.1.1=w.1.1 ∧ v.1.2+1=w.1.2 ∧ w.1.2<N ∧ v.2=3 ∧ w.2=0 ∧ (D.tile v.1).Occupied 3) ∨
  (w.1.1=v.1.1 ∧ w.1.2+1=v.1.2 ∧ v.1.2<N ∧ w.2=3 ∧ v.2=0 ∧ (D.tile w.1).Occupied 3)

lemma portWiring_symm (D : HoneycombAssignment N) {v w : HoneycombPort} :
    D.portWiring v w → D.portWiring w v := by
  intro h
  rcases h with ⟨he,h⟩ | h | h | h | h
  · exact Or.inl ⟨he.symm,by simpa only [he] using (Tile.adj_symm _).mp h⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

instance portWiring_symm_instance (D : HoneycombAssignment N) : Std.Symm D.portWiring :=
  ⟨fun _ _=>D.portWiring_symm⟩

lemma port_used (D : HoneycombAssignment N) (v : HoneycombPort) :
    Graph.Used D.portWiring v ↔ (D.tile v.1).Occupied v.2 := by
  constructor
  · rintro ⟨w,h⟩
    rcases v with ⟨⟨i,j⟩,a⟩
    rcases w with ⟨⟨k,l⟩,b⟩
    dsimp only [portWiring,Prod.fst,Prod.snd] at h
    rcases h with ⟨_,h⟩ | ⟨_,_,rfl,_,h⟩ | ⟨hj,hi,_,rfl,h⟩ |
      ⟨_,_,_,rfl,_,h⟩ | ⟨hi,hj,hn,_,rfl,h⟩
    · exact ⟨b,h⟩
    · exact h
    · have hh := (D.horizontal k l).mp h
      simpa only [hi,hj] using hh
    · exact h
    · have hh := (D.vertical k l (by omega)).mp h
      simpa only [hi,hj] using hh
  · rintro ⟨p,hp⟩
    exact ⟨(v.1,p),Or.inl ⟨rfl,hp⟩⟩

lemma port_in_strip (D : HoneycombAssignment N) {q : Cell} {a : Fin 4}
    (h : (D.tile q).Occupied a) : q.2<N := by
  by_contra hn
  have hh := D.outside q.1 q.2 (by omega)
  exact Tile.vacant_not_occupied a (hh ▸ h)



lemma tile_reach (D : HoneycombAssignment N) (q : Cell) {a b : Fin 4}
    (h : Relation.ReflTransGen (D.tile q).Adj a b) :
    Relation.ReflTransGen D.portWiring (q,a) (q,b) :=
  Graph.map_reach (fun a=>(q,a)) (fun _ _ h=>.single (Or.inl ⟨rfl,h⟩)) h

def representative (D : HoneycombAssignment N) (v : Triangle) : HoneycombPort :=
  ((v.1,v.2.1),(D.tile (v.1,v.2.1)).representative v.2.2)

lemma representative_projects (D : HoneycombAssignment N) (v : Triangle) :
    portTriangle (D.representative v)=v := by
  rcases v with ⟨i,j,b⟩
  change (i,j,decide (((D.tile (i,j)).representative b).val<2))=(i,j,b)
  rw [Tile.representative_side]

lemma port_to_representative (D : HoneycombAssignment N) {v : HoneycombPort}
    (hv : Graph.Used D.portWiring v) :
    Relation.ReflTransGen D.portWiring v (D.representative (portTriangle v)) :=
  D.tile_reach v.1 (Tile.reach_representative _ (D.physical v.1) _ ((D.port_used v).mp hv))

lemma edge_between_representatives (D : HoneycombAssignment N) {v w : HoneycombPort}
    (h : D.portWiring v w) : Relation.ReflTransGen D.portWiring
      (D.representative (portTriangle v)) (D.representative (portTriangle w)) :=
  ((symm (D.port_to_representative ⟨w,h⟩)).tail h).trans
    (D.port_to_representative ⟨v,D.portWiring_symm h⟩)

lemma up_lifts_edge (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) (w : Triangle)
    (h : D.graph.Adj (up i j) w) :
    Relation.ReflTransGen D.portWiring (D.representative (up i j)) (D.representative w) := by
  rcases (D.up_neighbors i j w).mp h with ⟨hn,⟨rfl,hm⟩ | ⟨rfl,hw⟩ | ⟨hj,rfl,hs⟩⟩
  · exact D.tile_reach (i,j) (Tile.reach_middle _ (D.physical (i,j)) hm)
  · have he : (D.tile (i-1,j)).Occupied 2 := by
      exact (D.horizontal (i-1) j).mpr (by simpa only [sub_add_cancel] using hw)
    exact D.edge_between_representatives (v:=((i,j),1)) (w:=((i-1,j),2))
      (Or.inr (Or.inr (Or.inl ⟨rfl,by dsimp; omega,rfl,rfl,he⟩)))
  · have he : (D.tile (i,j-1)).Occupied 3 := by
      have hn' : j-1+1<N := by omega
      have hh := (D.vertical i (j-1) hn').mpr
      exact hh (by simpa only [show j-1+1=j by omega] using hs)
    exact D.edge_between_representatives (v:=((i,j),0)) (w:=((i,j-1),3))
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,by dsimp; omega,hn,rfl,rfl,he⟩))))

lemma lifts_edge (D : HoneycombAssignment N) {v w : Triangle} (h : D.graph.Adj v w) :
    Relation.ReflTransGen D.portWiring (D.representative v) (D.representative w) := by
  rcases v with ⟨i,j,b⟩
  cases b
  · rcases w with ⟨k,l,b⟩
    cases b
    · have hh := (tileGraph_allowed N D.tile h).1
      simp [adjacent,upDownAdjacent] at hh
    · exact symm (D.up_lifts_edge k l (down i j) (D.graph.symm.symm _ _ h))
  · exact D.up_lifts_edge i j w h



end HoneycombAssignment
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SewnAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace SewnRectangle
variable {n : ℕ}



lemma physical (l r : List (Configuration n))
    (hl : ∀k j, ColumnChain.read l k j≠.verticalPair)
    (hr : ∀k j, ColumnChain.read r k j≠.capCup) (v : Cell) : tile l r v≠.verticalPair := by
  rcases v with ⟨i,j⟩
  by_cases hj : j<n
  · rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · exact (tile_left l r k ⟨j,hj⟩) ▸ hl k ⟨j,hj⟩
    · rw [tile_right l r k ⟨j,hj⟩]
      exact (Tile.physical_horizontal _).mpr (hr k ⟨j,hj⟩)
  · rw [tile_outside l r i j (by omega)]; decide

end SewnRectangle
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Graph

lemma drainsAt_iff {V : Type*} {r : V → V → Prop} {root : V} :
    DrainsAt r root ↔ Patch.drains r (fun v=>v=root) := by
  constructor
  · intro h v w hvw
    exact ⟨root,rfl,h v w hvw⟩
  · intro h v w hvw
    obtain ⟨_,rfl,hr⟩:=h v w hvw
    exact hr

lemma drainsAt_glued_iff {V W I : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (root : W) :
    DrainsAt (Patch.glued r s a b active) (.inr root) ↔
      (∀ v w,r v w → ∃ i,active i ∧ Relation.ReflTransGen r v (a i)) ∧
      DrainsAt (Patch.compressed r s a b active) root := by
  have he : (fun v : V⊕W=>v=Sum.inr root)=Patch.exteriorOutput (fun w=>w=root) := by
    funext v
    cases v <;> simp [Patch.exteriorOutput]
  rw [drainsAt_iff,he,Patch.drains_glued_iff,←drainsAt_iff]

end Graph

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Graph

 

lemma drainsAt_embedding_iff {V W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (f : V → W) (hf : Function.Injective f)
    (he : ∀v w, s (f v) (f w) ↔ r v w)
    (hs : ∀x y, s x y → x∈Set.range f ∧ y∈Set.range f) (root : V) :
    DrainsAt r root ↔ DrainsAt s (f root) := by
  have lift {x y : W} (h : Relation.ReflTransGen s x y) :
      ∀v, x=f v → ∃w, y=f w ∧ Relation.ReflTransGen r v w := by
    induction h with
    | refl => intro v hv; exact ⟨v,hv,.refl⟩
    | @tail y z h hyz ih =>
      intro v hv
      obtain ⟨u,rfl,hu⟩:=ih v hv
      obtain ⟨w,rfl⟩:=(hs _ _ hyz).2
      exact ⟨w,rfl,hu.tail ((he u w).mp hyz)⟩
  constructor
  · intro h x y hxy
    obtain ⟨v,rfl⟩:=(hs x y hxy).1
    obtain ⟨w,rfl⟩:=(hs _ y hxy).2
    exact map_reach f (fun x y h=>.single ((he x y).mpr h)) (h v w ((he v w).mp hxy))
  · intro h v w hvw
    obtain ⟨u,hu,hr⟩:=lift (h (f v) (f w) ((he v w).mpr hvw)) v rfl
    exact (hf hu).symm ▸ hr

end Diagram.Graph

namespace SewnRectangle
variable {n : ℕ}


lemma horizontalPort_eq (a b : Fin 4) :
    Tile.horizontalPort a=b ↔ a=Tile.horizontalPort b := by
  revert a b; decide

end SewnRectangle
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FiniteEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram.PathGraph
noncomputable section
open scoped Classical



lemma degree_eq_one_of_single {V : Type*} [Fintype V] (G : SimpleGraph V) {a : V}
    (ha : AtMostOne G.Adj a) (hu : Graph.Used G.Adj a) : G.degree a=1 := by
  obtain ⟨b,hb⟩ := hu
  rw [←G.card_neighborFinset_eq_degree]
  have he : G.neighborFinset a={b} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    exact ⟨fun h=>ha h hb,fun h=>h ▸ hb⟩
  rw [he,Finset.card_singleton]

lemma degree_eq_two_of_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h₂ : AtMostTwo G.Adj) {v : V} (hv : ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y) :
    G.degree v=2 := by
  obtain ⟨x,y,hx,hy,hxy⟩ := hv
  rw [←G.card_neighborFinset_eq_degree]
  have he : G.neighborFinset v={x,y} := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨fun h=>h₂ hx hy h hxy,fun h=>h.elim (fun h=>h ▸ hx) (fun h=>h ▸ hy)⟩
  simp [he,hxy]

 

lemma endpoints_connected {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h₂ : AtMostTwo G.Adj) {a b : V} (ha : AtMostOne G.Adj a)
    (hu : Graph.Used G.Adj a)
    (hi : ∀ v, v≠a → v≠b → Graph.Used G.Adj v →
      ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y) : G.Reachable a b := by
  apply reachable_of_odd_terminals G
  · rw [degree_eq_one_of_single G ha hu]
    exact odd_one
  · intro v hv
    by_cases hva : v=a
    · exact Or.inl hva
    by_cases hvb : v=b
    · exact Or.inr hvb
    exfalso
    by_cases hu : Graph.Used G.Adj v
    · rw [degree_eq_two_of_two G h₂ (hi v hva hvb hu)] at hv
      exact (by decide : ¬Odd (2:ℕ)) hv
    · have hz : G.degree v=0 := by
        rw [SimpleGraph.degree_eq_zero]
        intro w hw
        exact hu ⟨w,hw⟩
      rw [hz] at hv
      exact (by decide : ¬Odd (0:ℕ)) hv

 

lemma endpoints_connected_finite_support {V : Type*} (G : SimpleGraph V)
    (hf : G.support.Finite) (h₂ : AtMostTwo G.Adj) {a b : V}
    (ha : AtMostOne G.Adj a) (hu : Graph.Used G.Adj a)
    (hi : ∀ v, v≠a → v≠b → Graph.Used G.Adj v →
      ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y) :
    Relation.ReflTransGen G.Adj a b := by
  
  let S : Set V := insert b G.support
  have hs : S.Finite := hf.insert b
  let := hs.fintype
  let H := G.induce S
  let a' : S := ⟨a,Set.mem_insert_of_mem b hu⟩
  let b' : S := ⟨b,Set.mem_insert b _⟩
  have h₂' : AtMostTwo H.Adj := by
    intro v x y z hx hy hz hxy
    rcases h₂ hx hy hz (fun h=>hxy (Subtype.ext h)) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have ha' : AtMostOne H.Adj a' := by
    intro x y hx hy
    exact Subtype.ext (ha hx hy)
  have hu' : Graph.Used H.Adj a' := by
    obtain ⟨w,hw⟩:=hu
    exact ⟨⟨w,Set.mem_insert_of_mem b ⟨a,G.symm.symm _ _ hw⟩⟩,hw⟩
  have hi' : ∀ v : S, v≠a' → v≠b' → Graph.Used H.Adj v →
      ∃ x y, H.Adj v x ∧ H.Adj v y ∧ x≠y := by
    intro v hva hvb hv
    have hv' : Graph.Used G.Adj v.val := by
      obtain ⟨w,hw⟩:=hv
      exact ⟨w.val,hw⟩
    obtain ⟨x,y,hx,hy,hxy⟩:=hi v (fun h=>hva (Subtype.ext h))
      (fun h=>hvb (Subtype.ext h)) hv'
    let x' : S := ⟨x,Set.mem_insert_of_mem b ⟨v,G.symm.symm _ _ hx⟩⟩
    let y' : S := ⟨y,Set.mem_insert_of_mem b ⟨v,G.symm.symm _ _ hy⟩⟩
    exact ⟨x',y',hx,hy,fun h=>hxy (congrArg Subtype.val h)⟩
  have hr := (SimpleGraph.reachable_iff_reflTransGen (G := H) a' b').mp
    (endpoints_connected H h₂' ha' hu' hi')
  exact Graph.map_reach Subtype.val (fun _ _ h=>.single h) hr

 

lemma drains_of_two_terminals {V : Type*} (G : SimpleGraph V)
    (hf : G.support.Finite) (h₂ : AtMostTwo G.Adj) {a b : V}
    (ha : AtMostOne G.Adj a) (hu : Graph.Used G.Adj a)
    (hi : ∀ v, v≠a → v≠b → Graph.Used G.Adj v →
      ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x≠y)
    (hd : ∀ v w, G.Adj v w → Relation.ReflTransGen G.Adj v a ∨
      Relation.ReflTransGen G.Adj v b) : Graph.DrainsAt G.Adj a := by
  have := G.symm
  have hr:=endpoints_connected_finite_support G hf h₂ ha hu hi
  intro v w hvw
  exact (hd v w hvw).elim id (fun hv=>hv.trans (symm hr))

end
end CriticalStrip.Diagram.PathGraph

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram Diagram.PathGraph

namespace HoneycombAssignment
variable {N M : ℕ}



lemma restrict_adj (D : HoneycombAssignment N) (M : ℕ) (hM : M≤N) (v w : Triangle) :
    (D.restrict M hM).graph.Adj v w ↔
      v.2.1<M ∧ w.2.1<M ∧ D.graph.Adj v w := by
  by_cases hv : v.2.1<M
  · by_cases hw : w.2.1<M
    · have hvN : v.2.1<N := lt_of_lt_of_le hv hM
      have hwN : w.2.1<N := lt_of_lt_of_le hw hM
      simp only [graph,tileGraph,hv,hw,hvN,hwN,true_and,upDownWire,
        restrict_tile D M hM v.1 v.2.1 hv,restrict_tile D M hM w.1 w.2.1 hw]
    · simp only [graph,tileGraph,hw,and_false,hv,false_and]
  · simp only [graph,tileGraph,hv,false_and]

end HoneycombAssignment
end

 

 

noncomputable section
open scoped Classical
open Diagram

namespace Diagram.ColumnChain
variable {n : ℕ}

lemma read_map (ts : List (Configuration n)) (k : ℕ) (i : Fin n) :
    read ts k i=((ts.map (fun t=>t i))[k]?).getD Tile.vacant := by
  simp only [read,List.getElem?_map]
  cases ts[k]? <;> rfl

lemma north_shape_read (ts : List (Configuration (n+1))) (k l : ℕ)
    (h : ts.map (fun t=>t (Fin.last n))=
      List.replicate k Tile.diagonal₁ ++ Tile.vertical₀::List.replicate l Tile.vacant)
    (j : ℕ) : read ts j (Fin.last n)=
      if j<k then Tile.diagonal₁ else if j=k then Tile.vertical₀ else Tile.vacant := by
  rw [read_map,h,List.getElem?_append,List.length_replicate]
  split_ifs with hj hjk
  · rw [List.getElem?_replicate,ite_eq_left hj]; rfl
  · subst j
    simp
  · have hpos : 0<j-k := by omega
    have he : j-k=(j-k-1)+1 := by omega
    rw [he,List.getElem?_cons_succ,List.getElem?_replicate]
    split <;> rfl

end Diagram.ColumnChain

namespace SewnRectangle
variable {n : ℕ}

lemma north_south_occupied (l r : List (Configuration (n+1))) (kl ll kr lr : ℕ)
    (hl : l.map (fun t=>t (Fin.last n))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hr : r.map (fun t=>t (Fin.last n))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant)
    (i : ℤ) : (tile l r (i,n)).Occupied 0 ↔ i= -1-(kl:ℤ) ∨ i=(kr:ℤ) := by
  rcases split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
  · rw [show tile l r (-1-(k:ℤ),n)=ColumnChain.read l k (Fin.last n) from tile_left l r k (Fin.last n),ColumnChain.north_shape_read l kl ll hl k]
    split_ifs with hk he
    · have hc : ¬-1-(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬-1-(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide
    · subst k
      simp only [true_or]
      decide
    · have hc : ¬-1-(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬-1-(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide
  · rw [show tile l r ((k:ℤ),n)=(ColumnChain.read r k (Fin.last n)).horizontal from tile_right l r k (Fin.last n),Tile.horizontal_occupied_zero,
      ColumnChain.north_shape_read r kr lr hr k]
    split_ifs with hk he
    · have hc : ¬(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide
    · subst k
      simp only [or_true]
      decide
    · have hc : ¬(k:ℤ)= -1-(kl:ℤ) := by omega
      have hc' : ¬(k:ℤ)=(kr:ℤ) := by omega
      simp only [hc,hc',false_or]
      decide

end SewnRectangle
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical






namespace BoundaryInsert
variable {n m : ℕ}


lemma cover (k : ℕ) (hk : k≤n) (i : Fin (n+m)) :
    (∃ j,old k hk j=i) ∨ (∃ j,fresh k hk j=i) := by
  by_cases hi : i.val<k
  · left
    refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    change (if i.val<k then i.val else i.val+m)=i.val
    simp [hi]
  · by_cases hj : i.val<k+m
    · right
      refine ⟨⟨i.val-k,by omega⟩,?_⟩
      apply Fin.ext
      change k+(i.val-k)=i.val
      omega
    · left
      refine ⟨⟨i.val-m,by omega⟩,?_⟩
      apply Fin.ext
      change (if i.val-m<k then i.val-m else i.val-m+m)=i.val
      rw [ite_eq_right (by omega)]
      omega

 

lemma not_cross (k : ℕ) (hk : k≤n) (a b : Fin n) (i j : Fin m) :
    ¬Pairing.Cross (old k hk a) (old k hk b) (fresh k hk i) (fresh k hk j) := by
  change ¬Pairing.Cross
    (⟨if a.val<k then a.val else a.val+m, _⟩ : Fin (n+m))
    ⟨if b.val<k then b.val else b.val+m, _⟩ ⟨k+i.val, _⟩ ⟨k+j.val, _⟩
  simp only [Pairing.Cross,Fin.lt_def]
  split_ifs <;> omega


end BoundaryInsert
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundaryInsert
variable {n m : ℕ}

def equiv (k : ℕ) (hk : k≤n) : (Fin n ⊕ Fin m) ≃ Fin (n+m) :=
  Equiv.ofBijective (Sum.elim (old k hk) (fresh k hk)) ⟨by
    rintro (i|i) (j|j) h
    · exact congrArg Sum.inl ((old k hk).injective h)
    · exact (disjoint k hk i j h).elim
    · exact (disjoint k hk j i h.symm).elim
    · exact congrArg Sum.inr ((fresh k hk).injective h),by
    intro i
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk i
    · exact ⟨.inl j,rfl⟩
    · exact ⟨.inr j,rfl⟩⟩

@[simp] lemma equiv_old (k : ℕ) (hk : k≤n) (i : Fin n) :
    equiv (m:=m) k hk (.inl i)=old k hk i := rfl
@[simp] lemma equiv_fresh (k : ℕ) (hk : k≤n) (i : Fin m) :
    equiv (m:=m) k hk (.inr i)=fresh k hk i := rfl

def boundary {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V) (b : Fin m → W) :
    Fin (n+m) → (V ⊕ W) := fun i=>Sum.map a b ((equiv k hk).symm i)

@[simp] lemma boundary_old {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (i : Fin n) :
    boundary k hk a b (old k hk i)=.inl (a i) := by
  change Sum.map a b ((equiv k hk).symm (equiv k hk (.inl i)))=_
  simp only [Equiv.symm_apply_apply,Sum.map_inl]

@[simp] lemma boundary_fresh {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (i : Fin m) :
    boundary k hk a b (fresh k hk i)=.inr (b i) := by
  change Sum.map a b ((equiv k hk).symm (equiv k hk (.inr i)))=_
  simp only [Equiv.symm_apply_apply,Sum.map_inr]

def gauge (k : ℕ) (hk : k≤n) (g : Fin n → ℤ) (h : Fin m → ℤ) : Fin (n+m) → ℤ :=
  fun i=>Sum.elim g h ((equiv k hk).symm i)

@[simp] lemma gauge_old (k : ℕ) (hk : k≤n) (g : Fin n → ℤ) (h : Fin m → ℤ) (i : Fin n) :
    gauge k hk g h (old k hk i)=g i := by
  change Sum.elim g h ((equiv k hk).symm (equiv k hk (.inl i)))=_
  simp only [Equiv.symm_apply_apply,Sum.elim_inl]
@[simp] lemma gauge_fresh (k : ℕ) (hk : k≤n) (g : Fin n → ℤ) (h : Fin m → ℤ) (i : Fin m) :
    gauge k hk g h (fresh k hk i)=h i := by
  change Sum.elim g h ((equiv k hk).symm (equiv k hk (.inr i)))=_
  simp only [Equiv.symm_apply_apply,Sum.elim_inr]

end BoundaryInsert






namespace BoundaryErase
variable {n : ℕ}

abbrev keep (k : ℕ) (hk : k≤n) : Fin n ↪o Fin (n+2) := BoundaryInsert.old k hk
abbrev left (k : ℕ) (hk : k≤n) : Fin (n+2) := BoundaryInsert.fresh k hk 0
abbrev right (k : ℕ) (hk : k≤n) : Fin (n+2) := BoundaryInsert.fresh k hk 1

lemma adjacent (k : ℕ) (hk : k≤n) : (left k hk).val+1=(right k hk).val := by
  change (k+0)+1=k+1
  omega

lemma keep_ne_left (k : ℕ) (hk : k≤n) (i : Fin n) : keep k hk i≠left k hk :=
  BoundaryInsert.disjoint k hk i 0
lemma keep_ne_right (k : ℕ) (hk : k≤n) (i : Fin n) : keep k hk i≠right k hk :=
  BoundaryInsert.disjoint k hk i 1

end BoundaryErase

namespace BoundarySew
section Wiring
variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {old : Fin (n+2) → V}

 

def tile (active : Prop) : Tile := if active then .cap else .vacant

end Wiring






end BoundarySew
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnWideGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundaryInsert
variable {n m : ℕ}

@[simp] lemma old_val (k : ℕ) (hk : k≤n) (i : Fin n) :
    (old (m:=m) k hk i).val=(if i.val<k then i.val else i.val+m) := rfl
@[simp] lemma fresh_val (k : ℕ) (hk : k≤n) (i : Fin m) :
    (fresh k hk i).val=k+i.val := rfl

end BoundaryInsert

end
end CriticalStrip.Diagram

end OAI
end


