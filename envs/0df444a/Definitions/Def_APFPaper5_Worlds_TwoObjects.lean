-- Prove2me | Definitions.Def_APFPaper5_Worlds_TwoObjects
-- name    : APFPaper5_Worlds_TwoObjects
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:52:48.641982+00:00
-- url     : https://prove2.me/theorems/39da367f-d270-4795-8128-43e20e290804
-- title:
--   Two-state data and eight supplied input forms
-- statement:
--   Defines small Boolean worlds, a single protocol with bill one, shared record data, and a conjunction of the eight declared predicates on supplied arguments. EightHoldOn uses freely supplied Cont, a singleton A2 admissible set, vacuous support novelty, and a supplied joint class. It is not an instance certificate for the physical foundation or corrected word semantics.
--
--   **Meaning and scope.** Defines small Boolean worlds, a single protocol with bill one, shared record data, and a conjunction of the eight declared predicates on supplied arguments. Fidelity exposure: EightHoldOn uses freely supplied Cont, a singleton A2 admissible set, vacuous support novelty, and a supplied joint class. It is not an instance certificate for the physical foundation or corrected word semantics.
--
--   **Supplied data and hypotheses**
--
--   - All explicit/implicit parameters and hypotheses in the exact declaration inventory below, together with the recorded module variable and typeclass context. EightHoldOn uses freely supplied Cont, a singleton A2 admissible set, vacuous support novelty, and a supplied joint class. It is not an instance certificate for the physical foundation or corrected word semantics.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_Worlds_TwoObjects.lean; Sib v44 / pullbacks v1, SHA-256 c4a7072d6a671f88e541ba78e1021c1714d9757494def4e27e10650331857df2. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1224-1241,1774-1887,2197-2223,2624-2626,3188-3230,7090-7110'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '1617-1657,3034-3075; K clauses remain supplied physical obligations'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_Worlds_TwoObjects
title: Supplied data for small worlds with two raw states, and the eight declared forms stated on that data
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the eight declared-input definition nodes, unchanged (B01, B02, B03 r2, B04, B05 r2, B06, B07a, B07b).
standing: a supplied MODEL used only to test what the declared forms do not decide. It is not a physical
 instance and certifies nothing about the physical inputs.
statement: two raw states (Bool); processes are words (List Bool); one protocol, the word [true]; one record;
 one distinction, the one that tells the two raw states apart; every bill is 1; capacity 2. EightHoldOn Cont
 is the conjunction of the eight declared forms on this data, with the same continuation relation Cont in
 B01, B02 and B06, the same protocol, record and bill data in B02, B03, B05 and B06, and the realized
 configuration of A2 and BW taken to be the physical object of the raw state true.
 contU, afterU: the raw state true admits every word; false admits every word not beginning with false;
 after any nonempty word the state is true.
 contS, afterS: true admits every word; false admits only the empty word; a word leaves the state as it is.
-/
import Definitions.Def_APF_B01_DeclaredInput
import Definitions.Def_APF_B02_DeclaredInput
import Definitions.Def_APF_B03_DeclaredInput_r2
import Definitions.Def_APF_B04_DeclaredInput
import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput

set_option autoImplicit false
namespace APFPaper5.Worlds

/-- The protocols: the one word [true]. -/
abbrev Proto : Type := {p : List Bool // p ∈ ({[true]} : Set (List Bool))}

/-- The distinctions: the one that tells the two raw states apart. -/
abbrev Dist : Type := {d : Bool → Bool // d = id}

instance : DecidableEq Dist := fun a b => isTrue (Subtype.ext (a.2.trans b.2.symm))

def proto0 : Proto := ⟨[true], rfl⟩

def wholeRes (_ : Unit) (_ : Proto) : Unit := ()

def calib (_ : Unit) (_ : Unit) : NNReal := 1

def maint (_ : Unit) (_ : Proto) : Set Unit := Set.univ

def suff (_ : Unit) (_ : Proto) (_ : Set Unit) (_ : Dist) : Prop := True

def uses (_ : Unit) (_ : Proto) (_ : Dist) (_ : Set Unit) : Prop := True

/-- The eight declared forms on the supplied data, sharing one continuation relation. -/
def EightHoldOn (Cont : Bool → List Bool → Prop) : Prop :=
  APF_B01_DeclaredInput Cont
      (fun (f : APFB01.PhysicalState Cont → Prop) (x : Bool) => f (APFB01.physicalClass Cont x))
      (fun (f : APFB01.PhysicalState Cont → Prop) (x : Bool) => f (APFB01.physicalClass Cont x))
      (fun (f : APFB01.PhysicalState Cont → Prop) (x : Bool) => f (APFB01.physicalClass Cont x))
      (fun (f : APFB01.PhysicalState Cont → Prop) (x : Bool) => f (APFB01.physicalClass Cont x)) ∧
    APFB02.B02SourceMeaning (Context := Unit) (X := fun _ => Bool) (Q := fun _ => List Bool)
      (P := fun _ => Proto) (Record := fun _ => Unit)
      (fun _ => Cont) (fun _ d => d = id) maint suff uses ∧
    APFB03.B03TaskCost (Context := Unit) (D := fun _ => Dist) (P := fun _ => Proto)
      (R := fun _ => Unit) (Record := fun _ => Unit) wholeRes calib maint suff uses ∧
    APFB04.B04FiniteCapacity (Context := Unit) (fun _ => (2 : ℝ)) ∧
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => Dist) (P := fun _ => Proto)
      (R := fun _ => Unit) (Record := fun _ => Unit) wholeRes calib maint suff uses
      (fun _ _ => True) (fun _ => 2) (fun _ => 1) ∧
    (∃ (D : Unit → Set (APFB01.PhysicalState Cont → Bool))
        (actualJoint : Set (Sigma fun g : Unit => APFB06.OriginalAlignment Cont (D g))),
      APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Bool)
        (FullProcess := fun _ => List Bool) (Resource := fun _ => Unit)
        (fun _ => Cont) D (fun _ => ({[true]} : Set (List Bool))) (fun _ _ => Set.univ)
        wholeRes calib (fun _ => (2 : NNReal)) actualJoint) ∧
    APFB07a.A2Selection (Interface := Unit) (Configuration := fun _ => APFB01.PhysicalState Cont)
      (fun _ s => s = APFB01.physicalClass Cont true) (fun _ _ => (1 : ℝ))
      (fun _ => APFB01.physicalClass Cont true) ∧
    APFB07b.BWUniqueMinimum (Interface := Unit)
      (Configuration := fun _ => APFB01.PhysicalState Cont)
      (fun _ s => s = APFB01.physicalClass Cont true) (fun _ _ => (1 : ℝ))

/-- World U. The raw state true admits every word; false admits every word not beginning with false. -/
def contU (x : Bool) (w : List Bool) : Prop := x = true ∨ w.head? ≠ some false

/-- World U. After any nonempty word the state is true. -/
def afterU (x : Bool) (u : List Bool) : Bool := if u = [] then x else true

/-- World S. The raw state true admits every word; false admits only the empty word. -/
def contS (x : Bool) (w : List Bool) : Prop := x = true ∨ w = []

/-- World S. A word leaves the state as it is. -/
def afterS (x : Bool) (_ : List Bool) : Bool := x

end APFPaper5.Worlds


