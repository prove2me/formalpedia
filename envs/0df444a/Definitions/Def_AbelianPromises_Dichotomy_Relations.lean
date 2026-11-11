-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Relations
-- name    : AbelianPromises_Dichotomy_Relations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:54.15382+00:00
-- url     : https://prove2.me/theorems/92493ba5-5e7f-4fdc-b4b1-522745dba8db
-- title:
--   Ternary relations, actual domains and finite constraint instances
-- statement:
--   A relation R is a set of ordered triples. Its actual domain is the set of values appearing in its triples; the empty relation has empty domain. Homomorphisms map actual domains and preserve each ordered triple. A finite instance lists all n variables, including isolated variables, and lists ordered constraints; repeated coordinates and duplicate constraints are allowed. Duplicate constraints impose the same satisfaction condition as a set of constraints.
--
--   For an Abelian group G and c colours, the defining relations are
--   $$
--   \operatorname{Eqn}(G)=\{(x,y,z):x+y+z=0\},\quad
--   \operatorname{Eqn}^*(G)=\{(x,y,z):x+y+z=0,\ \neg(x=y=z)\},\quad
--   \operatorname{NAE}_c=\{(a,b,d)\in[c]^3:\neg(a=b=d)\}.
--   $$
--   An R-solution assigns a value in the actual domain to each variable and preserves every constraint. Induction of a relation keeps precisely tuples wholly in the specified subset. The zero restriction uses the fibre of the specified q over zero. These definitions are shared by every target in the mission.
--
--   **Formalization Note** Source colour i+1 is represented by i in Fin c. The published relational-structure, instance and satisfaction primitives are reused; actual domains are explicit subtypes. No nonemptiness or symmetry is imposed by these primitives.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, Abelian embeddings make useful promises: approximation of detrivialised equations, STOC 2027 submission #967 (October 2026), printed p. 5 (PDF p. 6), §2; Definition 1.3

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

set_option autoImplicit false

namespace AbelianPromises.Dichotomy

open PCSPBLPAff.Symmetric

/-- One ternary relation, using the published relational-structure interface. -/
abbrev Relation (A : Type) := RelStruct Unit (fun _ => 3) A

/-- The source's domain consists precisely of entries occurring in tuples. -/
def Carrier {A : Type} (R : Relation A) :=
  {a : A // ∃ t ∈ R.rel (), ∃ i : Fin 3, t i = a}

/-- The same relation on its actual domain, including the empty domain. -/
def actual {A : Type} (R : Relation A) : Relation (Carrier R) where
  rel _ := {t | (fun i => (t i).val) ∈ R.rel ()}

def Hom {A B : Type} (R : Relation A) (Q : Relation B) : Prop :=
  IsPromiseTemplate (actual R) (actual Q)

def induced {A : Type} (R : Relation A) (S : Set A) : Relation A where
  rel _ := {t | t ∈ R.rel () ∧ ∀ i, t i ∈ S}

def nae (c : ℕ) : Relation (Fin c) where
  rel _ := {t | ¬ (t 0 = t 1 ∧ t 1 = t 2)}

def eqn (G : Type) [AddCommGroup G] : Relation G where
  rel _ := {t | t 0 + t 1 + t 2 = 0}

def eqnStar (G : Type) [AddCommGroup G] : Relation G where
  rel _ := {t | t 0 + t 1 + t 2 = 0 ∧ ¬ (t 0 = t 1 ∧ t 1 = t 2)}

def zeroRelation {A G : Type} [Zero G] (R : Relation A) (q : Carrier R → G) :
    Relation (Carrier R) := induced (actual R) {a | q a = 0}

/-- All finite variables, including isolated ones; scopes may repeat variables. -/
abbrev Instance := PCSPBLPAff.Symmetric.Instance Unit (fun _ => 3)

def Satisfiable {A : Type} (I : Instance) (R : Relation A) : Prop :=
  SatIn I (actual R)

/-- Exact order exclusions, with no restriction on the group size. -/
def NoSmallOrders (G : Type) [AddCommGroup G] : Prop :=
  (∀ g : G, addOrderOf g ≠ 2) ∧ (∀ g : G, addOrderOf g ≠ 3)

end AbelianPromises.Dichotomy


