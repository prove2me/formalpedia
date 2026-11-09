-- Prove2me | Definitions.Def_QECDecodingHardness_AllThree_gadgets
-- name    : QECDecodingHardness_AllThree_gadgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:39.728821+00:00
-- url     : https://prove2.me/theorems/9c106c5d-66a8-4bbd-9f6c-fc056d9a9b16
-- title:
--   Gadget neighborhoods, signed excess, partner separation and connected covers
-- statement:
--   Let a finite check system be equipped with disjoint nonempty blocks of checks representing defects, each with one of three type labels. An ordinary defect has its Tanner 1-neighborhood; a combined surface-code Y defect has its 2-neighborhood. Thus an error location lies in a k-neighborhood precisely when a Tanner walk of length at most 2k-1 reaches it from a constituent check.
--
--   A gadget g has a defect set, a subset of nodes, and a cover. Covers are allowed errors whose syndrome contains all of g; their syndrome may also contain other checks. Its neighborhood R_g is the union of the defect neighborhoods. Its excess is the signed integer
--
--   $$m_g=\min_{e:\ e\text{ covers }g}|\operatorname{supp}(e)\cap R_g|-|g|.$$
--
--   The minimum is a least attained natural weight, constructed with an explicit cover witness. There is no minimum of an empty set. For a disjoint gadget family, let R be the union of all R_g. A minimal cover both attains the displayed local minimum and is supported in R, rather than necessarily in R_g.
--
--   Assumption 2 is represented by disjoint gadget neighborhoods, no adjacency between different gadgets except at nodes, and exactly one adjacent same-type partner for each node. Components of an error are computed on supported locations using next-nearest Tanner adjacency. The connected cover of g is the restriction of the original error to the union of components touching g. For a global error with the prescribed syndrome, this is the smallest union of its components covering g.
--
--   Isolation means every Tanner walk between constituent checks of distinct defects has length at least four. The presentation permits general disjoint check blocks and local binary systems for the two counting lemmas; it imposes no truth tables, concrete reduction, or hardness assumption.
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), pp.5,7–8, Tanner graph, gadget definitions, Eq. (1), Assumption 2; p.10, Lemma 6

import Definitions.Def_QECDecodingHardness_AllThree_check_system

noncomputable section

namespace QECDecodingHardness.AllThree

open Classical

/-- A defect is one check, or a combined Y defect's two checks. General block
presentations are allowed for the abstract counting lemmas. Disjoint nonempty
blocks prevent duplicate counting. Only a combined Y defect uses radius two.
This presentation carries no claims about gadget covers or truth values. -/
structure DefectPresentation (S : CheckSystem) where
  count : ℕ
  block : Fin count → Finset (Fin S.checks)
  nonempty : ∀ p, (block p).Nonempty
  disjoint : ∀ p q, p ≠ q → Disjoint (block p) (block q)
  kind : Fin count → Fin 3
  combinedY : Fin count → Bool

/-- Tanner k-neighborhood: error locations at distance at most 2k-1.
Walks avoid the zero-on-disconnected-input convention of graph `dist`. -/
def defectNeighborhood {S : CheckSystem} (D : DefectPresentation S)
    (p : Fin D.count) : Finset (Fin S.locations) :=
  Finset.univ.filter (fun q => ∃ c ∈ D.block p,
    ∃ w : (tannerGraph S).Walk (Sum.inr c) (Sum.inl q),
      w.length ≤ if D.combinedY p then 3 else 1)

def gadgetNeighborhood {S : CheckSystem} (D : DefectPresentation S)
    (g : Finset (Fin D.count)) : Finset (Fin S.locations) :=
  g.biUnion (defectNeighborhood D)

/-- A cover contains every constituent check of every defect, with no restriction
on other syndrome checks. It is an allowed physical fault assignment. -/
def Covers {S : CheckSystem} (D : DefectPresentation S)
    (g : Finset (Fin D.count)) (e : Error S) : Prop :=
  Allowed S e ∧ ∀ p ∈ g, ∀ c ∈ D.block p, syndrome S e c = 1

/-- Gadgets in Section III, p.7. Cover existence is the well-definedness condition
implicit in Eq.(1), not a local truth table or a reduction-correctness premise.
It is used only in the abstract lemmas, never as a hypothesis of Theorem 1. -/
structure Gadget {S : CheckSystem} (D : DefectPresentation S) where
  defects : Finset (Fin D.count)
  nodes : Finset (Fin D.count)
  nodes_subset : nodes ⊆ defects
  coverExists : ∃ e : Error S, Covers D defects e

def localWeight {S : CheckSystem} (D : DefectPresentation S)
    (g : Gadget D) (e : Error S) : ℕ :=
  (errorSupport e ∩ gadgetNeighborhood D g.defects).card

/-- Least attained local covering weight. `Nat.find` is applied only with an
explicit witness. There is no empty-set minimum or default infinite value. -/
def minimumLocalWeight {S : CheckSystem} (D : DefectPresentation S)
    (g : Gadget D) : ℕ :=
  Nat.find (show ∃ n : ℕ, ∃ e : Error S, Covers D g.defects e ∧ localWeight D g e = n from by
    obtain ⟨e, he⟩ := g.coverExists
    exact ⟨localWeight D g e, e, he, rfl⟩)

/-- Eq.(1), p.7. Integer subtraction preserves the surface gadgets' -1 excess. -/
def errorExcess {S : CheckSystem} (D : DefectPresentation S) (g : Gadget D) : ℤ :=
  (minimumLocalWeight D g : ℤ) - (g.defects.card : ℤ)

structure GadgetFamily {S : CheckSystem} (D : DefectPresentation S) where
  count : ℕ
  gadget : Fin count → Gadget D
  defects_disjoint : ∀ i j, i ≠ j → Disjoint (gadget i).defects (gadget j).defects

def allDefects {S : CheckSystem} {D : DefectPresentation S} (F : GadgetFamily D) :=
  Finset.univ.biUnion (fun i => (F.gadget i).defects)

def allNeighborhoods {S : CheckSystem} {D : DefectPresentation S} (F : GadgetFamily D) :=
  Finset.univ.biUnion (fun i => gadgetNeighborhood D (F.gadget i).defects)

def gadgetSyndrome {S : CheckSystem} {D : DefectPresentation S}
    (F : GadgetFamily D) : Syndrome S :=
  fun c => if c ∈ (allDefects F).biUnion D.block then 1 else 0

def totalExcess {S : CheckSystem} {D : DefectPresentation S} (F : GadgetFamily D) : ℤ :=
  ∑ i, errorExcess D (F.gadget i)

def NeighborhoodsAdjacent {S : CheckSystem} (D : DefectPresentation S)
    (p q : Fin D.count) : Prop :=
  ∃ u ∈ defectNeighborhood D p, ∃ v ∈ defectNeighborhood D q, ErrorAdjacent S u v

/-- Partners are computed from the geometric neighborhoods, not chosen to make
truth tables true. The relation is symmetric and concerns different gadgets. -/
def PartnerNodes {S : CheckSystem} {D : DefectPresentation S} (F : GadgetFamily D)
    (i : Fin F.count) (p : Fin D.count) (j : Fin F.count) (q : Fin D.count) : Prop :=
  i ≠ j ∧ p ∈ (F.gadget i).nodes ∧ q ∈ (F.gadget j).nodes ∧
    NeighborhoodsAdjacent D p q

/-- Assumption 2, p.7: disjoint neighborhoods, no adjacency across gadgets
except nodes, and exactly one same-type partner for each node. Distance here
is the error-location adjacency induced by the bipartite Tanner graph. -/
def SeparatedGadgets {S : CheckSystem} {D : DefectPresentation S}
    (F : GadgetFamily D) : Prop :=
  (∀ i j, i ≠ j → Disjoint (gadgetNeighborhood D (F.gadget i).defects)
    (gadgetNeighborhood D (F.gadget j).defects)) ∧
  (∀ i j, i ≠ j → ∀ p ∈ (F.gadget i).defects, ∀ q ∈ (F.gadget j).defects,
    NeighborhoodsAdjacent D p q → p ∈ (F.gadget i).nodes ∧ q ∈ (F.gadget j).nodes ∧
      D.kind p = D.kind q) ∧
  (∀ i, ∀ p ∈ (F.gadget i).nodes, ∃! jq : Fin F.count × Fin D.count,
    PartnerNodes F i p jq.1 jq.2 ∧ D.kind p = D.kind jq.2)

def MinimalCover {S : CheckSystem} {D : DefectPresentation S}
    (F : GadgetFamily D) (i : Fin F.count) (e : Error S) : Prop :=
  Covers D (F.gadget i).defects e ∧
    localWeight D (F.gadget i) e = minimumLocalWeight D (F.gadget i) ∧
    errorSupport e ⊆ allNeighborhoods F

/-- Components are formed on supported locations with next-nearest Tanner adjacency. -/
def SupportedStep {S : CheckSystem} (e : Error S) (q r : Fin S.locations) : Prop :=
  q ∈ errorSupport e ∧ r ∈ errorSupport e ∧ ErrorAdjacent S q r

/-- Union of the components of E touching any constituent check of g; restriction
retains each original Pauli, including Y. When E has the prescribed syndrome,
this is exactly the smallest union of E-components covering g, since different
components cannot touch the same check. No unrelated cover is quantified in its place. -/
def connectedCover {S : CheckSystem} (D : DefectPresentation S)
    (g : Gadget D) (e : Error S) : Error S :=
  fun q => if q ∈ errorSupport e ∧
    (∃ r ∈ errorSupport e, (∃ p ∈ g.defects, ∃ c ∈ D.block p, Incident S r c) ∧
      Relation.ReflTransGen (SupportedStep e) r q) then e q else 0

/-- All inter-defect Tanner distances are at least four. For combined blocks,
this means every constituent check of one is at least four from every constituent
of the other. Disconnected pairs have infinite distance and meet this condition. -/
def IsolatedDefects {S : CheckSystem} (D : DefectPresentation S) (g : Gadget D) : Prop :=
  ∀ p ∈ g.defects, ∀ q ∈ g.defects, p ≠ q →
    ∀ c ∈ D.block p, ∀ d ∈ D.block q,
      ∀ w : (tannerGraph S).Walk (Sum.inr c) (Sum.inr d), 4 ≤ w.length

end QECDecodingHardness.AllThree


