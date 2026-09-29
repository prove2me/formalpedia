-- Prove2me | Definitions.Def_AlgebraicCurve_AffinoidCentre
-- name    : AlgebraicCurve_AffinoidCentre
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/bd2e1c3f-db42-5bbd-b8e5-1a9bbb2bea45
-- title:
--   Tube-bounded functions, affinoid lifting, holomorphy rings, centres of charts
-- statement:
--   Throughout, $L$ is a field with a valuation subring $A$, $F$ is a field extension of $L$, and $\bar F$ is a field extension of the residue field $\kappa = \mathrm{ResidueField}(A)$; $C$ is a `ComponentChart A F Fbar`, that is, a valuation subring `C.integers` of $F$ together with a surjective ring map `C.residue` onto $\bar F$ with kernel the maximal ideal, a set `C.dom` of places of $F/L$, a finite set `C.nodes` of places of $\bar F/\kappa$, a map `C.placeMap` from places of $F/L$ to places of $\bar F/\kappa$ avoiding the nodes on `C.dom`, and the compatibility axioms of that structure. Four notions are defined, plus a subring.
--
--   `ComponentChart.tubeBounded C f` says that for every place $P \in C.\mathrm{dom}$ one has $f \in \mathcal{O}_P$ and the value $P.\mathrm{evalAt}\, f$ lies in $A$. `ComponentChart.HasAffinoidLifting C N`, for a finite set $N$ of places of $\bar F/\kappa$, is the conjunction of: every tube-bounded $f$ lies in `C.integers`; every $g \in \bar F$ lying in $\mathcal{O}_Q$ for all $Q \notin N$ is the residue of some tube-bounded element of `C.integers`; and every $h \in$ `C.integers` can be written as $h = r/s$ with $r, s$ tube-bounded, $s \in$ `C.integers` and residue of $s$ non-zero (stated as $h\,s = r$). `ComponentChart.regOff N` is the subring $\bigcap_{Q \notin N} \mathcal{O}_Q$ of $\bar F$, formed as a lattice infimum of subrings. `ComponentChart.HasPlaceDictionary N` asserts a bijection between the maximal ideals of `regOff N` and the places $Q \notin N$: each maximal ideal $\mathfrak{m}$ has a unique such $Q$ with $g \in \mathfrak{m}$ iff $g = 0$ or $\mathrm{ord}_Q(g) > 0$, and every $Q \notin N$ arises from some maximal ideal so described. Finally `ComponentChart.IsCentre C N O Q`, for a valuation subring $O$ of $F$ and a place $Q$ of $\bar F/\kappa$, says $Q \notin N$ and, for every tube-bounded $f \in$ `C.integers`, the residue of $f$ vanishes at $Q$ (i.e. is $0$ or has positive $Q$-order) exactly when $f$ lies in $O$ and in the maximal ideal of $O$. The disjunct '$=0$' accommodates the convention for the order of $0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of component chart, tube-bounded function, holomorphy ring of a set of places, or centre of a valuation on a chart; these predicates are the project's own. Only the ambient objects are Mathlib's: `ValuationSubring`, the infimum of a family of subrings, and `IsLocalRing.maximalIdeal`.
--
--   **Where it is used.** These notions supply the vocabulary for locating a valuation subring of $F$ that contains the tube-bounded functions of a chart: either it is the chart's own valuation ring, or it has a unique centre among the places of the reduction lying off the exceptional finite set. They are used in the analysis of charts of modular curves within the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_AffinoidCentre.lean

import Definitions.Def_AlgebraicCurve_SemistableChartsComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def ComponentChart.tubeBounded (C : ComponentChart A F Fbar) (f : F) : Prop :=
  ∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A

def ComponentChart.HasAffinoidLifting (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar)) : Prop :=
  (∀ f : F, C.tubeBounded f → f ∈ C.integers) ∧
  (∀ g : Fbar, (∀ Q : Place (ResidueField A) Fbar, Q ∉ N → g ∈ Q.toValuationSubring) →
    ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ C.residue ⟨f, hf⟩ = g) ∧
  ∀ h : F, h ∈ C.integers → ∃ (r s : F) (hs : s ∈ C.integers),
    C.tubeBounded r ∧ C.tubeBounded s ∧ C.residue ⟨s, hs⟩ ≠ 0 ∧ h * s = r

def ComponentChart.regOff (N : Finset (Place (ResidueField A) Fbar)) : Subring Fbar :=
  ⨅ (Q : Place (ResidueField A) Fbar) (_ : Q ∉ N), Q.toValuationSubring.toSubring

def ComponentChart.HasPlaceDictionary (N : Finset (Place (ResidueField A) Fbar)) : Prop :=
  (∀ 𝔪 : Ideal (ComponentChart.regOff (A := A) N), 𝔪.IsMaximal →
    ∃! Q : Place (ResidueField A) Fbar, Q ∉ N ∧ ∀ g : ComponentChart.regOff (A := A) N, g ∈ 𝔪 ↔ (g : Fbar) = 0 ∨ 0 < Q.ord (g : Fbar)) ∧
  ∀ Q : Place (ResidueField A) Fbar, Q ∉ N →
    ∃ 𝔪 : Ideal (ComponentChart.regOff (A := A) N), 𝔪.IsMaximal ∧
      ∀ g : ComponentChart.regOff (A := A) N, g ∈ 𝔪 ↔ (g : Fbar) = 0 ∨ 0 < Q.ord (g : Fbar)

def ComponentChart.IsCentre (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar)) (O : ValuationSubring F)
    (Q : Place (ResidueField A) Fbar) : Prop :=
  Q ∉ N ∧ ∀ (f : F) (hf : f ∈ C.integers), C.tubeBounded f →
    ((C.residue ⟨f, hf⟩ = 0 ∨ 0 < Q.ord (C.residue ⟨f, hf⟩)) ↔ ∃ h : f ∈ O, (⟨f, h⟩ : O) ∈ maximalIdeal O)

end AlgebraicCurve


