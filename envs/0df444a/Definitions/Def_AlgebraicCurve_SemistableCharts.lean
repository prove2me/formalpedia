-- Prove2me | Definitions.Def_AlgebraicCurve_SemistableCharts
-- name    : AlgebraicCurve_SemistableCharts
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/c8c12601-f307-5522-a06e-3620205fc907
-- title:
--   Component charts, annuli and attachment for semistable reduction
-- statement:
--   Throughout, $L$ is a field with a valuation subring $A$ of residue field $k$, $F$ is an extension of $L$ (a function field in the intended use) and $\bar F$ an extension of $k$. A `ComponentChart A F Fbar` is data together with axioms carried as fields: a valuation subring `integers` of $F$ whose contraction to $L$ is exactly $A$, a surjective ring map `residue` from `integers` to $\bar F$ with kernel the maximal ideal (so $\bar F$ is the residue field of `integers`) which on constants is the residue map of $A$ followed by $k \to \bar F$, and the normalisation that every $f \neq 0$ in $F$ satisfies $cf \in$ `integers` with nonzero residue for some $c \in L$; a set `dom` of places of $F/L$, a finite set `nodes` of places of $\bar F/k$, and a map `placeMap` from places of $F/L$ to places of $\bar F/k$ carrying `dom` off `nodes`. The two compatibility axioms are: for a rational $P \in$ `dom` and $f \in$ `integers` integral at every place of `dom` in the fibre of $P$ over `placeMap P`, the residue $\bar f$ is integral at `placeMap P`, the value $P.\mathrm{evalAt}\,f$ lies in $A$, and its residue, read in the residue field of `placeMap P`, is the value of $\bar f$ there; and, for $f \in$ `integers` with $\bar f \neq 0$, any divisor that computes $\mathrm{ord}_P f$ on `dom` and vanishes off `dom` pushes forward under `placeMap` to a divisor agreeing with $\mathrm{ord}_Q \bar f$ at every place $Q \notin$ `nodes`. `ofConstantReduction` turns a constant reduction satisfying the project predicate `ConstantReduction.IsPointwise` into a chart with `dom` all places and no nodes, the accompanying lemmas recording its fields.
--
--   An `Annulus A F` consists of a set `dom` of places of $F/L$, a parameter `param` $\in F$ and a `modulus` in the maximal ideal of $A$, subject to: every $P \in$ `dom` is rational, `param` is integral at $P$ with value $c_P := P.\mathrm{evalAt}(\mathrm{param})$ a nonzero element of the maximal ideal such that `modulus` $\in c_P \mathfrak m_A$; conversely every such $c$ is the value of `param` at exactly one place of `dom`; $\mathrm{param} - c_P$ has order $1$ at $P$; and a unit principle — a nonzero $f$ with $\mathrm{ord}_P f = 0$ throughout `dom` admits $m \in \mathbb Z$ and $c \in L^{\times}$ with $f(P)\,c^{-1}c_P^{-m}$ a unit of $A$ for all $P \in$ `dom`, that is, $f$ has a single slope on the annulus. `Annulus.IsAttached An C x` asserts that $x$ is a node of the chart $C$, that `An.param` lies in `C.integers` with residue a uniformiser at $x$, and that every $f \in$ `C.integers` with nonzero residue and no zero or pole on `An.dom` has slope exactly $\mathrm{ord}_x \bar f$ with unit leading coefficient: $f(P)\,c_P^{-\mathrm{ord}_x \bar f} \in A^{\times}$ for all $P \in$ `An.dom`. Degenerate members are provided for $A = \top$: the maximal ideal of the whole field is zero, whence every annulus over $\top$ has empty domain; `Annulus.ofTop` realises one, `ComponentChart.ofTop` is the chart coming from the trivial constant reduction with $\bar F = F$, all places in `dom` and no nodes, and consequently no annulus is attached to it at any place.
--
--   **Relation to Mathlib.** Mathlib has no notion of constant reduction, component chart or annulus of a function field; these are the project's own. `ComponentChart` is a localised variant of the project's `ConstantReduction`: the same integers, residue map and map on places, but with the degree-preservation requirement dropped and the divisor-pushforward and pointwise-evaluation requirements restricted to a set `dom` of places and to places outside a finite set `nodes`.
--
--   **Where it is used.** The module supplies the vocabulary in which a semistable model of a function field over a valuation subring is described place by place: charts for the components, annuli for the formal neighbourhoods of the nodes, and the attachment predicate linking the two. It sits above the project's constant reductions and its lifts of a finite place of a number field to a valuation subring of $\overline{\mathbb Q}$, and is used where the reduction of a curve at a finite place and the resulting divisor class groups are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_SemistableCharts.lean

import Definitions.Def_ModularCurve_FinitePlaceLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure ComponentChart where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  dom : Set (Place L F)

  nodes : Finset (Place (ResidueField A) Fbar)

  placeMap : Place L F → Place (ResidueField A) Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

  placeMap_not_mem_nodes : ∀ P ∈ dom, placeMap P ∉ nodes

  pointwise : ∀ P ∈ dom, P.IsRational → ∀ (f : F) (hf : f ∈ integers),
    (∀ w ∈ dom, placeMap w = placeMap P → f ∈ w.toValuationSubring) →
      ∃ (hm : (residue ⟨f, hf⟩ : Fbar) ∈ (placeMap P).toValuationSubring) (h : P.evalAt f ∈ A),
        algebraMap (ResidueField A) (placeMap P).ResidueField (IsLocalRing.residue A ⟨P.evalAt f, h⟩)
          = IsLocalRing.residue (placeMap P).toValuationSubring ⟨residue ⟨f, hf⟩, hm⟩

  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P ∈ dom, D P = P.ord (f : F)) → (∀ P, P ∉ dom → D P = 0) →
      ∀ Q, Q ∉ nodes → Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

namespace ComponentChart

variable {A F Fbar}

def ofConstantReduction (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    ComponentChart A F Fbar where
  integers := R.integers
  residue := R.residue
  dom := Set.univ
  nodes := ∅
  placeMap := R.placeMap
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem
  placeMap_not_mem_nodes := fun _ _ h => (Finset.notMem_empty _ h).elim
  pointwise := fun P _ hP f hf hfib => hR P hP f hf (fun w hw => hfib w (Set.mem_univ w) hw)
  mapDomain_placeMap := fun f hf D hD _ Q _ =>
    R.mapDomain_placeMap f hf D (fun P => hD P (Set.mem_univ P)) Q

@[simp] theorem ofConstantReduction_integers (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).integers = R.integers := rfl

@[simp] theorem ofConstantReduction_dom (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).dom = Set.univ := rfl

@[simp] theorem ofConstantReduction_nodes (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).nodes = ∅ := rfl

@[simp] theorem ofConstantReduction_placeMap (R : ConstantReduction A F Fbar) (hR : R.IsPointwise) :
    (ofConstantReduction R hR).placeMap = R.placeMap := rfl

end ComponentChart

structure Annulus where

  dom : Set (Place L F)

  param : F

  modulus : A

  modulus_mem : modulus ∈ maximalIdeal A

  mem_dom : ∀ P ∈ dom, P.IsRational ∧ param ∈ P.toValuationSubring ∧
    (∃ h : P.evalAt param ∈ A, (⟨P.evalAt param, h⟩ : A) ∈ maximalIdeal A) ∧ P.evalAt param ≠ 0 ∧
    ∃ m ∈ maximalIdeal A, (modulus : L) = P.evalAt param * m

  existsUnique_evalAt_eq : ∀ c : A, c ∈ maximalIdeal A → (c : L) ≠ 0 →
    (∃ m ∈ maximalIdeal A, (modulus : L) = c * m) → ∃! P : Place L F, P ∈ dom ∧ P.evalAt param = c

  ord_param_sub : ∀ P ∈ dom, P.ord (param - algebraMap L F (P.evalAt param)) = 1

  unit_principle : ∀ f : F, f ≠ 0 → (∀ P ∈ dom, P.ord f = 0) →
    ∃ (m : ℤ) (c : L), c ≠ 0 ∧
      ∀ P ∈ dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A)

namespace Annulus

variable {A F}

variable {Fbar}

def IsAttached (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) :
    Prop :=
  x ∈ C.nodes ∧ ∃ hz : An.param ∈ C.integers, x.ord (C.residue ⟨An.param, hz⟩) = 1 ∧
    ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)

section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]

theorem maximalIdeal_top_eq_bot' : maximalIdeal ↥(⊤ : ValuationSubring L) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [Ideal.mem_bot]
  by_contra hne
  apply hx
  have hxv : (x : L) ≠ 0 := fun h => hne (Subtype.ext h)
  exact ⟨⟨x, ⟨(x : L)⁻¹, ValuationSubring.mem_top _⟩,
    Subtype.ext (mul_inv_cancel₀ hxv), Subtype.ext (inv_mul_cancel₀ hxv)⟩, rfl⟩

def ofTop : Annulus (⊤ : ValuationSubring L) F where
  dom := ∅
  param := 1
  modulus := 0
  modulus_mem := Ideal.zero_mem _
  mem_dom := fun _ h => (Set.notMem_empty _ h).elim
  existsUnique_evalAt_eq := fun c hc hc0 _ => by
    rw [maximalIdeal_top_eq_bot', Ideal.mem_bot] at hc
    exact absurd (congrArg Subtype.val hc) hc0
  ord_param_sub := fun _ h => (Set.notMem_empty _ h).elim
  unit_principle := fun _ _ _ => ⟨0, 1, one_ne_zero, fun _ h => (Set.notMem_empty _ h).elim⟩

theorem dom_ofTop : (ofTop L F).dom = ∅ := rfl

theorem dom_eq_empty_of_top (An : Annulus (⊤ : ValuationSubring L) F) : An.dom = ∅ := by
  ext P
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hP
  obtain ⟨-, -, ⟨h, hm⟩, hne, -⟩ := An.mem_dom P hP
  rw [maximalIdeal_top_eq_bot', Ideal.mem_bot] at hm
  exact hne (congrArg Subtype.val hm)

end DegenerateMember

end Annulus

namespace ComponentChart

section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]

attribute [local instance] ConstantReduction.ofTopAlgebra

def ofTop : ComponentChart (⊤ : ValuationSubring L) F F :=
  ofConstantReduction (ConstantReduction.ofTop L F) (ConstantReduction.isPointwise_ofTop L F)

theorem ofTop_dom : (ofTop L F).dom = Set.univ := rfl

theorem ofTop_nodes : (ofTop L F).nodes = ∅ := rfl

theorem not_isAttached_ofTop (An : Annulus (⊤ : ValuationSubring L) F)
    (x : Place (ResidueField ↥(⊤ : ValuationSubring L)) F) : ¬ An.IsAttached (ofTop L F) x :=
  fun h => Finset.notMem_empty _ h.1

end DegenerateMember

end ComponentChart

end AlgebraicCurve

end


