-- Prove2me | Definitions.Def_ChapterG
-- name    : ChapterG
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T14:32:40.612081+00:00
-- url     : https://prove2.me/theorems/e2151df1-93c7-44a5-a6d6-ad056e43e343
-- title:
--   Chapter G
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterG.lean`): generated def bundle for ChapterG. See BookProof/ChapterG.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterG.lean

import Mathlib


/-!
# Chapter G — Gauge transformations in probability spaces

This file formalizes the self-contained mathematical backbone of the book's
chapter *"Gauge symmetry and dissipative dynamics in probability spaces"*
(book line 2128), following work-package **N6** of `FORMALIZATION_ROADMAP.md`.

Sections G.0–G.7:
* G.0 the gauge group of a parametrization,
* G.1 orbits = fibers; gauge-invariance ⇔ factoring through `π`,
* G.2 gauge-invariant subalgebras; gauge-independence of expectation values,
* G.3 the Dirac obstruction (no shift-invariant state on `ℤ`),
* G.4 gauge-fixing sections always exist,
* G.5 Haar averaging (invariantization) and the pushforward headline,
* G.6 the BRST ghost algebra (nilpotency),
* G.7 dissipative dynamics: Koopman evolution.

None of these needs an `EXTERNAL` hypothesis; everything is `sorry`-free.
-/

open scoped ComplexConjugate InnerProductSpace Matrix

namespace BookProof.ChapterG

/-! ## G.0 — Parametrization and its gauge group -/

/-- The gauge group of a parametrization `π : X → Y`: permutations of the
parameter space that preserve every fiber of `π` (book line 2247). -/
def gaugeGroup {X Y : Type*} (π : X → Y) : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ x, π (g x) = π x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [ha, hb]
  inv_mem' := by
    intro a ha x
    have h := ha (a⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_gaugeGroup {X Y : Type*} {π : X → Y} {g : Equiv.Perm X} :
    g ∈ gaugeGroup π ↔ ∀ x, π (g x) = π x := Iff.rfl

/-! ## G.1 — Orbits are fibers; gauge-invariance ⇔ factoring -/







/-! ## G.2 — Gauge-invariant subalgebras and expectation values -/

/-- Gauge-invariant observables form a subalgebra of `X → R`
(book 2277–2289). -/
def gaugeInvariantSubalgebra (R : Type*) [CommSemiring R] {X Y : Type*}
    (π : X → Y) : Subalgebra R (X → R) where
  carrier := {f | ∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x}
  mul_mem' := by
    intro f f' hf hf' g hg x
    simp only [Pi.mul_apply]
    rw [hf g hg, hf' g hg]
  add_mem' := by
    intro f f' hf hf' g hg x
    simp only [Pi.add_apply]
    rw [hf g hg, hf' g hg]
  algebraMap_mem' := by
    intro r g _ x
    rfl

/-- The gauge-invariant *operator* algebra of a family of gauge unitaries is the
centralizer of that family (book 2444). -/
abbrev gaugeInvariantOperators (𝔽 : Type*) [CommSemiring 𝔽] {V : Type*}
    [Semiring V] [Algebra 𝔽 V] {G : Type*} (U : G → V) : Subalgebra 𝔽 V :=
  Subalgebra.centralizer 𝔽 (Set.range U)



/-! ## G.3 — The Dirac obstruction: no gauge-invariant normalized state -/

open MeasureTheory









/-! ## G.4 — Gauge-fixing: sections always exist -/

/-- A complete gauge-fixing slice crosses each fiber at most once (book 2294). -/
def IsCompleteGaugeFixing {X Y : Type*} (π : X → Y) (S : Set X) : Prop :=
  ∀ ⦃x x'⦄, x ∈ S → x' ∈ S → π x = π x' → x = x'



/-! ## G.5 — Haar averaging (invariantization) and the pushforward headline -/

section Haar

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

/-- The Haar averaging (invariantization) operator (book 2350–2392). -/
noncomputable def haarAverage (f : X → ℝ) (x : X) : ℝ := ∫ g, f (g⁻¹ • x) ∂μG









end Haar



/-! ## G.6 — BRST ghost algebra (nilpotency) -/

section BRST

variable {A : Type*} [Ring A]

/-- The ghost annihilation operator `ψ` (book 2403–2452). -/
def ghostAnnih : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]

/-- The ghost creation operator `ψ†`. -/
def ghostCreat : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]









/-- The BRST charge `Ω = Q·ψ†` for a gauge generator `Q` (book: `Ω=(πφ+π*φ*)ψ†`). -/
def BRST (Q : A) : Matrix (Fin 2) (Fin 2) A := !![0, 0; Q, 0]



end BRST

/-! ## G.7 — Dissipative dynamics: Koopman evolution -/

/-- The damped coupled-oscillator system in companion (first-order) form
(book eq. 2199). -/
def dampedCoupledMatrix (l₁ l₂ w₁ w₂ c₁ c₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;  -w₁^2, -l₁, c₂, 0;  0, 0, 0, 1;  c₁, 0, -w₂^2, -l₂]







/-! ### G.7a — the Koopman unitary of a measure-preserving equivalence -/

section Koopman

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Composing with `f` then with `f.symm` is the identity on `Lp E p ν`. -/
theorem koopman_comp_left (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν) (u : Lp E p ν) :
    (Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm)
      (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u) = u := by
  apply Lp.ext
  have h2 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm)
      (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : β → E)
      =ᵐ[ν] (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : α → E) ∘ f.symm :=
    Lp.coeFn_compMeasurePreserving _ hf.symm
  have h1 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : α → E)
      =ᵐ[μ] (↑↑u : β → E) ∘ f :=
    Lp.coeFn_compMeasurePreserving _ hf
  have h1' : ((↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : α → E) ∘ f.symm)
      =ᵐ[ν] ((↑↑u : β → E) ∘ f) ∘ f.symm :=
    (hf.symm.quasiMeasurePreserving).ae_eq_comp h1
  refine h2.trans (h1'.trans ?_)
  filter_upwards with x
  simp [Function.comp_apply, MeasurableEquiv.apply_symm_apply]

/-- Composing with `f.symm` then with `f` is the identity on `Lp E p μ`. -/
theorem koopman_comp_right (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν) (v : Lp E p μ) :
    (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf)
      (Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v) = v := by
  apply Lp.ext
  have h2 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf)
      (Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : α → E)
      =ᵐ[μ] (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : β → E) ∘ f :=
    Lp.coeFn_compMeasurePreserving _ hf
  have h1 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : β → E)
      =ᵐ[ν] (↑↑v : α → E) ∘ f.symm :=
    Lp.coeFn_compMeasurePreserving _ hf.symm
  have h1' : ((↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : β → E) ∘ f)
      =ᵐ[μ] ((↑↑v : α → E) ∘ f.symm) ∘ f :=
    (hf.quasiMeasurePreserving).ae_eq_comp h1
  refine h2.trans (h1'.trans ?_)
  filter_upwards with x
  simp [Function.comp_apply, MeasurableEquiv.symm_apply_apply]

/-! ## G.13 — Parametrization implies gauge group existence

From book.tex lines 2240–2251: every parametrization `π : X → Y` has an
associated gauge group acting on `X` such that `π` is invariant under the
group action.
-/



/-! ## G.14 — Gauge symmetry vs anomalies

From book.tex lines 2394–2400: a gauge symmetry cannot exhibit anomalies
because there is no symmetry-breaking parameter.  Formally: expectation
values of gauge-invariant operators are invariant under the gauge group
action.  An anomaly would appear as a failure of this invariance.
-/



/-- The **Koopman unitary** induced by a measure-preserving equivalence: the
probability-conserving evolution acts as an isometric isomorphism of
wave-functions (book §2184, and the N7(a) deliverable for book-Ch.-B §7/§9). -/
noncomputable def koopmanEquiv (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν) :
    Lp E p ν ≃ₗᵢ[ℝ] Lp E p μ where
  toLinearEquiv :=
  { (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf).toLinearMap with
    invFun := Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm
    left_inv := koopman_comp_left f hf
    right_inv := koopman_comp_right f hf }
  norm_map' := (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf).norm_map'

end Koopman

/-! ## G.13 — Unconstrained gauge-fixing

From book.tex lines 2334–2348: a gauge-fixing is *unconstrained* when the
gauge generators are necessarily excluded from the commutative von Neumann
algebra and thus do not impose constraints on the spectrum of the algebra.
The commutative algebra used in the gauge-fixing is necessarily commutative
(bounded commuting normal operators can always be simultaneously diagonalized),
so the gauge generators (which are non-commutative in general) cannot be
members of it.
-/

/-- A gauge-fixing is *unconstrained* if the gauge group acts non-trivially
on the commutative von Neumann algebra of gauge-invariant functions
(book line 2342). This means the gauge generators are excluded from the
algebra — they cannot impose constraints on the spectrum. -/
def IsUnconstrainedGaugeFixing {X Y : Type*} (π : X → Y) : Prop :=
  ∃ g ∈ gaugeGroup π, ∃ (f : gaugeInvariantSubalgebra ℝ π),
    (f : X → ℝ) ∘ g ≠ (f : X → ℝ)



/-! ## G.14 — Two-basis correspondence

From book.tex lines 2356–2366: there is always one basis where the gauge
unitary transformations are functions of the spectrum (constrained basis) and
another basis where they are not (unconstrained basis). The expectation
values of gauge-invariant operators are the same in both bases.
-/

/-- The *constrained basis*: a basis where gauge unitary transformations
depend only on the spectrum (book line 2356). In this basis, the
transformation acts as `basis (g x) = φ (basis x)` for some `φ : Y → Y`. -/
def constrainedBasis {X Y : Type*} (π : X → Y) : Prop :=
  ∃ (basis : X → Y) (_ : Function.Bijective basis),
    ∀ g ∈ gaugeGroup π, ∃ (φ : Y → Y), basis ∘ g = φ ∘ basis

/-- The *unconstrained basis*: a basis where gauge transformations are
not functions of the spectrum (book line 2357). There exists a gauge
transformation that does not commute with the basis in the sense above. -/
def unconstrainedBasis {X Y : Type*} (π : X → Y) : Prop :=
  ∃ (basis : X → Y) (_ : Function.Bijective basis),
    ∃ g ∈ gaugeGroup π, ∀ (φ : Y → Y), basis ∘ g ≠ φ ∘ basis



/-! ## G.15 — Casimir operator constraints

From book.tex lines 2368–2370: it suffices to constrain to zero the Casimir
operators of the (eventually non-commutative) Lie algebra of constraints;
this imposes the constraints without the need for the constraints to be part
of the commutative von Neumann algebra.
-/



end BookProof.ChapterG


