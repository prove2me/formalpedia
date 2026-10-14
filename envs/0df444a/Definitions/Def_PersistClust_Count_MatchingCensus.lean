-- Prove2me | Definitions.Def_PersistClust_Count_MatchingCensus
-- name    : PersistClust_Count_MatchingCensus
-- status  : Definition
-- author  : @fabianroll
-- created : 2026-10-12T05:57:16.912248+00:00
-- url     : https://prove2.me/theorems/2b57bf1c-e989-486e-9bda-2b9cb4d23a1c
-- title:
--   Theorem 4.5 module machinery: component classes, strong interleaving, tameness, and birth bookkeeping
-- statement:
--   This file defines the module-level machinery used by the matching construction of Theorem 4.5 (RR-6968, §4).
--
--   A $0$-dimensional persistence module is given by a decreasing family of stages $X^t$ (a set over each level $t$) together with the same-stage component relation $J_t$. The type `comps stage J t` is the set of component classes at level $t$, implemented as the quotient-free image form; `compRep` chooses a representative point of a class, and `structMap` is the coarsening (λ-structure) map sending each stage-$t$ class to the unique stage-$s$ class containing it, for $s \le t$.
--
--   `StrongInterleavingAbove` is the paper's strong $\varepsilon$-interleaving above a level $\alpha$ between two modules, expressed at the component level: maps $\varphi_\beta : X^\beta \to Y^{\beta-\varepsilon}$ and $\psi_\beta : Y^\beta \to X^{\beta-\varepsilon}$ for $\beta \ge \alpha$, together with the two naturality squares with the coarsening maps and the two interleaving-composition squares $\varphi_{\beta-\varepsilon} \circ \psi_\beta = y^\beta_{\beta-2\varepsilon}$ (and the mirror).
--
--   `IsTameModule` is the finite-type condition on a module: pointwise finiteness of the class image, a finite critical set outside of which the class structure is rigid on critical-free windows, and eventual emptiness. `critSet` extracts the critical set, and `critSet_spec` its rigidity property. `IsFresh` says a class has no ancestor at any higher level; `hasOriginAbove` says a class carries a fresh origin above a given level; `AncSet` is the set of ancestor levels of a class and `birthSup` its supremum — the birth level of the class.
--
--   `t3_comb` is the box-combination of ranks whose infimum over $\eta \in (0, (b-d)/2)$ computes the multiplicity of the bar $(b,d)$ in the module's persistence diagram.
--
--   **Formalization Note** These declarations are the shared interface between the published children of Theorem 4.5: the demand-routing child, the gate child (`theorem_4_5_gate_matching`), and the assembly child (`theorem_4_5_matching_assembly`). The file contains only definitions and the two choice-accessor lemmas; it is verified to compile in the platform's default environment.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 8–9 and pp. 18–21 (§2.2 modules and Eq. (1) tameness; §4 component-level interleaving in the proof of Theorem 4.5)

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw

namespace PersistClust.Count

/-! ### Module-level machinery for the matching construction (Theorem 4.5)

The component-level interface between a filtration and the multi-bijection construction of
Theorem 4.5: component classes and their structure maps, the strong interleaving of two
modules above a level, finite-type tameness of a module, and the birth/census bookkeeping
(critical set, freshness, ancestor levels, birth suprema, the mult box-combination). -/

/-- Component classes at level `t`: the classes of the equivalence relation "same stage-`t`
component" — implemented as the image of the stage under the relation's neighborhood map. -/
abbrev comps {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop) (t : ℝ) :=
  {C : Set ι // C ∈ (fun x => {y | J t x y}) '' stage t}

/-- A chosen representative point of a component class. -/
noncomputable def compRep {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop) (t : ℝ)
    (C : comps stage J t) : ι :=
  Classical.choose
    (show ∃ x, x ∈ stage t ∧ (fun x => {y | J t x y}) x = C.val from C.property)

/-- The chosen representative lies in the stage and represents the class. -/
theorem compRep_spec {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop) (t : ℝ)
    (C : comps stage J t) :
    compRep stage J t C ∈ stage t ∧
      (fun x => {y | J t x y}) (compRep stage J t C) = C.val :=
  Classical.choose_spec
    (show ∃ x, x ∈ stage t ∧ (fun x => {y | J t x y}) x = C.val from C.property)

/-- The λ-structure (coarsening) map: each stage-`t` component lies in a unique stage-`s`
one (`s ≤ t`). -/
noncomputable def structMap {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : s ≤ t) (C : comps stage J t) :
    comps stage J s :=
  ⟨{y | J s (compRep stage J t C) y},
    ⟨compRep stage J t C, hLaw.antitone hst (compRep_spec stage J t C).1, rfl⟩⟩

/-- The value of the structure map: the stage-`s` neighborhood of the representative. -/
theorem structMap_val {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : s ≤ t) (C : comps stage J t) :
    (structMap hLaw hst C).val = {y | J s (compRep stage J t C) y} := rfl

/-- The paper's strong ε-interleaving above α: maps `φ_β : X^β → Y^{β−ε}` and
`ψ_β : Y^β → X^{β−ε}` for `β ≥ α`, with the four commuting squares:
(i') `φ_β ∘ x^{β'}_β = y^{β'−ε}_{β−ε} ∘ φ_{β'}` and (ii') the mirror for `ψ`
(`β' ≥ β ≥ α`); (iii') `φ_{β−ε} ∘ ψ_β = y^β_{β−2ε}` and (iv') the mirror
(`β ≥ α + ε`). -/
def StrongInterleavingAbove {ιX ιY : Type*}
    (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop) (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY) (α ε : ℝ) (hε : 0 ≤ ε) :
    Prop :=
  ∃ (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε)),
    (∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x)) ∧
    (∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y)) ∧
    (∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y) ∧
    (∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)

/-- Finite-type structure of a module: pointwise finiteness of the class image, a finite
critical set with the critical-free componentwise bijection, and eventual emptiness. -/
def IsTameModule {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop) : Prop :=
  (∀ t, ((fun x => {y | J t x y}) '' stage t).Finite) ∧
  (∃ T : Finset ℝ, ∀ t s : ℝ, t ≤ s → (∀ u ∈ T, u < t ∨ s < u) →
      (∀ x ∈ stage t, ∃ y ∈ stage s, J t x y) ∧
      (∀ y ∈ stage s, ∀ y' ∈ stage s, J t y y' → J s y y')) ∧
  (∃ s₀, ∀ s ≥ s₀, stage s = ∅)

/-- A class is `fresh` at level `τ` when it has no ancestor at any higher level. -/
def IsFresh {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (τ : ℝ) (C : comps stage J τ) : Prop :=
  ∀ (s : ℝ) (hs : τ < s) (C' : comps stage J s),
    structMap hLaw (le_of_lt hs) C' ≠ C

/-- The finite critical set carried by `IsTameModule`. -/
noncomputable def critSet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hTame : IsTameModule stage J) : Finset ℝ :=
  Classical.choose hTame.2.1

/-- The critical-set property: the class structure is rigid on critical-set-free windows. -/
theorem critSet_spec {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hTame : IsTameModule stage J) : ∀ t s : ℝ, t ≤ s →
      (∀ u ∈ critSet hTame, u < t ∨ s < u) →
      (∀ x ∈ stage t, ∃ y ∈ stage s, J t x y) ∧
      (∀ y ∈ stage s, ∀ y' ∈ stage s, J t y y' → J s y y') :=
  Classical.choose_spec hTame.2.1

/-- A class at level `t` carries a fresh origin at level `≥ s`. -/
def hasOriginAbove {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (s : ℝ) {t : ℝ} (C : comps stage J t) : Prop :=
  ∃ (τ : ℝ) (hτ : t ≤ τ) (C' : comps stage J τ),
    s ≤ τ ∧ IsFresh hLaw τ C' ∧ structMap hLaw hτ C' = C

/-- The ancestor-level set of a cell. -/
def AncSet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) : Set ℝ :=
  {u : ℝ | ∃ (hu : t ≤ u) (C' : comps stage J u), structMap hLaw hu C' = C}

/-- The birth-sup of a cell: the supremum of the levels at which it has an ancestor. -/
noncomputable def birthSup {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) : ℝ :=
  sSup {u : ℝ | ∃ (hu : t ≤ u) (C' : comps stage J u), structMap hLaw hu C' = C}

/-- The mult box-combination at `(b,d)` as a function of `η`: the bracket whose infimum
over `η ∈ (0, (b−d)/2)` gives the multiplicity of `(b,d)` in the diagram of the module. -/
noncomputable def t3_comb {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (b d η : ℝ) : ℕ∞ :=
  (rankFn stage J (b - η) (d + η) - rankFn stage J (b + η) (d + η)) -
    (rankFn stage J (b - η) (d - η) - rankFn stage J (b + η) (d - η))

end PersistClust.Count


