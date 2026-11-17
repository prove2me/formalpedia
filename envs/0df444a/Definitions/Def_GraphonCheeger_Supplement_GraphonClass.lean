-- Prove2me | Definitions.Def_GraphonCheeger_Supplement_GraphonClass
-- name    : GraphonCheeger_Supplement_GraphonClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:20:21.168104+00:00
-- url     : https://prove2.me/theorems/ea5917fe-09e9-4d0b-a6ea-ab865e7aabf5
-- title:
--   All $\kappa$-coloured graphons modulo equivalence, and the map $[W]\mapsto\tau(W)$
-- statement:
--   A $\kappa$-coloured graphon may live on any probability space $(\Omega,\mathcal F,\mu)$. Bundling the space with the graphon, the coloured graphons form one collection, and equivalence $\cong$ (equality of all homomorphism densities $t(F,\cdot)$) is an equivalence relation on it. The quotient is the set of all coloured graphons modulo $\cong$, and
--   $$
--   [W]\longmapsto\tau(W)=(t(F,W))_F
--   $$
--   is a well-defined map on it. Among the classes are those of the pure coloured graphons $(W,\chi)$ on $[0,1]$ with Lebesgue measure.
--
--   This is the object in Theorem 2.12, which identifies the set of coloured graph limits with this quotient.
--
--   **Formalization Note** `AnyKGraphon κ` bundles a type `Ω : Type` (the lowest universe, which contains $[0,1]$ and every `Fin n`), its σ-field, a probability measure, a graphon and a colouring. `graphonSetoid κ` is the kernel of $\tau$, i.e. equivalence by Definition 2.6 via Lemma 2.5(i); `GraphonClass κ` is the quotient and `limitOf` the induced map. `pureUnit W hW χ hχ` is the pure coloured graphon $(W,\chi)$ on `unitInterval` with `volume`.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Definition 2.6, p.8; Theorem 2.12, p.10

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens

open MeasureTheory

namespace GraphonCheeger.Supplement

/-!
# All `κ`-coloured graphons modulo equivalence

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), Definition 2.6 (p.8) and Theorem 2.12 (p.10).

**Formalization Note.**
* `AnyKGraphon κ` bundles a `κ`-coloured graphon together with its probability space
  `(Ω, F, µ)`, where `Ω : Type` ranges over all types of the lowest universe (which contains
  `[0, 1]` and every `Fin n`).
* `graphonSetoid κ` is equivalence `≅` (Def. 2.6, via Lemma 2.5(i)): equality of all
  homomorphism densities, i.e. the kernel of `τ`. `GraphonClass κ` is the quotient, and
  `limitOf` is the map `[W] ↦ τ(W) = (t(F, W))_F` it induces.
* `pureUnit W hW χ hχ` is the pure coloured graphon `(W, χ)` on `[0, 1]` with Lebesgue measure.
-/

/-- A `κ`-coloured graphon on some probability space `(Ω, F, µ)` (Def. 2.1, p.6). -/
structure AnyKGraphon (κ : ℕ) where
  /-- The underlying space. -/
  Ω : Type
  /-- Its σ-field. -/
  [ms : MeasurableSpace Ω]
  /-- Its probability measure. -/
  μ : Measure Ω
  [prob : IsProbabilityMeasure μ]
  /-- The graphon. -/
  W : Ω → Ω → ℝ
  /-- The colouring. -/
  Ψ : Ω → Fin κ → ℝ
  isGraphon : IsGraphon W
  isColouring : IsKColouring Ψ

attribute [instance] AnyKGraphon.ms AnyKGraphon.prob

/-- `τ(W) = (t(F, W))_F` of a bundled coloured graphon. -/
noncomputable def AnyKGraphon.tau {κ : ℕ} (X : AnyKGraphon κ) : LIdx κ → ℝ :=
  Supplement.tau X.μ X.W X.Ψ

/-- Equivalence `≅` of coloured graphons (Def. 2.6, p.8) as a setoid. -/
noncomputable def graphonSetoid (κ : ℕ) : Setoid (AnyKGraphon κ) :=
  Setoid.ker AnyKGraphon.tau

/-- The set of all `κ`-coloured graphons modulo `≅`. -/
def GraphonClass (κ : ℕ) : Type 1 :=
  Quotient (graphonSetoid κ)

/-- The map `[W] ↦ τ(W)` on equivalence classes. -/
noncomputable def limitOf {κ : ℕ} : GraphonClass κ → (LIdx κ → ℝ) :=
  Quotient.lift AnyKGraphon.tau (fun _ _ h => h)

/-- The pure coloured graphon `(W, χ)` on `[0, 1]` with Lebesgue measure. -/
noncomputable def pureUnit {κ : ℕ} (W : unitInterval → unitInterval → ℝ) (hW : IsGraphon W)
    (χ : unitInterval → Fin κ) (hχ : Measurable χ) : AnyKGraphon κ where
  Ω := unitInterval
  μ := volume
  W := W
  Ψ := ofColour χ
  isGraphon := hW
  isColouring := by
    refine ⟨fun ℓ => (measurable_of_countable (fun c : Fin κ => if c = ℓ then (1 : ℝ) else 0)).comp hχ,
      fun x ℓ => ?_, fun x => ?_⟩
    · unfold ofColour; split_ifs <;> norm_num
    · simp [ofColour]

end GraphonCheeger.Supplement


