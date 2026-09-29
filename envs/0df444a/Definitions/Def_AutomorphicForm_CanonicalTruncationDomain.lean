-- Prove2me | Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
-- name    : AutomorphicForm_CanonicalTruncationDomain
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/cec72093-a0c3-510b-88c5-0e8a757f9f06
-- title:
--   Canonical truncation data for adelic GL(2) fundamental domains
-- statement:
--   Throughout, $L$ is a number field and $\alpha,\beta$ are real parameters cutting out the determinant slab $\{g \in \mathrm{GL}_2(\mathbb{A}_L) : \lVert \det g\rVert \in [\alpha,\beta]\}$, the norm being [`NumberField.TateGlobal.ideleNorm`](../def/NumberField_TateGlobalZeta.html#L19), the value of the module character `distribHaarChar` of the adele ring on the determinant idele. The predicate `IsTruncationDatum L α β d` applies to a tuple $d = ((c,u,d_1,d_2), T, \Phi)$ consisting of four reals and two subsets of $\mathrm{GL}_2(\mathbb{A}_L)$, and asserts five things: $c > 0$; $T$ is compact; $\Phi$ is contained in $\bigcup_{y\in T} S\cdot y$, where $S$ is the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (finite part integral, every archimedean local height at least $c$, every archimedean window quantity `xWindowSq` at most $u^2$, every archimedean determinant norm in $[d_1,d_2]$); $\Phi$ lies in the determinant slab; and $\Phi$ is a fundamental domain, in Mathlib's sense, for the left translation action of the subgroup $\mathrm{GL}_2(L) \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ (the range of `globalPoints`) on the slab, with respect to the adelic Haar measure `adelicGLHaar` restricted to the slab.
--
--   `canonicalTruncationData L α β` then fixes one such tuple once and for all: it is a choice of a datum when one exists, and the degenerate tuple $((0,0,0,0),\emptyset,\emptyset)$ otherwise, so the definition is total. Its components are named separately: `canonicalTruncationDomain` ($\Phi$), `canonicalTruncationTranslates` ($T$), and `canonicalTruncationFloor`, `canonicalTruncationWindow`, `canonicalTruncationLowerCut`, `canonicalTruncationUpperCut` ($c$, $u$, $d_1$, $d_2$). Two lemmas record the only properties of the choice: under the hypothesis that an admissible datum exists, the chosen tuple is the one produced by that existence proof, and it satisfies `IsTruncationDatum`. No existence assertion is made; for $0 < \alpha < \beta$ that is a matter of reduction theory, proved elsewhere.
--
--   **Relation to Mathlib.** `IsFundamentalDomain`, compactness and the Haar machinery are Mathlib's; the notion of a truncation datum for the determinant slab in $\mathrm{GL}_2$ of an adele ring, and the canonical choice of one, are the project's own, built on its Siegel-set and adelic-Haar definitions.
--
--   **Where it is used.** The chosen set `canonicalTruncationDomain` is the region over which adelic automorphic forms on $\mathrm{GL}_2$ are integrated: it is a fundamental domain for $\mathrm{GL}_2(L)$ inside a determinant slab, and its containment in finitely many translates of a centre-cut Siegel set is what makes growth estimates and $L^2$ conditions on such forms usable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CanonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm

variable (L : Type) [Field L] [NumberField L]

def IsTruncationDatum (α β : ℝ)
    (d : (ℝ × ℝ × ℝ × ℝ) × Set (AdelicGL2 (𝓞 L) L) × Set (AdelicGL2 (𝓞 L) L)) : Prop :=
  0 < d.1.1 ∧ IsCompact d.2.1 ∧
    d.2.2 ⊆ ⋃ y ∈ d.2.1, (· * y) '' WindowedSiegel.centreCutSiegelSet L d.1.1 d.1.2.1 d.1.2.2.1 d.1.2.2.2 ∧
    d.2.2 ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
    IsFundamentalDomain (globalPoints (𝓞 L) L).range d.2.2
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})

open Classical in

def canonicalTruncationData (α β : ℝ) : (ℝ × ℝ × ℝ × ℝ) × Set (AdelicGL2 (𝓞 L) L) × Set (AdelicGL2 (𝓞 L) L) :=
  if h : ∃ d, IsTruncationDatum L α β d then Classical.choose h else ((0, 0, 0, 0), ∅, ∅)

def canonicalTruncationDomain (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  (canonicalTruncationData L α β).2.2

def canonicalTruncationTranslates (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  (canonicalTruncationData L α β).2.1

def canonicalTruncationFloor (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.1

def canonicalTruncationWindow (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.2.1

def canonicalTruncationLowerCut (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.2.2.1

def canonicalTruncationUpperCut (α β : ℝ) : ℝ :=
  (canonicalTruncationData L α β).1.2.2.2

theorem canonicalTruncationData_eq_of_exists {α β : ℝ}
    (h : ∃ d, IsTruncationDatum L α β d) : canonicalTruncationData L α β = Classical.choose h := by
  unfold canonicalTruncationData
  exact dif_pos h

theorem canonicalTruncationData_spec {α β : ℝ}
    (h : ∃ d, IsTruncationDatum L α β d) : IsTruncationDatum L α β (canonicalTruncationData L α β) := by
  rw [canonicalTruncationData_eq_of_exists L h]
  exact Classical.choose_spec h

end AutomorphicForm

example (L : Type) [Field L] [NumberField L] (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  AutomorphicForm.canonicalTruncationDomain L α β

example (L : Type) [Field L] [NumberField L]
    (h : ∃ d, AutomorphicForm.IsTruncationDatum L 1 2 d) :
    AutomorphicForm.canonicalTruncationDomain L 1 2 = (Classical.choose h).2.2 := by
  unfold AutomorphicForm.canonicalTruncationDomain
  rw [AutomorphicForm.canonicalTruncationData_eq_of_exists L h]

end


