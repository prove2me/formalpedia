-- Prove2me | Definitions.Def_MDPFinance_Contracting_LsSet
-- name    : MDPFinance_Contracting_LsSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:42:40.072073+00:00
-- url     : https://prove2.me/theorems/f48e45a6-03a7-40e5-9d0c-32b775d8d442
-- title:
--   The upper limit Ls of a sequence of sets, set-valued semicontinuity, and argmax sets D*
-- statement:
--   For the semicontinuous existence theorems of §7.2, $D_n^*(x) := \{a \in D(x) \mid a \text{
--   maximizes } a \mapsto LJ_{n-1}(x,a)\}$ collects the optimal actions of the $n$-stage problem, and
--   $\mathrm{Ls}\,D_n^*(x)$, the **upper limit of the sequence of sets** $(D_n^*(x))_n$, collects
--   every point that is an accumulation point of *some* selection $a_n \in D_n^*(x)$ — a statement
--   about a sequence of points, not a `Filter.limsup` of sets, rendered here via Mathlib's
--   `MapClusterPt`. A set-valued map $x \mapsto D(x)$ is **upper semicontinuous** if, whenever
--   $x_n \to x$ and $a_n \in D(x_n)$, the sequence $(a_n)$ has an accumulation point in $D(x)$ — the
--   book's own Appendix A.2.1 definition, restated (own namespace copy) from
--   `MDPFinance.Semicontinuous.USCSetValued` (chunk `02b`).
--
--   **Formalization Note.** `Dstar` is parametrized by an arbitrary value function `Jval`, so the
--   same definition instantiates $D_n^*$ (at `Jn n`), $D_\infty^*$ (at `Jinf`), and $D^*$ (at `Jlim`)
--   without three separate definitions.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 201, unnumbered display preceding Theorem 7.2.1

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace E]
  [TopologicalSpace A]

/-- `\mathrm{Ls}\,D_n(x)`, the upper limit of a sequence of sets (Bäuerle–Rieder, p. 201, PDF
212): `a` is an accumulation point of *some* sequence `(a_n)` with `a_n \in D_n` for every `n` —
stated exactly as the book's own definition (a statement about a sequence of *points*, not a
`Filter.limsup` of sets), via Mathlib's `MapClusterPt`. -/
def LsSeq (Dn : ℕ → Set A) : Set A :=
  {a | ∃ an : ℕ → A, (∀ n, an n ∈ Dn n) ∧ MapClusterPt a atTop an}

/-- A set-valued map `x ↦ D(x)` is upper semicontinuous (Bäuerle–Rieder, Appendix Definition
A.2.1a, p. 351, PDF 358, restated from `MDPFinance.Semicontinuous.USCSetValued`, chunk `02b`, per
this chunk's file-ownership boundary): sequence-based, as the book's own remark that this is
"slightly more restrictive" than other literature definitions. -/
def USCSetValued (D : E → Set A) : Prop :=
  ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    ∀ as : ℕ → A, (∀ n, as n ∈ D (xs n)) → ∃ a ∈ D x, MapClusterPt a atTop as

/-- A set-valued map is continuous (Bäuerle–Rieder, Appendix Definition A.2.1c) if it is upper
*and* lower semicontinuous — lower semicontinuity restated directly here since Theorem 7.3.6 is
this chunk's only consumer of "continuous" `x ↦ D(x)`. -/
def ContinuousSetValued (D : E → Set A) : Prop :=
  USCSetValued D ∧
    ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
      ∀ a ∈ D x, ∃ as : ℕ → A, (∀ n, as n ∈ D (xs n)) ∧ MapClusterPt a atTop as

/-- `D^*_{J}(x) := \{a \in D(x) \mid a \text{ is a maximum point of } a \mapsto LJ(x,a)\}`
(Bäuerle–Rieder, p. 201, PDF 212, `D_n^*`/`D_\infty^*`/`D^*` all instances of this one shape at
different value functions `J`). -/
def Dstar (M : MarkovDecisionModel E A) (Jval : E → EReal) (x : E) : Set A :=
  {a | a ∈ M.Dx x ∧ ∀ a' ∈ M.Dx x, L M Jval (x, a') ≤ L M Jval (x, a)}

end MDPFinance.Contracting


