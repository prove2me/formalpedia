-- Prove2me | Definitions.Def_TwoItemMenu1393_Main_Model
-- name    : TwoItemMenu1393_Main_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:23:31.431392+00:00
-- url     : https://prove2.me/theorems/d39c3b57-9b1d-484f-b998-b9416a733822
-- title:
--   Two-item utilities, direct mechanisms, menus and complexity
-- statement:
--   A mechanism has a finite nonnegative convex utility $u$ on $\mathbb R^2$, normalized by $u(0)=0$, with every subgradient in $[0,1]^2$, and a Borel selection $g(v)\in\partial u(v)$. Its payment is $p(v)=g(v)\cdot v-u(v)$ and its revenue under a law $F$ is $\mathrm{Rev}_F(u,g)=\int p\,dF$. The supremum over all mechanisms is $\mathrm{OPT}(F)$.
--
--   Allocations are marginal probabilities, so $(1,1)$ is allowed. A menu is any set of allocation-price pairs with nonnegative prices. Its envelope is the supremum of zero and all offered affine utilities. A finite implementation must reproduce the utility on the square and contain every actual selected outcome, including at atoms. Null is available without being counted. Define
--   $$M_F(\varepsilon)=\inf\{N\in\mathbb N: \exists (u,g)\text{ of size at most }N,\ \mathrm{Rev}_F(u,g)\ge\mathrm{OPT}(F)-\varepsilon\},\quad M(\varepsilon)=\sup_F M_F(\varepsilon).$$
--   The module also defines direct IC/IR mechanisms, global extensions, tangent sub-menus, discounts, and the IC slack $u(t)-u(v)-g(v)\cdot(t-v)$. These interfaces are shared across the upper and lower bounds. Real revenues are used only with bounded Borel payments; complexity uses extended nonnegative reals. All subgradients use the published general subgradient definition.
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), §2, pp. 4–5; B.1–B.3, pp. 16–19; Definitions B.1, B.3, B.4, B.5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf

import Mathlib
import Definitions.Def_LinearOptimization_Subgradient
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace TwoItemMenu1393.Main

/-! Chan–Guo–Thach, STOC 2027 submission #1393 (October 2026),
§2 pp. 4–5; Appendix B.1–B.3 pp. 16–19, Definitions B.1, B.3–B.5.
The plane has its Euclidean norm and Borel measurable structure. -/
abbrev Vec := EuclideanSpace ℝ (Fin 2)
def vec (x y : ℝ) : Vec := WithLp.toLp 2 ![x, y]
def square (R : ℝ) : Set Vec := {v | ∀ i, 0 ≤ v i ∧ v i ≤ R}
abbrev TypeSquare := {v : Vec // v ∈ square 1}
def dot (v w : Vec) : ℝ := ∑ i, v i * w i

/-- The published general subgradient predicate, transported along the coordinate equivalence.
On the whole plane its domain-membership conjunct imposes no condition. -/
def Subgradient (u : Vec → ℝ) (v q : Vec) : Prop :=
  LinearOptimization.IsSubgradientOn (fun x => u (WithLp.toLp 2 x)) Set.univ
    (WithLp.ofLp q) (WithLp.ofLp v)

/-- Definition B.1: finite, globally nonnegative and convex; *all* subgradients are bounded. -/
def Utility (u : Vec → ℝ) : Prop :=
  (∀ v, 0 ≤ u v) ∧ ConvexOn ℝ Set.univ u ∧ u 0 = 0 ∧
    ∀ v q, Subgradient u v q → q ∈ square 1

def Selection (u : Vec → ℝ) (g : Vec → Vec) : Prop :=
  Measurable g ∧ ∀ v, Subgradient u v (g v)

structure Mechanism where
  u : Vec → ℝ
  g : Vec → Vec

def Admissible (M : Mechanism) : Prop := Utility M.u ∧ Selection M.u M.g
def payment (M : Mechanism) (v : Vec) : ℝ := dot (M.g v) v - M.u v
def slack (M : Mechanism) (v t : Vec) : ℝ := M.u t - M.u v - dot (M.g v) (t - v)

/-- Borel laws on the continuous square, represented as measures on the plane. -/
def Law (F : Measure Vec) : Prop := IsProbabilityMeasure F ∧ F (square 1)ᶜ = 0
def FiniteSupport (F : Measure Vec) : Prop :=
  ∃ V : Finset Vec, F (↑V : Set Vec)ᶜ = 0
def revenue (F : Measure Vec) (M : Mechanism) : ℝ := ∫ v, payment M v ∂F

/-- Real supremum: on laws and admissible mechanisms the set contains zero and lies in [0,2].
Neither those bounds nor optimality/attainment are fields of the model. -/
def optimum (F : Measure Vec) : ℝ := sSup {r | ∃ M, Admissible M ∧ revenue F M = r}

abbrev Entry := Vec × ℝ
def nullEntry : Entry := (0, 0)
def ValidEntry (e : Entry) : Prop := e.1 ∈ square 1 ∧ 0 ≤ e.2
def entryUtility (e : Entry) (v : Vec) : ℝ := dot e.1 v - e.2
def ValidMenu (S : Set Entry) : Prop := ∀ e ∈ S, ValidEntry e

/-- Include zero *inside* the supremum: the empty menu gives zero, never the
conditionally complete real supremum of an empty set. Valid menus give a bounded set. -/
def envelope (S : Set Entry) (v : Vec) : ℝ :=
  sSup (insert 0 ((fun e => entryUtility e v) '' S))
def outcome (M : Mechanism) (v : Vec) : Entry := (M.g v, payment M v)
def Implements (M : Mechanism) (S : Set Entry) : Prop :=
  (∀ v ∈ square 1, M.u v = envelope S v) ∧
    ∀ v ∈ square 1, outcome M v ∈ insert nullEntry S
def MenuSizeAtMost (M : Mechanism) (N : ℕ) : Prop :=
  ∃ S : Finset Entry, S.card ≤ N ∧ (∀ e ∈ S, ValidEntry e) ∧ Implements M (↑S)

/-- Extended nonnegative reals preserve infinity for empty feasible sets. -/
def menuSize (M : Mechanism) : ℝ≥0∞ :=
  sInf {r | ∃ N : ℕ, MenuSizeAtMost M N ∧ r = (N : ℝ≥0∞)}
def complexity (F : Measure Vec) (ε : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ (N : ℕ) (M : Mechanism), Admissible M ∧ MenuSizeAtMost M N ∧
    optimum F - ε ≤ revenue F M ∧ r = (N : ℝ≥0∞)}
def worstComplexity (ε : ℝ) : ℝ≥0∞ := ⨆ (F : Measure Vec) (_ : Law F), complexity F ε

def tangentEntry (M : Mechanism) (s : Vec) : Entry := (M.g s, payment M s)
def subMenu (M : Mechanism) (J : Finset Vec) : Set Entry := tangentEntry M '' (↑J)
def subUtility (M : Mechanism) (J : Finset Vec) : Vec → ℝ := envelope (subMenu M J)
def discount (δ : ℝ) (S : Set Entry) : Set Entry :=
  (fun e => (e.1, (1 - δ) * e.2)) '' S
def GlobalEntrySelection (M : Mechanism) (S : Set Entry) : Prop :=
  M.u = envelope S ∧ Selection M.u M.g ∧
    ∀ v, outcome M v ∈ insert nullEntry S

structure DirectMechanism where
  q : TypeSquare → Vec
  p : TypeSquare → ℝ
def directUtility (D : DirectMechanism) (v : TypeSquare) : ℝ := dot (D.q v) v - D.p v
def DirectAdmissible (D : DirectMechanism) : Prop :=
  Measurable D.q ∧ Measurable D.p ∧ (∀ v, D.q v ∈ square 1) ∧
    (∀ v w : TypeSquare, dot (D.q w) v - D.p w ≤ directUtility D v) ∧
    ∀ v, 0 ≤ directUtility D v
def directEnvelope (D : DirectMechanism) (v : Vec) : ℝ :=
  sSup (insert 0 (Set.range (fun w : TypeSquare => dot (D.q w) v - D.p w)))
def directRestriction (M : Mechanism) : DirectMechanism :=
  ⟨fun v => M.g v, fun v => payment M v⟩

end TwoItemMenu1393.Main


