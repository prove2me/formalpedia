-- Prove2me | Definitions.Def_OAI_Probability_Ising_Contraction
-- name    : OAI_Probability_Ising_Contraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:03:04.378102+00:00
-- url     : https://prove2.me/theorems/3c5b3ee8-d8bc-4d1c-a007-1d1add79e625
-- title:
--   General pair interactions, loop removal and the contracted comparison graph with induced fields
-- statement:
--   The file builds, from a finite graph with pins, the single finite Ising model on which the comparison of conditional laws is carried out.
--
--   **General pair interactions.** Let $U$ and $E$ be finite sets. A pair interaction $P$ on $U$ with edge set $E$ consists of endpoint maps $l,r:E\to U$ and couplings $K_e\ge0$; loops ($l(e)=r(e)$) and parallel edges are allowed. For a field $h\in\mathbb{R}^U$ and $\sigma\in\{-1,+1\}^U$:
--
--   1. **Energy and weight.**
--
--      $$H^P_h(\sigma)=\sum_{e\in E}K_e\,\sigma_{l(e)}\sigma_{r(e)}+\sum_{u\in U}h_u\sigma_u,\qquad w^P_h(\sigma)=e^{H^P_h(\sigma)} .$$
--
--   2. **Non-loop edges** $E_{\neq}=\{e\in E:\ l(e)\neq r(e)\}$ and the **loop constant** $\kappa(P)=\sum_{e:\ l(e)=r(e)}K_e$; each loop contributes the constant $K_e$ to the energy since $\sigma_u^2=1$.
--
--   3. **Associated finite graph** $\Gamma(P)$: delete the loops and relabel the vertices and the non-loop edges by $\{0,\dots,|U|-1\}$ and $\{0,\dots,|E_{\neq}|-1\}$ through fixed enumerations, keeping endpoints and couplings. It is a loopless graph with nonnegative couplings; parallel edges are kept and nothing is assumed about fields or connectivity.
--
--   4. **Quotient field.** For an equivalence $S$ on a finite set $U$ and $h\in\mathbb{R}^U$, the field on classes $(h/S)(q)=\sum_{u\in q}h_u$.
--
--   **The contracted comparison graph.** Now let $G$ be a finite ferromagnetic graph on $V=\{0,\dots,n-1\}$, $h\in\mathbb{R}^V$, $I,J,F\subseteq V$ and $\tau\in\{-1,+1\}^V$. Let $V_F=V\setminus F$, let $E_F$ be the set of edges with both endpoints in $V_F$, and let $\sim_\varnothing$ be the equivalence on $V_F$ identifying all kept vertices of $I$ with each other and, separately, all kept vertices of $J$ with each other.
--
--   5. **Contracted vertices and kept edges**: the classes $V_F/{\sim_\varnothing}$, and the edges of $E_F$ with their endpoints viewed in $V_F$.
--
--   6. **Contracted interaction**: the pair interaction on $V_F/{\sim_\varnothing}$ with edge set $E_F$, endpoints $e\mapsto([l(e)],[r(e)])$ and couplings $K_e$. An edge inside $I$ or inside $J$ becomes a loop.
--
--   7. **Actual comparison graph, field and terminals**: the finite graph $\Gamma$ of the contracted interaction; the field on it obtained by summing over each class the pin-induced field $h^{F,\tau}_v=h_v+\sum_{e:\,l(e)=v,\,r(e)\in F}K_e\tau_{r(e)}+\sum_{e:\,r(e)=v,\,l(e)\in F}K_e\tau_{l(e)}$; and, for a kept vertex $i$, the index in $\Gamma$ of its class $[i]$.
--
--   When $I,J,F$ are pairwise disjoint and $i\in I$, $j\in J$ are kept vertices, the extreme log-odds of the pinned two-block marginal equals four times the effective coupling between the terminals $[i]$ and $[j]$ in $\Gamma$ with the actual comparison field, while the inverse hyperbolic tangent of the zero-field random-cluster connection probability is the effective coupling of the same graph at zero field. The comparison of conditional laws thus reduces to comparing one fixed finite ferromagnet with its zero-field version.
--
--   **Formalization Note** The Lean names are `PairInteraction`, `interactionEnergy`, `interactionWeight`, `NonloopEdge`, `interactionLoopConstant`, `interactionGraph` (with enumerations given by `Fintype.equivFin`), `ContractedVertex`, `KeptEdge`, `edgeLeftKept`, `edgeRightKept`, `contractedInteraction`, `quotientField`, `actualComparisonGraph`, `actualComparisonField G h I J F τ` and `actualTerminal G I J F i`. The enumerations are noncanonical, so only relabeling-invariant quantities are meaningful.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Contraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Contraction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- A finite pair interaction allowing self-loops and arbitrary vertex and edge labels. -/
structure PairInteraction (V E : Type*) where
  left : E → V
  right : E → V
  coupling : E → ℝ
  coupling_nonneg : ∀ e, 0 ≤ coupling e

noncomputable def interactionEnergy {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) : ℝ :=
  (∑ e, P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e))) +
    ∑ v, h v * spin (σ v)

noncomputable def interactionWeight {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) : ℝ :=
  Real.exp (interactionEnergy P h σ)

abbrev NonloopEdge {V E : Type*} (P : PairInteraction V E) :=
  {e : E // P.left e ≠ P.right e}

noncomputable def interactionLoopConstant {V E : Type*} [Fintype E]
    (P : PairInteraction V E) : ℝ := ∑ e, if P.left e = P.right e then P.coupling e else 0

/-- Relabeling a finite loop-deleted interaction by `Fin` does not introduce
any assumption on the fields or on connectivity. Parallel edges are kept. -/
noncomputable def interactionGraph {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) :
    FiniteGraph (Fintype.card V) (Fintype.card (NonloopEdge P)) where
  left e := Fintype.equivFin V (P.left ((Fintype.equivFin (NonloopEdge P)).symm e).val)
  right e := Fintype.equivFin V (P.right ((Fintype.equivFin (NonloopEdge P)).symm e).val)
  coupling e := P.coupling ((Fintype.equivFin (NonloopEdge P)).symm e).val
  coupling_nonneg e := P.coupling_nonneg _
  no_loops e := by
    intro H
    exact ((Fintype.equivFin (NonloopEdge P)).symm e).property
      ((Fintype.equivFin V).injective H)

abbrev ContractedVertex {n m : ℕ} (G : FiniteGraph n m) (I J F : Finset (Fin n)) :=
  Quotient (comparisonSetoid G I J F ∅)

abbrev KeptEdge {n m : ℕ} (G : FiniteGraph n m) (F : Finset (Fin n)) :=
  {e : Fin m // e ∈ keptEdges G F}

noncomputable def edgeLeftKept {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (e : KeptEdge G F) : KeptVertex F :=
  ⟨G.left e.val, (Finset.mem_filter.mp e.property).2.1⟩

noncomputable def edgeRightKept {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (e : KeptEdge G F) : KeptVertex F :=
  ⟨G.right e.val, (Finset.mem_filter.mp e.property).2.2⟩

noncomputable def contractedInteraction {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) : PairInteraction (ContractedVertex G I J F) (KeptEdge G F) where
  left e := Quotient.mk _ (edgeLeftKept G F e)
  right e := Quotient.mk _ (edgeRightKept G F e)
  coupling e := G.coupling e.val
  coupling_nonneg e := G.coupling_nonneg e.val

/-- The contracted finite field is the SUM of the fields in the identified
class. Common fixed spins have already been removed and contribute through
`pinField`; opposite common signs are never wired together. -/
noncomputable def quotientField {V : Type*} [Fintype V] (S : Setoid V)
    (h : V → ℝ) (q : Quotient S) : ℝ := ∑ v, if Quotient.mk S v = q then h v else 0

noncomputable def actualComparisonGraph {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) := interactionGraph (contractedInteraction G I J F)

noncomputable def actualComparisonField {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n) :=
    fun x => quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)
      ((Fintype.equivFin (ContractedVertex G I J F)).symm x)

noncomputable def actualTerminal {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i : KeptVertex F) :=
    Fintype.equivFin (ContractedVertex G I J F) (Quotient.mk _ i)

end BufferedIsing

end OAI


