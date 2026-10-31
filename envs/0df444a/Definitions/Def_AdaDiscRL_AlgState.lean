-- Prove2me | Definitions.Def_AdaDiscRL_AlgState
-- name    : AdaDiscRL_AlgState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:51.16798+00:00
-- url     : https://prove2.me/theorems/f7bc5ad4-cb13-4488-b0d8-b258c662e798
-- title:
--   State of the adaptive partition, relevant balls and the greedy selection rule
-- statement:
--   At each step $h$ the algorithms keep a finite tree $\mathcal T_h$ of activated regions ("balls") of the hierarchical partition. Its leaves are the **active balls** $\mathcal P_h$; for every ball they keep the count $n_h(B)$ (selections of $B$ or its ancestors), the estimate $\overline{\mathbf Q}_h(B)$, and for AdaMB the reward estimate $\bar r_h(B)$, the transition estimate $\overline{\mathbf T}_h(\cdot\mid B)$ on the state cells of level $\ell(B)$, and $\widetilde{\mathbf V}_h(A)$ on state cells $A$.
--
--   - **Relevant balls:** $\mathrm{RELEVANT}_h(x)=\{\text{active } B:\ (x,a)\in B \text{ for some } a\}$.
--   - **Induced state partition** (Eq. (5)): the state cells $\mathcal S(B)$ of active balls not strictly containing the state cell of another active ball.
--   - **Greedy selection:** $B_h=\arg\max_{B\in\mathrm{RELEVANT}_h(x)}\overline{\mathbf Q}_h(B)$, ties broken by an arbitrary rule.
--   - **Refine partition:** when a ball $B$ is split, its children enter the tree and inherit its count and estimates; a child's transition estimate is $\overline{\mathbf T}(A\mid\text{child})=2^{-d_{\mathcal S}}\,\overline{\mathbf T}(A^{par}\mid B)$, and a new state cell inherits $\widetilde{\mathbf V}$ of $\mathcal S(B)$.
--
--   **Formalization Note** Statistics are kept for all tree nodes (split balls keep frozen values). `EpData` is one episode's data $(X_1,\dots,X_{H+1};A_1,\dots,A_H;R_1,\dots,R_H)$.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §3.1–3.3, pp.14–17; Algorithm 1, p.13; §3.4, p.19; Table 2, p.36

import Mathlib
import Definitions.Def_AdaDiscRL_HierPartition

namespace AdaDiscRL

open Classical

/-- **The state of the adaptive partition at one step `h`** (arXiv:2110.15843v3, §3.1–3.3,
pp.14–17, and Table 2, p.36): the tree `𝒯_h` of activated nodes of the hierarchical partition
(the active balls `P_h` are its leaves, the others are inactive parent balls), and for every node
the statistics `n_h(B)` (selections of `B` or its ancestors), `Q̄_h(B)`, `r̄_h(B)`,
`T̄_h(· | B)` (a weight on the state cells of level `ℓ(B)`), plus `Ṽ_h(A)` on state cells `A`
(AdaMB, Eq. (7)).

**Formalization Note.** Statistics are kept for every node; a node that is split keeps its
frozen statistics (Lemma B.1 speaks of parent balls). AdaQL ignores `rbar`, `Tbar`, `Vt`. -/
structure Stats (S ι : Type*) where
  tree : Finset ι
  n : ι → ℕ
  Q : ι → ℝ
  rbar : ι → ℝ
  Tbar : ι → Set S → ℝ
  Vt : Set S → ℝ

/-- The algorithm state after an episode: one `Stats` per step `h : Fin H` (paper step `h + 1`). -/
abbrev AlgState (S ι : Type*) (H : ℕ) := Fin H → Stats S ι

/-- The data observed in one episode: states `X_1, …, X_{H+1}` (`Fin (H+1)`, index `i` is the
paper's `i + 1`), actions `A_1, …, A_H` and rewards `R_1, …, R_H`. -/
abbrev EpData (S A : Type*) (H : ℕ) := (Fin (H + 1) → S) × (Fin H → A) × (Fin H → ℝ)

variable {S A ι : Type*} [MeasurableSpace S] [MeasurableSpace A]
  {D : S × A → S × A → ℝ} {dS Lmax : ℕ}

/-- `B` is an active ball (a leaf of the tree): it is in the tree and none of its children is. -/
def isActive (P : HierPartition S A ι D dS Lmax) (st : Stats S ι) (B : ι) : Prop :=
  B ∈ st.tree ∧ ∀ C ∈ P.children B, C ∉ st.tree

/-- `RELEVANT(x) = {active B | (x, a) ∈ B for some a ∈ A}` (§3.2, p.16). -/
noncomputable def relevant (P : HierPartition S A ι D dS Lmax) (st : Stats S ι) (x : S) :
    Finset ι :=
  st.tree.filter (fun B => isActive P st B ∧ ∃ a, (x, a) ∈ P.region B)

/-- The induced state partition `S(P_h)` (Eq. (5), p.15): the state cells `S(B)` of active balls
`B` for which no active ball has a strictly smaller state cell. -/
def minCells (P : HierPartition S A ι D dS Lmax) (st : Stats S ι) : Set (Set S) :=
  {X | ∃ B, isActive P st B ∧ P.sCell B = X ∧ ¬ ∃ B', isActive P st B' ∧ P.sCell B' ⊂ X}

/-- A tie-breaking rule for `argmax`: `choose F f` is a maximizer of `f` over a nonempty finite
set `F` (any tie-breaking, §3.2, p.16). -/
def IsArgmaxRule (choose : Finset ι → (ι → ℝ) → ι) : Prop :=
  ∀ (F : Finset ι) (f : ι → ℝ), F.Nonempty → choose F f ∈ F ∧ ∀ B ∈ F, f B ≤ f (choose F f)

/-- **Greedy selection rule** (Algorithm 1 line 7, p.13; §3.2, p.16):
`B_h = argmax_{B ∈ RELEVANT_h(x)} Q̄_h(B)`, ties broken by `choose`. -/
noncomputable def selBall {H : ℕ} (P : HierPartition S A ι D dS Lmax)
    (choose : Finset ι → (ι → ℝ) → ι) (σ : AlgState S ι H) (h : Fin H) (x : S) : ι :=
  choose (relevant P (σ h) x) (σ h).Q

/-- **Refine Partition** (Algorithm 1 lines 11–14, p.13; §3.4, p.19): add the children of `B` to
the tree; each child inherits the count, `Q̄` and `r̄` of `B`; its transition estimate is
`T̄(A | child) = 2^{−d_S} T̄(A^{par} | B)` on the state cells `A` of level `ℓ(B) + 1`, where `A^{par}`
is the cell of level `ℓ(B)` containing `A`; and a state cell of a child that is not yet in `S(P_h)`
inherits `Ṽ` of `S(B)`. -/
noncomputable def splitStats (P : HierPartition S A ι D dS Lmax) (st : Stats S ι) (B : ι) :
    Stats S ι where
  tree := st.tree ∪ P.children B
  n := fun C => if C ∈ P.children B then st.n B else st.n C
  Q := fun C => if C ∈ P.children B then st.Q B else st.Q C
  rbar := fun C => if C ∈ P.children B then st.rbar B else st.rbar C
  Tbar := fun C => if C ∈ P.children B then
      (fun X => if X ∈ P.cellsAt (P.level B + 1) then
        (2 : ℝ) ^ (-(dS : ℤ)) * ∑ᶠ (Y : Set S) (_ : X ⊆ Y), st.Tbar B Y else 0)
    else st.Tbar C
  Vt := fun X =>
    if (∃ C ∈ P.children B, P.sCell C = X) ∧ X ∉ minCells P st then st.Vt (P.sCell B)
    else st.Vt X

end AdaDiscRL


