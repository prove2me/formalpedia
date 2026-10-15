-- Prove2me | Definitions.Def_OAI_Probability_Ising_EdwardsSokal
-- name    : OAI_Probability_Ising_EdwardsSokal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:56:35.626749+00:00
-- url     : https://prove2.me/theorems/a6c18402-41fb-449c-b604-5b431fb74eb6
-- title:
--   Edwards–Sokal weights on the vertex-deleted graph with separately contracted terminal sets
-- statement:
--   Let $G$ be a finite graph on $V=\{0,\dots,n-1\}$ whose edges $e$ have endpoints $l(e)\neq r(e)$ and couplings $K_e\ge0$. Fix vertex sets $I,J,F\subseteq V$. The vertices of $F$ are *deleted*, not pinned: the kept vertices are $V_F=V\setminus F$ and the kept edges are $E_F=\{e:\ l(e)\notin F,\ r(e)\notin F\}$. For a set $\omega$ of edges let $\sim_\omega$ be the comparison equivalence on $V_F$, the smallest equivalence relation in which any two kept vertices of $I$ are equivalent, any two kept vertices of $J$ are equivalent, and the two endpoints of every edge of $\omega$ joining two kept vertices are equivalent. Its classes are the open clusters of $\omega$ after $I$ and $J$ have each been contracted to a single vertex. Write $p_e=1-e^{-2K_e}$, and let $s\in\{-1,+1\}^{V_F}$ denote a coloring of the kept vertices. The file defines:
--
--   1. **Bond weight.** The independent-bond part of the random-cluster weight (edges of $\omega$ outside $E_F$ are ignored),
--
--      $$\phi(\omega)=\prod_{e\in E_F}\bigl(p_e\,\mathbf{1}[e\in\omega]+(1-p_e)\,\mathbf{1}[e\notin\omega]\bigr).$$
--
--   2. **Joint Edwards–Sokal weight.** $\Phi(\omega,s)=\phi(\omega)$ if $s$ is constant on every class of $\sim_\omega$, and $\Phi(\omega,s)=0$ otherwise.
--
--   3. **Spin marginal.** $\Psi(s)=\sum_{\omega\subseteq E_F}\Phi(\omega,s)$.
--
--   4. **Extension by $-1$.** $\bar s\in\{-1,+1\}^V$ equals $s$ on $V_F$ and $-1$ on $F$; the values on $F$ are immaterial because no kept edge meets $F$.
--
--   5. **Bond compatibility.** $s$ is compatible with $\omega$ if $\bar s_{l(e)}=\bar s_{r(e)}$ for every $e\in\omega$.
--
--   6. **Deleted energy.** The zero-field energy of the graph with $F$ deleted,
--
--      $$H^F(s)=\sum_{e\in E_F}K_e\,\bar s_{l(e)}\,\bar s_{r(e)} .$$
--
--   7. **Contracted zero-field weight.** $w^F_{I,J}(s)=e^{H^F(s)}$ if $s$ is constant on the classes of $\sim_\varnothing$, i.e. constant on $I\setminus F$ and constant on $J\setminus F$, and $w^F_{I,J}(s)=0$ otherwise.
--
--   These are the ingredients of the finite Edwards–Sokal coupling with $q=2$ on the vertex-deleted graph in which $I$ and $J$ are contracted separately. Summing $\Phi(\omega,\cdot)$ over colorings gives the random-cluster weight $2^{k(\omega)}\phi(\omega)$, where $k(\omega)$ is the number of classes of $\sim_\omega$, and the one-edge identity $e^{Kxy}=e^{K}\bigl((1-p)+p\,\mathbf{1}[x=y]\bigr)$ for $x,y\in\{-1,+1\}$ and $p=1-e^{-2K}$ turns $\Psi$ into $e^{-\sum_{e\in E_F}K_e}\,w^F_{I,J}$. This identifies the terminal connection probability of the random-cluster model with a zero-field spin correlation of the contracted graph.
--
--   **Formalization Note** The Lean names are `fkEdgeWeight`, `jointColorWeight`, `comparisonSpinWeight`, `extendKept` (with the simp lemma `extendKept_apply`), `BondCompatible`, `deletedEnergy` and `contractedZeroWeight`. Colorings of kept vertices are functions `KeptVertex F → Bool` on the subtype of vertices outside $F$, and $\sim_\omega$ is `comparisonSetoid G I J F ω` from the base definitions. Unlike the base random-cluster weight `fkWeight`, the bond weight here omits the cluster factor $2^{k(\omega)}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/EdwardsSokal.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/EdwardsSokal.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Independent bond part of the comparison FK weight; the cluster factor
is supplied by summing compatible fair cluster colors. -/
noncomputable def fkEdgeWeight {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (ω : Finset (Fin m)) : ℝ :=
  ∏ e ∈ keptEdges G F,
    if e ∈ ω then 1 - Real.exp (-2 * G.coupling e) else Real.exp (-2 * G.coupling e)

noncomputable def jointColorWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (σ : KeptVertex F → Bool) : ℝ :=
  if Respects (comparisonSetoid G I J F ω) σ then fkEdgeWeight G F ω else 0

noncomputable def comparisonSpinWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) : ℝ :=
  ∑ ω ∈ (keptEdges G F).powerset, jointColorWeight G I J F ω σ

/-- Extend a coloring from the vertex-DELETED graph. The values at deleted
vertices are immaterial: every incident edge is absent from keptEdges. -/
def extendKept {n : ℕ} (F : Finset (Fin n)) (σ : KeptVertex F → Bool) : Spins n :=
  fun v => if hv : v ∉ F then σ ⟨v, hv⟩ else false

@[simp] lemma extendKept_apply {n : ℕ} (F : Finset (Fin n))
    (σ : KeptVertex F → Bool) (v : KeptVertex F) :
    extendKept F σ v.val = σ v := by
  simp [extendKept, v.property]

def BondCompatible {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (σ : KeptVertex F → Bool) (ω : Finset (Fin m)) : Prop :=
  ∀ e ∈ ω, extendKept F σ (G.left e) = extendKept F σ (G.right e)

noncomputable def deletedEnergy {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (σ : KeptVertex F → Bool) : ℝ :=
  ∑ e ∈ keptEdges G F,
    G.coupling e * spin (extendKept F σ (G.left e)) * spin (extendKept F σ (G.right e))

/-- Zero-field Ising weight on the vertex-deleted graph, with I,J separately
contracted by restricting each to constant spin assignments. -/
noncomputable def contractedZeroWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) : ℝ :=
  if Respects (comparisonSetoid G I J F ∅) σ then Real.exp (deletedEnergy G F σ) else 0

end BufferedIsing

end OAI


