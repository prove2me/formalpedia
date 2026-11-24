-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_GeneralNetwork
-- name    : SRAudit_TwoPhase_Supplement_GeneralNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:25:30.894793+00:00
-- url     : https://prove2.me/theorems/834bc94e-388c-405c-bcef-509439a6a4dd
-- title:
--   Appendix H.1, OA-53–OA-54, Definition H.1 — general directed supply networks, path-based dependents, ⊕ and ⊖, V*, LVUS, symmetry and Assumptions D.1–D.2
-- statement:
--   Appendix H: a supply network is a finite directed graph $g=(W_g,E_g)$ whose vertices are firms; the arc $ji$ means "$j$ supplies $i$". The buyer is a fixed vertex $c$, $S_g=W_g\setminus\{c\}$ are the suppliers, and $g\in G$ when $c\in W_g$, $c$ is reachable from every supplier and every supplier has positive outdegree.
--
--   1. **Dependents** $D_g(i)$: the suppliers $j$ such that $i$ lies on every directed path from a raw-material supplier (a supplier with no upstream supplier) to $c$ that traverses $j$; so $i\in D_g(i)$.
--   2. **States** $\gamma=(g,U)$, $U\subseteq S_g$; $\gamma\oplus i=(g,U\setminus\{i\})$; $\gamma\ominus i=(g[W_g\setminus D_g(i)],\,U\cap W_{g'})$ (fn. 5–6).
--   3. **Auditing MDP**: actions $\mathrm{pp},\mathrm{ar}(i),\mathrm{ad}(i)$, $\zeta(\gamma)=|U_\gamma|uwz$, $V^*$ and $\widetilde V^*$ by (1)–(5), optimal policies (argmax at every state); the production profit $\pi$ is a function of the network.
--   4. $\nabla(\gamma,i)=\pi(\gamma)-\pi(\gamma\ominus i)$, LVUS, $\widetilde V^*(\gamma,\mathrm{rp})=\pi(\gamma)-c_{rp}|U_\gamma|$, reachable states $R^+(\gamma)$.
--   5. **Definition H.1**: $i,i'\in W_g$ are symmetric in $\gamma$ if some bijection $\theta$ of $W_g$ with $ji\in E_g\iff\theta(j)\theta(i)\in E_g$ and $k\in U\iff\theta(k)\in U$ for every supplier $k$ maps $i$ to $i'$.
--   6. **Assumptions D.1 and D.2** on general networks, with symmetry in the sense of Definition H.1.
--
--   **Formalization Note** Directed paths have no repeated vertex. The state type allows any finite digraph; $G$ (well-formedness) is a separate predicate, imposed where the source's assumptions range over $\Gamma$.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-53–OA-54, Appendix H.1, fns. 5–6, Definition H.1

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

/-! Appendix H (OA-53–OA-54): the auditing model on a general supply network, a finite directed
graph whose vertices are firms (the buyer `c` and the suppliers) and whose arc `(j, i)` means
"`j` supplies `i`". Vertices are labelled by a type `V`; the buyer is a fixed vertex `c : V`. -/

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

variable {V : Type} [DecidableEq V]

/-- A finite directed graph `g = (W_g, E_g)` with `E_g ⊆ W_g × W_g`. -/
structure GNet (V : Type) [DecidableEq V] where
  W : Finset V
  E : Finset (V × V)
  hE : ∀ e ∈ E, e.1 ∈ W ∧ e.2 ∈ W

/-- The suppliers `S_g = W_g \ {c}`. -/
def GNet.S (c : V) (g : GNet V) : Finset V := g.W.erase c

/-- A supply network of `G` (OA-53): the buyer `c` is a vertex, `c` is reachable from every supplier,
and every supplier has positive outdegree. -/
def GNet.WellFormed (c : V) (g : GNet V) : Prop :=
  c ∈ g.W ∧ (∀ i ∈ g.S c, Relation.TransGen (fun x y => (x, y) ∈ g.E) i c) ∧
    (∀ i ∈ g.S c, ∃ k, (i, k) ∈ g.E)

/-- A raw-material supplier: a supplier with no upstream supplier. -/
def GNet.IsRaw (c : V) (g : GNet V) (s : V) : Prop := s ∈ g.S c ∧ ∀ k, (k, s) ∉ g.E

/-- A directed path (no repeated vertex) from a raw-material supplier to the buyer `c`. -/
def GNet.IsRawPath (c : V) (g : GNet V) (p : List V) : Prop :=
  p.Nodup ∧ p.IsChain (fun x y => (x, y) ∈ g.E) ∧
    (∃ s, p.head? = some s ∧ g.IsRaw c s) ∧ p.getLast? = some c

open Classical in
/-- The dependents `D_g(i)` (OA-53): the suppliers `j` such that `i` lies on every directed path from a
raw-material supplier to the buyer that traverses `j`. In particular `i ∈ D_g(i)` for `i ∈ S_g`. -/
noncomputable def GNet.dependents (c : V) (g : GNet V) (i : V) : Finset V :=
  (g.S c).filter (fun j => ∀ p : List V, g.IsRawPath c p → j ∈ p → i ∈ p)

open Classical in
/-- The subgraph of `g` induced by `g.W \ D` (used by `⊖`, fn. 6 of OA-54). -/
noncomputable def GNet.removeVertices (g : GNet V) (D : Finset V) : GNet V :=
  ⟨g.W \ D, g.E.filter (fun e => e.1 ∉ D ∧ e.2 ∉ D), by
    intro e he
    simp only [Finset.mem_filter] at he
    exact ⟨Finset.mem_sdiff.2 ⟨(g.hE e he.1).1, he.2.1⟩, Finset.mem_sdiff.2 ⟨(g.hE e he.1).2, he.2.2⟩⟩⟩

/-- A state `γ = (g, U)` with `U ⊆ S_g` the unaudited suppliers (OA-53). -/
structure HState (V : Type) [DecidableEq V] (c : V) where
  g : GNet V
  U : Finset V
  hU : U ⊆ g.S c

variable {c : V}

/-- A state of `Γ`: its network lies in `G`. -/
def HState.WellFormed (γ : HState V c) : Prop := γ.g.WellFormed c

/-- `γ ⊕ i = (g, U \ {i})` (fn. 5, OA-53). -/
def HState.vet (γ : HState V c) (i : V) : HState V c :=
  ⟨γ.g, γ.U.erase i, (Finset.erase_subset i γ.U).trans γ.hU⟩

/-- `γ ⊖ i = (g[W_g \ D_g(i)], U ∩ W_{g'})` (fn. 6, OA-54). -/
noncomputable def HState.drop (γ : HState V c) (i : V) : HState V c :=
  ⟨γ.g.removeVertices (γ.g.dependents c i), γ.U ∩ (γ.g.W \ γ.g.dependents c i), by
    intro x hx
    rcases Finset.mem_inter.1 hx with ⟨hxU, hxW⟩
    have hxS := γ.hU hxU
    simp only [GNet.S, Finset.mem_erase] at hxS ⊢
    exact ⟨hxS.1, hxW⟩⟩

theorem HState.vet_card_lt (γ : HState V c) (i : V) (hi : i ∈ γ.U) :
    (γ.vet i).U.card < γ.U.card := by
  simpa [HState.vet] using Finset.card_erase_lt_of_mem hi

theorem HState.drop_card_lt (γ : HState V c) (i : V) (hi : i ∈ γ.U) :
    (γ.drop i).U.card < γ.U.card := by
  classical
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset Finset.inter_subset_left).2 ⟨i, hi, ?_⟩
  have hiD : i ∈ γ.g.dependents c i := by
    simp only [GNet.dependents, Finset.mem_filter]
    exact ⟨γ.hU hi, fun _ _ h => h⟩
  simp [hiD]

/-- Actions `pp`, `ar(i)`, `ad(i)` on a general network. -/
inductive HAction (V : Type) | pp | ar (i : V) | ad (i : V)

/-- Admissible actions `X_γ`. -/
def HAdmissible (γ : HState V c) : HAction V → Prop
  | .pp => True
  | .ar i => i ∈ γ.U
  | .ad i => i ∈ γ.U

/-- An auditing policy and admissibility (`Ξ`). -/
def HPolicy (V : Type) [DecidableEq V] (c : V) := HState V c → HAction V

def HIsAdmissible (ξ : HPolicy V c) : Prop := ∀ γ, HAdmissible γ (ξ γ)

/-- `Ṽ*(γ, pp) = π(γ) − ζ(γ)` with `ζ(γ) = |U_γ| u w z`; the production profit `π` is a function of the
supply network. -/
def ppValueH (P : Params) (π : GNet V → ℝ) (γ : HState V c) : ℝ :=
  π γ.g - γ.U.card * (P.u * P.w * P.z)

/-- `V*` on general networks: the recursion (1)–(5). -/
noncomputable def VstarH (P : Params) (π : GNet V → ℝ) (γ : HState V c) : ℝ :=
  if h : γ.U.Nonempty then
    max (ppValueH P π γ)
      (γ.U.attach.sup' (by simpa using h) (fun i =>
        max (-P.a - P.u * P.r + VstarH P π (γ.vet i.val))
            (-P.a + (1 - P.u) * VstarH P π (γ.vet i.val) + P.u * VstarH P π (γ.drop i.val))))
  else ppValueH P π γ
termination_by γ.U.card
decreasing_by
  all_goals
    first | exact γ.vet_card_lt i.val i.property | exact γ.drop_card_lt i.val i.property

/-- `Ṽ*(γ, x)` on general networks (junk `0` at inadmissible actions). -/
noncomputable def QstarH (P : Params) (π : GNet V → ℝ) (γ : HState V c) : HAction V → ℝ
  | .pp => ppValueH P π γ
  | .ar i => if i ∈ γ.U then -P.a - P.u * P.r + VstarH P π (γ.vet i) else 0
  | .ad i => if i ∈ γ.U then
      -P.a + (1 - P.u) * VstarH P π (γ.vet i) + P.u * VstarH P π (γ.drop i) else 0

/-- An optimal auditing policy on general networks (argmax at every state). -/
def IsOptimalH (P : Params) (π : GNet V → ℝ) (ξ : HPolicy V c) : Prop :=
  HIsAdmissible ξ ∧ ∀ γ, QstarH P π γ (ξ γ) = VstarH P π γ

/-- `∇(γ, i) = π(γ) − π(γ ⊖ i)`. -/
noncomputable def nablaH (π : GNet V → ℝ) (γ : HState V c) (i : V) : ℝ := π γ.g - π (γ.drop i).g

/-- `i` is an LVUS in `γ` (Definition 1). -/
def IsLVUSH (π : GNet V → ℝ) (γ : HState V c) (i : V) : Prop :=
  i ∈ γ.U ∧ ∀ i' ∈ γ.U, nablaH π γ i ≤ nablaH π γ i'

/-- `Ṽ*(γ, rp) = π(γ) − c_rp |U_γ|`. -/
def rpValueH (P : Params) (π : GNet V → ℝ) (γ : HState V c) : ℝ := π γ.g - crp P * γ.U.card

/-- `R+(γ)`: states reached from `γ` (including `γ`) by a finite chain of `⊕`/`⊖` transitions. -/
def ReachH (γ γ' : HState V c) : Prop :=
  Relation.ReflTransGen (fun x y : HState V c => ∃ i ∈ x.U, y = x.vet i ∨ y = x.drop i) γ γ'

/-- Definition H.1 (OA-54): `i, i' ∈ W_g` are symmetric in `γ` if some isomorphism of `γ` with itself
(a bijection `θ` of `W_g` preserving arcs in both directions and the unaudited status of every
supplier) maps `i` to `i'`. -/
def SymmetricH (γ : HState V c) (i i' : V) : Prop :=
  i ∈ γ.g.W ∧ i' ∈ γ.g.W ∧
  ∃ θ : V → V, Set.BijOn θ ↑γ.g.W ↑γ.g.W ∧
    (∀ x ∈ γ.g.W, ∀ y ∈ γ.g.W, (x, y) ∈ γ.g.E ↔ (θ x, θ y) ∈ γ.g.E) ∧
    (∀ x ∈ γ.g.S c, x ∈ γ.U ↔ θ x ∈ γ.U) ∧ θ i = i'

/-- Assumption D.1 on general networks: for every state of `Γ` and `i, i' ∈ U_γ` with `i' ∉ D_γ(i)`,
`∇(γ, i') ≤ ∇(γ ⊖ i, i')`. -/
def AssumptionD1H (π : GNet V → ℝ) : Prop :=
  ∀ γ : HState V c, γ.WellFormed → ∀ i ∈ γ.U, ∀ i' ∈ γ.U, i' ∉ γ.g.dependents c i →
    nablaH π γ i' ≤ nablaH π (γ.drop i) i'

/-- Assumption D.2 on general networks, with symmetry in the sense of Definition H.1. -/
def AssumptionD2H (π : GNet V → ℝ) : Prop :=
  ∀ γ : HState V c, γ.WellFormed → ∀ i, IsLVUSH π γ i → ∀ i' ∈ γ.U, ¬ SymmetricH γ i' i →
    i ∉ γ.g.dependents c i' →
    ∀ i'' ∈ (γ.drop i').U, nablaH π (γ.drop i') i ≤ nablaH π (γ.drop i') i''

end SRAudit.TwoPhase.Supplement


