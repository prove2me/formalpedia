-- Prove2me | Definitions.Def_TwMSOCount_Main_Tables
-- name    : TwMSOCount_Main_Tables
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:45:34.232291+00:00
-- url     : https://prove2.me/theorems/13692141-88a6-48c4-a0d3-58f7d1ee8a30
-- title:
--   Tests, state maps (Definition 4.1), separator contexts, the graph and collection tables, recurrences (3)–(8), defining classes and expanded descriptions
-- statement:
--   **Tests (§4.1).** On a $B$-boundaried graph and $Q\subseteq B$: $\mathrm{NoEdge}_Q$ ($\iota(Q)$ spans no edge), $\mathrm{Piece}_Q$ ($\mathrm{NoEdge}_Q$ and $H - \iota(Q)$ nonempty and connected), $\mathrm{Width}_k$ ($\mathrm{tw}(H)\le k$), and $\Phi_{B,B_S,N}$ on graphs with names $B\cup N$, here given by its meaning from Appendix C.2: the first feasible eligible partition of the old boundary $B$ has first part $B_S$ and its farthest minimum internal separator, of size at most $(k+1)-|B_S|$, is $\iota^+(N)$ or $\iota^+(N\setminus\{s_1\})$.
--
--   **State maps (Definition 4.1).** A state map assigns each colored $B$-boundaried graph a state in a finite set $T_B$ such that (i) states are invariant under color- and label-preserving isomorphism; (ii) for a defined gluing, edge insertion or forgetting, the input states determine the result state; (iii) graphs with the same state in $T_B$ have the same boundary colors and adjacency and agree on $\mathrm{Width}_k$, $\mathrm{NoEdge}_Q$, $\mathrm{Piece}_Q$, on $\Phi_{B',B_S,N}$ (when $B = B'\cup N$) and, for $B=\emptyset$, on $\psi$. States are coded by natural numbers; $\tau \models \varphi$ and the induced operations $\mathrm{glue}_J$, $\mathrm{add}_F$, $\mathrm{forget}_N$ are read off graphs of the given states.
--
--   **Tables (§4.2–4.3).** A **separator context** $\gamma = (B, B_S, N, \chi^+)$ has $|B|\le 6(k+1)$, $B_S\subseteq B$, $N$ the first $j\ge1$ labels of $\Lambda_k\setminus B$, $|J|\le k+2$ and a label coloring $\chi^+$. A **collection** with inherited labels $I\subseteq B\setminus B_S$ is a $(J\cup I)$-boundaried graph with colors $\chi^+$, no edge inside $S=\iota(J)$, and every component $D$ of $K-S$ with $|D\cap\iota(I)|\le\lfloor 2|B|/3\rfloor$ and $\mathrm{tw}(K[D\cup S])\le k$. The graph table $G_B(m,\tau)$ and collection table $U_\gamma(I,m,\tau)$ are the solutions of
--   $$G_B(0,\tau)=\sum_{F}\,[\mathrm{tw}(H_{B,F})\le k,\ \mathrm{st}=\tau]\,\omega_{\chi_B}(F),\qquad U_\gamma(\emptyset,0,\tau)=[\tau=\mathrm{st}_J(K^0_J)],$$
--   $$U_\gamma(I,m,\tau)=\sum_{(I_1,m_1)\in A(I,m)}\mathrm{alloc}_I(m,m_1)\!\!\sum_{\mathrm{glue}_J(\tau_1,\tau_2)=\tau}\!\! G^{\mathrm{piece}}_\gamma(I_1,m_1,\tau_1)\,U_\gamma(I\setminus I_1,m-m_1,\tau_2),$$
--   $$G_B(m,\tau)=\sum_{(\gamma,F,\tau_{\mathrm{col}})\in R_B(\tau),\ |N|\le m}\binom{m-1}{|N|-1}\,w_\gamma(F)\,U_\gamma(B\setminus B_S,\,m-|N|,\,\tau_{\mathrm{col}})\quad(m>0),$$
--   with $A(I,m)$, $\mathrm{alloc}_I$, the piece filter (4), the parent test (7) and $w_\gamma(F)=\omega_{\chi^+}(F)\prod_{s\in N}\lambda_{\chi^+(s)}$ as in §4.3. The **defining classes** (Definition B.3) are the stored graphs on $V_B\sqcup[m]$ of width $\le k$ and state $\tau$, and the stored collections on $V_{J\cup I}\sqcup[m]$ of state $\tau$. An **expanded description** (Definition B.4) of an entry on an actual label set $L$ is a finite tree of recurrence choices (graph-base leaf, empty-collection leaf, parent node with $L_{\mathrm{new}}\ni\min L$, collection node with an $m_1$-subset $L_1$); it has an output graph, a weight (product of local factors), a number of calls, and, for given tables, the probability with which the recursive sampler (Algorithm 2) makes its choices.
--
--   **Formalization Note.** `StateMap`, `StateMap.IsStateMap ψ`, `Ctx`, `Entry`, `rhs`, `SolvesRecurrences` (the tables are any solution of (3)–(8) at every existing entry), `Uses`, `Entry.rank`, `RankLt`, `classSum`, `IsCollection`, `ExpDesc` with `output`, `weight`, `calls`, `pathProb`, and `rootGraph`. Contexts fix $\chi^+$ to color $0$ outside $B\cup N$ so that each context has one code.
--
--   The state-map axioms and structural collections use `BoundaryWF`, so their meaning is independent of output labels before allocation. `StoresTables` requires a solution of (3)–(8) to occupy distinct written cells for every existing entry of size at most the input size.
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), §4, pp. 7–11 (PDF 8–12), Definition 4.1 and eqs. (3)–(8); Appendix B.2–B.4, pp. 19–21 (PDF 20–22), Definitions B.3–B.4; Algorithm 2, p. 34 (PDF 35)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator

namespace TwMSOCount.Main

open Classical

variable {r k : ℕ}

/-! ### The tests of Section 4.1 -/

/-- `NoEdge_Q`: `ι(Q)` spans no edge. -/
def NoEdgeT (H : BGraph r k) (Q : Finset (Lab k)) : Prop :=
  ∀ u ∈ H.img Q, ∀ v ∈ H.img Q, ¬ H.G.Adj u v

/-- `Piece_Q`: `NoEdge_Q`, and `H − ι(Q)` is nonempty and connected. -/
def PieceT (H : BGraph r k) (Q : Finset (Lab k)) : Prop :=
  NoEdgeT H Q ∧ (Finset.univ \ H.img Q).Nonempty ∧
    ∀ u ∉ H.img Q, ∀ v ∉ H.img Q, (BGraph.delV H.G ↑(H.img Q)).Reachable u v

/-- The meaning of the recognizing sentence `Φ_{B,B_S,N}` on a graph with boundary names `B ∪ N`
(Appendix C.2: `⋁_P (First_{B,P} ∧ Sel_{B,P,N})` over eligible `P` with first part `B_S`): the
first feasible eligible partition of the old boundary `B` has first part `B_S`, and its farthest
minimum internal separator `Y_P`, of size at most `(k + 1) − |B_S|`, is `ι(N)` or `ι(N \ {s₁})`. -/
def PhiT (B BS N : Finset (Lab k)) (H : BGraph r k) : Prop :=
  ∃ P : BPart k, P.1 = BS ∧ IsFirstFeasible H B P ∧
    ∃ Y, IsYP H B P Y ∧ Y.card + BS.card ≤ k + 1 ∧
      (Y = H.img N ∨ Y = H.img (N.filter (fun s => ∃ t ∈ N, t < s)))

/-! ### State maps (Definition 4.1) -/

/-- A state map: a state code `st H` for every colored boundaried graph, and for each label set
`B` a finite set `states B` of codes (the set `T_B`). -/
structure StateMap (r k : ℕ) where
  st : BGraph r k → ℕ
  states : Finset (Lab k) → Finset ℕ

/-- Definition 4.1 for the sentence `ψ`, quantified over boundaried graphs with injective boundary maps, independently of output labels: states
lie in the finite set `T_B`; (i) invariance under color- and boundary-label-preserving
isomorphism; (ii) the input states of a defined gluing, edge insertion or forgetting determine the
result state; (iii) equal states in `T_B` give equal boundary colors and adjacency and the same
truth of `Width_k`, `NoEdge_Q`, `Piece_Q` (`Q ⊆ B`), of `Φ_{B',B_S,N}` (for `B = B' ∪ N`), and, for
`B = ∅`, of `ψ`. -/
def StateMap.IsStateMap (SM : StateMap r k) (ψ : Formula r Empty) : Prop :=
  (∀ H : BGraph r k, H.BoundaryWF → SM.st H ∈ SM.states H.B) ∧
  (∀ H H' : BGraph r k, H.BoundaryWF → H'.BoundaryWF → BGraph.IsoBL H H' → SM.st H = SM.st H') ∧
  (∀ H₁ H₂ H₁' H₂' : BGraph r k, H₁.BoundaryWF → H₂.BoundaryWF → H₁'.BoundaryWF → H₂'.BoundaryWF →
    H₁.B = H₁'.B → H₂.B = H₂'.B → SM.st H₁ = SM.st H₁' → SM.st H₂ = SM.st H₂' →
    BGraph.GlueOK H₁ H₂ → BGraph.GlueOK H₁' H₂' →
    SM.st (BGraph.glue H₁ H₂) = SM.st (BGraph.glue H₁' H₂')) ∧
  (∀ (H H' : BGraph r k) (a b : Lab k), H.BoundaryWF → H'.BoundaryWF → H.B = H'.B → SM.st H = SM.st H' →
    H.AddEdgeOK a b → H'.AddEdgeOK a b →
    SM.st (H.addEdges {s(a, b)}) = SM.st (H'.addEdges {s(a, b)})) ∧
  (∀ (H H' : BGraph r k) (b : Lab k), H.BoundaryWF → H'.BoundaryWF → H.B = H'.B → SM.st H = SM.st H' →
    b ∈ H.B → SM.st (H.forget b) = SM.st (H'.forget b)) ∧
  (∀ H H' : BGraph r k, H.BoundaryWF → H'.BoundaryWF → H.B = H'.B → SM.st H = SM.st H' →
    (∀ (b : Lab k) (h : b ∈ H.B) (h' : b ∈ H'.B), H.col (H.ι ⟨b, h⟩) = H'.col (H'.ι ⟨b, h'⟩)) ∧
    (∀ (a b : Lab k) (ha : a ∈ H.B) (hb : b ∈ H.B) (ha' : a ∈ H'.B) (hb' : b ∈ H'.B),
      H.G.Adj (H.ι ⟨a, ha⟩) (H.ι ⟨b, hb⟩) ↔ H'.G.Adj (H'.ι ⟨a, ha'⟩) (H'.ι ⟨b, hb'⟩)) ∧
    (H.tw ≤ k ↔ H'.tw ≤ k) ∧
    (∀ Q ⊆ H.B, NoEdgeT H Q ↔ NoEdgeT H' Q) ∧
    (∀ Q ⊆ H.B, PieceT H Q ↔ PieceT H' Q) ∧
    (∀ B BS N : Finset (Lab k), H.B = B ∪ N → BS ⊆ B → N.Nonempty → Disjoint N B →
      (PhiT B BS N H ↔ PhiT B BS N H')) ∧
    (H.B = ∅ → (ModelsPsi H.G H.col ψ ↔ ModelsPsi H'.G H'.col ψ)))

/-- `H` has an injective boundary map, label set `B` and state `τ`. -/
def StateMap.HasSt (SM : StateMap r k) (H : BGraph r k) (B : Finset (Lab k)) (τ : ℕ) : Prop :=
  H.BoundaryWF ∧ H.B = B ∧ SM.st H = τ

/-- `τ ⊨ p`: the graphs of state `τ ∈ T_B` satisfy `p` (witnessed by one graph; by
Definition 4.1(iii) all graphs of the state then agree on each listed test). -/
def StateMap.SatT (SM : StateMap r k) (B : Finset (Lab k)) (τ : ℕ) (p : BGraph r k → Prop) :
    Prop :=
  ∃ H, SM.HasSt H B τ ∧ p H

/-- `glue(τ₁, τ₂) = τ` (defined only when the gluing of graphs of these states is defined). -/
def StateMap.GlueRel (SM : StateMap r k) (B₁ B₂ : Finset (Lab k)) (τ₁ τ₂ τ : ℕ) : Prop :=
  ∃ H₁ H₂, SM.HasSt H₁ B₁ τ₁ ∧ SM.HasSt H₂ B₂ τ₂ ∧ BGraph.GlueOK H₁ H₂ ∧
    SM.st (BGraph.glue H₁ H₂) = τ

/-- `add_F(τ) = τ'`. -/
def StateMap.AddRel (SM : StateMap r k) (B : Finset (Lab k)) (F : Finset (Sym2 (Lab k)))
    (τ τ' : ℕ) : Prop :=
  ∃ H, SM.HasSt H B τ ∧ H.AddEdgesOK F ∧ SM.st (H.addEdges F) = τ'

/-- `forget_N(τ) = τ'`. -/
def StateMap.ForgetRel (SM : StateMap r k) (B N : Finset (Lab k)) (τ τ' : ℕ) : Prop :=
  ∃ H, SM.HasSt H B τ ∧ N ⊆ B ∧ SM.st (H.forgetSet N) = τ'

/-- The boundary colors of `τ` are given by `χ`. -/
def StateMap.HasColors (SM : StateMap r k) (B : Finset (Lab k)) (τ : ℕ) (χ : Lab k → Fin r) :
    Prop :=
  SM.SatT B τ (fun H => ∀ (b : Lab k) (h : b ∈ H.B), H.col (H.ι ⟨b, h⟩) = χ b)

/-- `acc(τ)`: the graphs of state `τ ∈ T_∅` satisfy `ψ`. -/
def StateMap.Acc (SM : StateMap r k) (ψ : Formula r Empty) (τ : ℕ) : Prop :=
  SM.SatT ∅ τ (fun H => ModelsPsi H.G H.col ψ)

/-! ### Separator contexts and the two tables (Section 4.2) -/

/-- A separator context `γ = (B, B_S, j, χ⁺)`: parent labels `B`, old separator labels `B_S`, the
number `j` of new labels `N = {s₁ < ⋯ < s_j}` (the first `j` labels of `Λ_k \ B`), and the label
coloring `χ⁺` on `B ∪ N` (fixed to `0` elsewhere so that each context has one code). -/
abbrev Ctx (r k : ℕ) := Finset (Lab k) × Finset (Lab k) × ℕ × (Lab k → Fin r)

namespace Ctx

/-- The parent's labels `B`. -/
def B (γ : Ctx r k) : Finset (Lab k) := γ.1
/-- The old separator labels `B_S`. -/
def BS (γ : Ctx r k) : Finset (Lab k) := γ.2.1
/-- The new labels `N`. -/
noncomputable def N (γ : Ctx r k) : Finset (Lab k) := newLabels γ.1 γ.2.2.1
/-- The separator labels `J = B_S ⊔ N`. -/
noncomputable def J (γ : Ctx r k) : Finset (Lab k) := γ.BS ∪ γ.N
/-- The label coloring `χ⁺`. -/
def χ (γ : Ctx r k) : Lab k → Fin r := γ.2.2.2

/-- A valid context: `|B| ≤ 6(k+1)`, `B_S ⊆ B`, `1 ≤ j ≤ |Λ_k \ B|`, `|J| ≤ k + 2`, and `χ⁺` is
`0` outside `B ∪ N`. -/
def Valid [NeZero r] (γ : Ctx r k) : Prop :=
  γ.B.card ≤ 6 * (k + 1) ∧ γ.BS ⊆ γ.B ∧ 1 ≤ γ.2.2.1 ∧ γ.2.2.1 ≤ (Finset.univ \ γ.B).card ∧
    γ.J.card ≤ k + 2 ∧ ∀ b, b ∉ γ.B ∪ γ.N → γ.χ b = 0

end Ctx

/-- The valid contexts with parent labels `B`. -/
noncomputable def ctxFinset [NeZero r] (B : Finset (Lab k)) : Finset (Ctx r k) :=
  ((B.powerset ×ˢ Finset.range (k + 3) ×ˢ (Finset.univ : Finset (Lab k → Fin r))).image
    (fun x => (B, x.1, x.2.1, x.2.2))).filter Ctx.Valid

/-- The label pairs `(B choose 2)`. -/
noncomputable def pairs (B : Finset (Lab k)) : Finset (Sym2 (Lab k)) :=
  ((B ×ˢ B).filter (fun p => p.1 < p.2)).image (fun p => s(p.1, p.2))

/-- The empty collection `K⁰_J`: the edgeless graph on `V_J` colored by `χ⁺`. -/
noncomputable def emptyColl (γ : Ctx r k) : BGraph r k := BGraph.boundaryOnly γ.J (fun s => γ.χ s.1) ∅

/-- A collection with inherited labels `I` in context `γ` (Section 4.2): a well-formed
`(J ∪ I)`-boundaried graph with boundary colors `χ⁺`, no edge inside `S = ι(J)`, and every
component `D` of `K − S` with `|D ∩ ι(I)| ≤ ⌊2|B|/3⌋` and `tw(K[D ∪ S]) ≤ k`. -/
def IsCollection (γ : Ctx r k) (I : Finset (Lab k)) (K : BGraph r k) : Prop :=
  K.BoundaryWF ∧ K.B = γ.J ∪ I ∧
    (∀ (b : Lab k) (h : b ∈ K.B), K.col (K.ι ⟨b, h⟩) = γ.χ b) ∧ NoEdgeT K γ.J ∧
    ∀ D ∈ BGraph.comps K.G (K.img γ.J),
      (D ∩ K.img I).card ≤ 2 * γ.B.card / 3 ∧
      PlantedSubgraphLD.tw (K.G.induce (↑(D ∪ K.img γ.J) : Set K.V)) ≤ k

/-- Table entries: graph entries `G_B(m, τ)` and collection entries `U_γ(I, m, τ)`. -/
inductive Entry (r k : ℕ) where
  | g (B : Finset (Lab k)) (m : ℕ) (τ : ℕ)
  | u (γ : Ctx r k) (I : Finset (Lab k)) (m : ℕ) (τ : ℕ)

/-- The internal size index of an entry. -/
def Entry.size : Entry r k → ℕ
  | .g _ m _ => m
  | .u _ _ m _ => m

/-- The entries that exist: `|B| ≤ 6(k+1)` and `τ ∈ T_B`; or `γ` valid, `I ⊆ B \ B_S` and
`τ ∈ T_{J ∪ I}`. -/
def Entry.Valid [NeZero r] (SM : StateMap r k) : Entry r k → Prop
  | .g B _ τ => B.card ≤ 6 * (k + 1) ∧ τ ∈ SM.states B
  | .u γ I _ τ => γ.Valid ∧ I ⊆ γ.B \ γ.BS ∧ τ ∈ SM.states (γ.J ∪ I)

/-- The rank (12) used by Proposition 4.2: `(m, 0, 0)` for graph entries, `(m, 1, |I|)` for
collection entries, compared lexicographically. -/
def Entry.rank : Entry r k → ℕ × ℕ × ℕ
  | .g _ m _ => (m, 0, 0)
  | .u _ I m _ => (m, 1, I.card)

/-- Strict lexicographic order on ranks. -/
def RankLt (a b : ℕ × ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

/-- The split set `A(I, m)` of the collection recurrence. -/
noncomputable def splitSet (I : Finset (Lab k)) (m : ℕ) : Finset (Finset (Lab k) × ℕ) :=
  if h : I.Nonempty then (I.powerset.filter (fun I₁ => I.min' h ∈ I₁)) ×ˢ Finset.range (m + 1)
  else {∅} ×ˢ Finset.Icc 1 m

/-- `alloc_I(m, m₁)`: `C(m, m₁)` if `I ≠ ∅`, else `C(m-1, m₁-1)`. -/
def alloc (I : Finset (Lab k)) (m m₁ : ℕ) : ℕ :=
  if I.Nonempty then Nat.choose m m₁ else Nat.choose (m - 1) (m₁ - 1)

/-- A parent transition `(γ, F, τ_col)` of `R_B(τ)`: `τ_col ∈ T_{B∪N}` has colors `χ⁺` and
satisfies `NoEdge_J`, and `τ_add = add_F(τ_col)` passes (7), `τ_add ⊨ Width_k ∧ Φ_{B,B_S,N}`, with
`forget_N(τ_add) = τ`. -/
def ParentTrans (SM : StateMap r k) (B : Finset (Lab k)) (τ : ℕ) (γ : Ctx r k)
    (F : Finset (Sym2 (Lab k))) (τcol : ℕ) : Prop :=
  SM.HasColors (B ∪ γ.N) τcol γ.χ ∧ SM.SatT (B ∪ γ.N) τcol (fun H => NoEdgeT H γ.J) ∧
    ∃ τadd, SM.AddRel (B ∪ γ.N) F τcol τadd ∧
      SM.SatT (B ∪ γ.N) τadd (fun H => H.tw ≤ k ∧ PhiT B γ.BS γ.N H) ∧
      SM.ForgetRel (B ∪ γ.N) γ.N τadd τ

/-- `w_γ(F) = ω_{χ⁺}(F) ∏_{s ∈ N} λ_{χ⁺(s)}`. -/
noncomputable def wCtx (w : Weights r) (γ : Ctx r k) (F : Finset (Sym2 (Lab k))) : ℚ≥0 :=
  w.omega γ.χ F * ∏ s ∈ γ.N, w.vtx (γ.χ s)

/-- The piece filter of (4) (without the table value): `|I| ≤ ⌊2|B|/3⌋`, `τ ⊨ Piece_J` and `τ`
has boundary colors `χ⁺` on `J ∪ I`. -/
def PieceOK (SM : StateMap r k) (γ : Ctx r k) (I : Finset (Lab k)) (τ : ℕ) : Prop :=
  I.card ≤ 2 * γ.B.card / 3 ∧ SM.SatT (γ.J ∪ I) τ (fun H => PieceT H γ.J) ∧
    SM.HasColors (γ.J ∪ I) τ γ.χ

/-- The filtered piece query (4) on a table `tab`. -/
noncomputable def Gpiece (SM : StateMap r k) (tab : Entry r k → ℚ≥0) (γ : Ctx r k)
    (I : Finset (Lab k)) (m τ : ℕ) : ℚ≥0 :=
  if PieceOK SM γ I τ then tab (.g (γ.J ∪ I) m τ) else 0

/-- Right-hand side of base (3): `Σ_F [tw(H_{B,F}) ≤ k ∧ st(H_{B,F}) = τ] ω_{χ_B}(F)`, summed also
over the boundary colorings `χ_B` (only the one recorded by `τ` contributes). -/
noncomputable def rhsG0 [NeZero r] (SM : StateMap r k) (w : Weights r) (B : Finset (Lab k))
    (τ : ℕ) : ℚ≥0 :=
  ∑ χB : B → Fin r, ∑ F ∈ (pairs B).powerset,
    if (BGraph.boundaryOnly B χB F).tw ≤ k ∧ SM.st (BGraph.boundaryOnly B χB F) = τ then
      w.omega (BGraph.boundaryOnly B χB F).col (BGraph.boundaryOnly B χB F).G.edgeFinset
    else 0

/-- Right-hand side of the parent recurrence (8), for `m > 0`. -/
noncomputable def rhsG [NeZero r] (SM : StateMap r k) (w : Weights r) (tab : Entry r k → ℚ≥0)
    (B : Finset (Lab k)) (m τ : ℕ) : ℚ≥0 :=
  ∑ γ ∈ ctxFinset B, ∑ F ∈ (pairs γ.J).powerset, ∑ τcol ∈ SM.states (B ∪ γ.N),
    if ParentTrans SM B τ γ F τcol ∧ γ.N.card ≤ m then
      (Nat.choose (m - 1) (γ.N.card - 1) : ℚ≥0) * wCtx w γ F *
        tab (.u γ (B \ γ.BS) (m - γ.N.card) τcol)
    else 0

/-- Right-hand side of the collection recurrence (6), for `|I| + m > 0`. -/
noncomputable def rhsU (SM : StateMap r k) (tab : Entry r k → ℚ≥0) (γ : Ctx r k)
    (I : Finset (Lab k)) (m τ : ℕ) : ℚ≥0 :=
  ∑ p ∈ splitSet I m, (alloc I m p.2 : ℚ≥0) *
    ∑ τ₁ ∈ SM.states (γ.J ∪ p.1), ∑ τ₂ ∈ SM.states (γ.J ∪ (I \ p.1)),
      if SM.GlueRel (γ.J ∪ p.1) (γ.J ∪ (I \ p.1)) τ₁ τ₂ τ then
        Gpiece SM tab γ p.1 p.2 τ₁ * tab (.u γ (I \ p.1) (m - p.2) τ₂)
      else 0

/-- The right-hand side of the recurrence defining each entry: (3), (8), (5) or (6). -/
noncomputable def rhs [NeZero r] (SM : StateMap r k) (w : Weights r) (tab : Entry r k → ℚ≥0) :
    Entry r k → ℚ≥0
  | .g B 0 τ => rhsG0 SM w B τ
  | .g B (m + 1) τ => rhsG SM w tab B (m + 1) τ
  | .u γ I m τ =>
      if I = ∅ ∧ m = 0 then (if τ = SM.st (emptyColl γ) then 1 else 0) else rhsU SM tab γ I m τ

/-- `tab` satisfies the recurrences (3)–(8) at every existing entry (the tables computed by
Algorithm 1 are the solution; Proposition 4.2 makes it unique). -/
def SolvesRecurrences [NeZero r] (SM : StateMap r k) (w : Weights r) (tab : Entry r k → ℚ≥0) :
    Prop :=
  ∀ e : Entry r k, e.Valid SM → tab e = rhs SM w tab e

/-- Completed numerical tables stored in the final memory of the counting program. Every
existing entry of size at most `n` occupies its own written rational cell and holds the value
specified by (3)–(8). The address assignment is an encoding of the finite table indices. -/
def StoresTables [NeZero r] (SM : StateMap r k) (w : Weights r) (n : ℕ) (c : Config) : Prop :=
  ∃ (tab : Entry r k → ℚ≥0) (addr : Entry r k → ℕ),
    SolvesRecurrences SM w tab ∧
    Set.InjOn addr {e | e.Valid SM ∧ e.size ≤ n} ∧
    ∀ e : Entry r k, e.Valid SM → e.size ≤ n →
      addr e ∈ c.used ∧ c.reg (addr e) = ((tab e : ℚ≥0) : ℚ)

/-- The entries read on the right-hand side of the recurrence of `e` (Proposition 4.2); a graph
entry is read by the piece query (4) only when the filter passes. -/
def Uses [NeZero r] (SM : StateMap r k) : Entry r k → Entry r k → Prop
  | .g B m τ, e' => 0 < m ∧ ∃ γ ∈ ctxFinset B, ∃ F ∈ (pairs γ.J).powerset,
      ∃ τcol ∈ SM.states (B ∪ γ.N), ParentTrans SM B τ γ F τcol ∧ γ.N.card ≤ m ∧
        e' = .u γ (B \ γ.BS) (m - γ.N.card) τcol
  | .u γ I m τ, e' => ¬ (I = ∅ ∧ m = 0) ∧ ∃ p ∈ splitSet I m,
      ∃ τ₁ ∈ SM.states (γ.J ∪ p.1), ∃ τ₂ ∈ SM.states (γ.J ∪ (I \ p.1)),
        SM.GlueRel (γ.J ∪ p.1) (γ.J ∪ (I \ p.1)) τ₁ τ₂ τ ∧
        ((PieceOK SM γ p.1 τ₁ ∧ e' = .g (γ.J ∪ p.1) p.2 τ₁) ∨ e' = .u γ (I \ p.1) (m - p.2) τ₂)

/-! ### Defining classes (Definition B.3) -/

/-- The sum of partial weights over the defining class of `G_B(m, τ)`: graphs on `V_B ⊔ [m]` with
boundary map `b ↦ v_b`, `tw ≤ k` and state `τ`. -/
noncomputable def gClassSum (SM : StateMap r k) (w : Weights r) (B : Finset (Lab k)) (m τ : ℕ) :
    ℚ≥0 :=
  ∑ G : SimpleGraph (B ⊕ Fin m), ∑ χ : B ⊕ Fin m → Fin r,
    if (BGraph.stored B m G χ).tw ≤ k ∧ SM.st (BGraph.stored B m G χ) = τ then
      BGraph.pw w (BGraph.stored B m G χ) else 0

/-- The sum of partial weights over the defining class of `U_γ(I, m, τ)`: collections on
`V_{J∪I} ⊔ [m]` with boundary map `b ↦ v_b` and state `τ`. -/
noncomputable def uClassSum (SM : StateMap r k) (w : Weights r) (γ : Ctx r k) (I : Finset (Lab k))
    (m τ : ℕ) : ℚ≥0 :=
  ∑ G : SimpleGraph ((γ.J ∪ I : Finset (Lab k)) ⊕ Fin m),
    ∑ χ : (γ.J ∪ I : Finset (Lab k)) ⊕ Fin m → Fin r,
    if IsCollection γ I (BGraph.stored (γ.J ∪ I) m G χ) ∧
        SM.st (BGraph.stored (γ.J ∪ I) m G χ) = τ then
      BGraph.pw w (BGraph.stored (γ.J ∪ I) m G χ) else 0

/-- The class sum of an entry. -/
noncomputable def classSum (SM : StateMap r k) (w : Weights r) : Entry r k → ℚ≥0
  | .g B m τ => gClassSum SM w B m τ
  | .u γ I m τ => uClassSum SM w γ I m τ

/-! ### Expanded descriptions (Definition B.4) -/

/-- An increasing renaming of the vertices named by `N` to the output labels `Lnew`: the `i`-th
smallest label of `N` names a vertex that receives the `i`-th smallest element of `Lnew`. -/
noncomputable def renameNew (H : BGraph r k) (N : Finset (Lab k)) (Lnew : Finset ℕ) :
    BGraph r k :=
  { H with
    out := fun v =>
      if h : ∃ s : H.B, s.1 ∈ N ∧ H.ι s = v then
        (Lnew.sort (· ≤ ·)).getD ((N.sort (· ≤ ·)).idxOf h.choose.1) 0
      else H.out v }

/-- An expanded description of an entry on an actual internal label set `L` (Definition B.4): a
graph-base leaf, an empty-collection leaf, a parent node (a retained transition and a set
`L_new ⊆ L` of size `|N|` containing `min L`, with one collection child on `L \ L_new`), or a
collection node (a split `(I₁, m₁) ∈ A(I, m)` and states with `glue_J(τ₁, τ₂) = τ`, an admissible
first piece, and an `m₁`-subset `L₁ ⊆ L` containing `min L` when `I = ∅`, with a graph child on
`L₁` and a collection child on `L \ L₁`). -/
inductive ExpDesc [NeZero r] (SM : StateMap r k) : Entry r k → Finset ℕ → Type where
  | gbase (B : Finset (Lab k)) (τ : ℕ) (χB : B → Fin r) (F : Finset (Sym2 (Lab k)))
      (hF : F ∈ (pairs B).powerset) (htw : (BGraph.boundaryOnly B χB F).tw ≤ k)
      (hst : SM.st (BGraph.boundaryOnly B χB F) = τ) : ExpDesc SM (.g B 0 τ) ∅
  | ubase (γ : Ctx r k) (τ : ℕ) (hτ : τ = SM.st (emptyColl γ)) : ExpDesc SM (.u γ ∅ 0 τ) ∅
  | parent (B : Finset (Lab k)) (m τ : ℕ) (L : Finset ℕ) (hm : 0 < m) (hL : L.card = m)
      (γ : Ctx r k) (hγ : γ ∈ ctxFinset B) (F : Finset (Sym2 (Lab k)))
      (hF : F ∈ (pairs γ.J).powerset) (τcol : ℕ) (hcol : τcol ∈ SM.states (B ∪ γ.N))
      (htr : ParentTrans SM B τ γ F τcol) (hN : γ.N.card ≤ m) (Lnew : Finset ℕ)
      (hLnew : Lnew ⊆ L ∧ Lnew.card = γ.N.card ∧ ∃ x ∈ Lnew, ∀ y ∈ L, x ≤ y)
      (child : ExpDesc SM (.u γ (B \ γ.BS) (m - γ.N.card) τcol) (L \ Lnew)) :
      ExpDesc SM (.g B m τ) L
  | coll (γ : Ctx r k) (I : Finset (Lab k)) (m τ : ℕ) (L : Finset ℕ) (hL : L.card = m)
      (hne : ¬ (I = ∅ ∧ m = 0)) (p : Finset (Lab k) × ℕ) (hp : p ∈ splitSet I m)
      (τ₁ τ₂ : ℕ) (h₁ : τ₁ ∈ SM.states (γ.J ∪ p.1)) (h₂ : τ₂ ∈ SM.states (γ.J ∪ (I \ p.1)))
      (hglue : SM.GlueRel (γ.J ∪ p.1) (γ.J ∪ (I \ p.1)) τ₁ τ₂ τ)
      (hpiece : PieceOK SM γ p.1 τ₁) (L₁ : Finset ℕ)
      (hL₁ : L₁ ⊆ L ∧ L₁.card = p.2 ∧ (I = ∅ → ∃ x ∈ L₁, ∀ y ∈ L, x ≤ y))
      (c₁ : ExpDesc SM (.g (γ.J ∪ p.1) p.2 τ₁) L₁)
      (c₂ : ExpDesc SM (.u γ (I \ p.1) (m - p.2) τ₂) (L \ L₁)) :
      ExpDesc SM (.u γ I m τ) L

namespace ExpDesc

variable [NeZero r] {SM : StateMap r k}

/-- The output graph of a description: `H_{B,F}`; `K⁰_J`; the child's output with `F` added, the
vertices `v_s` (`s ∈ N`) renamed increasingly to `L_new` and `N` forgotten; or the gluing of the
two children's outputs along `J`. -/
noncomputable def output : {e : Entry r k} → {L : Finset ℕ} → ExpDesc SM e L → BGraph r k
  | _, _, .gbase B _ χB F _ _ _ => BGraph.boundaryOnly B χB F
  | _, _, .ubase γ _ _ => emptyColl γ
  | _, _, .parent _ _ _ _ _ _ γ _ F _ _ _ _ _ Lnew _ child =>
      BGraph.forgetSet (renameNew (BGraph.addEdges child.output F) γ.N Lnew) γ.N
  | _, _, .coll _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ => BGraph.glue c₁.output c₂.output

/-- The weight of a description: the product of its local factors `ω_{χ_B}(F)`, `1`, `w_γ(F)`
and `1`. -/
noncomputable def weight (w : Weights r) : {e : Entry r k} → {L : Finset ℕ} → ExpDesc SM e L → ℚ≥0
  | _, _, .gbase B _ χB F _ _ _ =>
      w.omega (BGraph.boundaryOnly B χB F).col (BGraph.boundaryOnly B χB F).G.edgeFinset
  | _, _, .ubase _ _ _ => 1
  | _, _, .parent _ _ _ _ _ _ γ _ F _ _ _ _ _ _ _ child => wCtx w γ F * weight w child
  | _, _, .coll _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ => weight w c₁ * weight w c₂

/-- The numbers of graph calls and collection calls of a sample following the description (one
per node). -/
noncomputable def calls : {e : Entry r k} → {L : Finset ℕ} → ExpDesc SM e L → ℕ
  | _, _, .gbase _ _ _ _ _ _ _ => 1
  | _, _, .ubase _ _ _ => 1
  | _, _, .parent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ child => 1 + calls child
  | _, _, .coll _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ => 1 + calls c₁ + calls c₂

/-- The probability that the recursive sampler (Algorithm 2) run on the tables `tab` makes the
choices recorded by the description, started at its entry: at each node the summand is chosen with
probability (its mass) / (the entry's value), and the output-label allocation is uniform among the
allocations counted by its binomial coefficient; children are sampled independently. -/
noncomputable def pathProb (w : Weights r) (tab : Entry r k → ℚ≥0) :
    {e : Entry r k} → {L : Finset ℕ} → ExpDesc SM e L → ℚ≥0
  | _, _, .gbase B τ χB F _ _ _ =>
      w.omega (BGraph.boundaryOnly B χB F).col (BGraph.boundaryOnly B χB F).G.edgeFinset /
        tab (.g B 0 τ)
  | _, _, .ubase _ _ _ => 1
  | _, _, .parent B m τ _ _ _ γ _ F _ τcol _ _ _ _ _ child =>
      ((Nat.choose (m - 1) (γ.N.card - 1) : ℚ≥0) * wCtx w γ F *
          tab (.u γ (B \ γ.BS) (m - γ.N.card) τcol)) / tab (.g B m τ) /
        (Nat.choose (m - 1) (γ.N.card - 1) : ℚ≥0) * pathProb w tab child
  | _, _, .coll γ I m τ _ _ _ p _ τ₁ τ₂ _ _ _ _ _ _ c₁ c₂ =>
      ((alloc I m p.2 : ℚ≥0) * Gpiece SM tab γ p.1 p.2 τ₁ * tab (.u γ (I \ p.1) (m - p.2) τ₂)) /
          tab (.u γ I m τ) / (alloc I m p.2 : ℚ≥0) *
        (pathProb w tab c₁ * pathProb w tab c₂)

end ExpDesc

/-- The root graph `(G, χ)` on `[n]` (here `Fin n`) as an `∅`-boundaried graph whose vertices are
their own output labels. -/
def rootGraph {n : ℕ} (G : SimpleGraph (Fin n)) (χ : Fin n → Fin r) : BGraph r k where
  V := Fin n
  G := G
  col := χ
  B := ∅
  ι := fun x => absurd x.2 (Finset.notMem_empty x.1)
  out := fun v => v.val

end TwMSOCount.Main


