-- Prove2me | Definitions.Def_TwMSOCount_Main_Separator
-- name    : TwMSOCount_Main_Separator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:44:24.701198+00:00
-- url     : https://prove2.me/theorems/bd5d55c5-503d-418d-a3b6-84f043df13ba
-- title:
--   Farthest minimum separators, eligible and feasible boundary partitions, the canonical separator, one-step descriptions and candidate assemblies
-- statement:
--   **Definition A.3.** Let $T_1, T_2$ be disjoint vertex sets of a finite graph $G$. A terminal-disjoint $T_1$–$T_2$ separator is a set $Y \subseteq V(G)\setminus(T_1\cup T_2)$ meeting every path with one endpoint in each terminal set; its $T_1$-reachable side is $L_Y = \{v \notin Y : \text{a path in } G - Y \text{ joins } T_1 \text{ to } v\}$. A minimum separator has minimum cardinality; a **farthest minimum separator** is a minimum separator $Y$ with $L_Z \subseteq L_Y$ for every minimum separator $Z$.
--
--   **Boundary partitions (§3.3).** For a $B$-boundaried graph $H$, a partition $P = (B_S, B_L, B_R)$ of $B$ (empty parts allowed) is **eligible** if $|B_S| \le k+1$ and $|B_L|, |B_R| \le \lfloor 2|B|/3 \rfloor$, and **feasible** in $H$ if some $Y \subseteq H^\circ$ with $|Y| \le (k+1) - |B_S|$ meets every path from $\iota(B_L)$ to $\iota(B_R)$ in $H - \iota(B_S)$ (an **internal separator**). $Y_P$ is the minimum internal separator farthest from $\iota(B_L)$. Eligible partitions are ordered first by $|B_S|$, then lexicographically by the word of roles of the labels in increasing order, with $L < R < S$; $P_\star = (B_{S,\star}, B_{L,\star}, B_{R,\star})$ is the first feasible one. With $x_\star = \min H^\circ$ and $Y_\star = Y_{P_\star}$, the **canonical separator** is
--   $$S_\star(H,B) = \iota(B_{S,\star}) \cup Y_\star \cup \{x_\star\}.$$
--   All these notions are also used relative to a designated old boundary $B_0 \subseteq B$ (internal = outside $\iota(B_0)$).
--
--   **One-step descriptions (§3.1).** For $S \subseteq V(H)$, let $D_1, D_2, \dots$ be the components of $H - S$, $F_S = E(H[S])$ the **local edges** and $S_{\mathrm{int}} = S\setminus\partial H$. New labels $N \subseteq \Lambda_k\setminus B$ name $S_{\mathrm{int}}$ through a bijection $\eta : N \to S_{\mathrm{int}}$, giving $\iota^+ = \iota\cup\eta$ on $B \cup N$. The **piece** of $D_i$ is $H_i = H[D_i\cup S] - F_S$ with the labels of $\iota^+$ lying in $D_i \cup S$, i.e. $B_i = J \,\dot\cup\, I_i$ with $J = B_S \,\dot\cup\, N$ and $I_i = \iota^{-1}(D_i)$. The label pattern $F \subseteq \binom J2$ records $F_S$. The **naming convention** takes $N$ to be the first $j = |S_{\mathrm{int}}|$ labels of $\Lambda_k\setminus B$ with $\eta$ increasing; the **anchor order** lists first the components containing an old boundary vertex, by least label, then the others by least output label.
--
--   **Candidate assemblies (§3.2).** A record of old labels $B$, $B_S \subseteq B$, new labels $N$, prescribed colors on $J$, the output labels $\eta(s)$ of the vertices named $s \in N$, a pattern $F \subseteq \binom J2$ and an ordered list of pieces, each a well-formed $(J\cup I_i)$-boundaried graph agreeing with the prescribed colors and output labels, without edges inside $\iota(J)$ and with $P - \iota(J)$ nonempty and connected; the $I_i$ partition $B \setminus B_S$, and allocated output labels are disjoint. Gluing the pieces onto the edgeless graph on $J$, adding $F$ (this gives $\iota^+$) and forgetting $N$ gives the **candidate parent**. The assembly **is the canonical description** of its parent when its separator is $S_\star$, its pattern is that of $E(H[S_\star])$, it follows the naming convention, and its pieces are, in anchor order, the pieces of $H$ along $S_\star$ (up to isomorphism preserving colors, boundary labels and output labels).
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), §3.1–3.3, pp. 4–7 (PDF 5–8); Definition A.3, p. 16 (PDF 17)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph

namespace TwMSOCount.Main

open Classical

/-! ### Definition A.3: terminal-disjoint separators in a finite graph -/

/-- `L_Y`: the vertices outside `Y` joined to `T` by a walk in `G − Y` (length zero allowed). -/
def reachSide {V : Type} (G : SimpleGraph V) (T Y : Finset V) : Set V :=
  {v | v ∉ Y ∧ ∃ u ∈ T, ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ Y}

/-- A terminal-disjoint `T₁–T₂` separator: `Y ⊆ V(G) \ (T₁ ∪ T₂)` meeting every walk (equivalently
every path) with one endpoint in each terminal set. -/
def IsTermSep {V : Type} (G : SimpleGraph V) (T₁ T₂ Y : Finset V) : Prop :=
  Disjoint Y (T₁ ∪ T₂) ∧ ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ p : G.Walk u v, ∃ x ∈ p.support, x ∈ Y

/-- A minimum separator: minimum cardinality among terminal-disjoint separators. -/
def IsMinSep {V : Type} (G : SimpleGraph V) (T₁ T₂ Y : Finset V) : Prop :=
  IsTermSep G T₁ T₂ Y ∧ ∀ Z, IsTermSep G T₁ T₂ Z → Y.card ≤ Z.card

/-- A farthest minimum separator from `T₁`: a minimum separator whose `T₁`-reachable side
contains that of every minimum separator. -/
def IsFarthestMinSep {V : Type} (G : SimpleGraph V) (T₁ T₂ Y : Finset V) : Prop :=
  IsMinSep G T₁ T₂ Y ∧ ∀ Z, IsMinSep G T₁ T₂ Z → reachSide G T₁ Z ⊆ reachSide G T₁ Y

variable {r k : ℕ}

/-! ### Boundary partitions (Section 3.3), relative to a designated old boundary `B₀` -/

/-- A partition `P = (B_S, B_L, B_R)` of a label set, empty parts allowed. -/
abbrev BPart (k : ℕ) := Finset (Lab k) × Finset (Lab k) × Finset (Lab k)

/-- `P` is a partition of `B₀`. -/
def IsPartitionOf (B₀ : Finset (Lab k)) (P : BPart k) : Prop :=
  P.1 ∪ P.2.1 ∪ P.2.2 = B₀ ∧ Disjoint P.1 P.2.1 ∧ Disjoint P.1 P.2.2 ∧ Disjoint P.2.1 P.2.2

/-- Eligible: `|B_S| ≤ k + 1` and `|B_L|, |B_R| ≤ ⌊2|B₀|/3⌋`. -/
def Eligible (B₀ : Finset (Lab k)) (P : BPart k) : Prop :=
  IsPartitionOf B₀ P ∧ P.1.card ≤ k + 1 ∧ P.2.1.card ≤ 2 * B₀.card / 3 ∧
    P.2.2.card ≤ 2 * B₀.card / 3

/-- Vertices internal relative to the old boundary `B₀`: `V(H) \ ι(B₀)`. -/
def intRel (H : BGraph r k) (B₀ : Finset (Lab k)) : Finset H.V := Finset.univ \ H.img B₀

/-- An internal separator for `P`: `Y` internal relative to `B₀`, meeting every path from
`ι(B_L)` to `ι(B_R)` in `H − ι(B_S)`. -/
def IsIntSep (H : BGraph r k) (B₀ : Finset (Lab k)) (P : BPart k) (Y : Finset H.V) : Prop :=
  Y ⊆ intRel H B₀ ∧ ∀ u ∈ H.img P.2.1, ∀ v ∈ H.img P.2.2,
    ∀ p : (BGraph.delV H.G ↑(H.img P.1)).Walk u v, ∃ x ∈ p.support, x ∈ Y

/-- Feasible: some internal separator has `|Y| ≤ (k + 1) − |B_S|`. -/
def Feasible (H : BGraph r k) (B₀ : Finset (Lab k)) (P : BPart k) : Prop :=
  ∃ Y, IsIntSep H B₀ P Y ∧ Y.card + P.1.card ≤ k + 1

/-- The reachable side from `ι(B_L)` in `H − (ι(B_S) ∪ Y)`. -/
def reachP (H : BGraph r k) (P : BPart k) (Y : Finset H.V) : Set H.V :=
  reachSide (BGraph.delV H.G ↑(H.img P.1)) (H.img P.2.1) Y

/-- `Y = Y_P`: a minimum internal separator for `P` whose reachable side from `ι(B_L)` contains
that of every minimum internal separator (Definition A.3 applied in `H − ι(B_S)`). -/
def IsYP (H : BGraph r k) (B₀ : Finset (Lab k)) (P : BPart k) (Y : Finset H.V) : Prop :=
  IsIntSep H B₀ P Y ∧ (∀ Z, IsIntSep H B₀ P Z → Y.card ≤ Z.card) ∧
    ∀ Z, IsIntSep H B₀ P Z → Z.card = Y.card → reachP H P Z ⊆ reachP H P Y

/-- The role word of `P`: each label of `B₀` in increasing order, coded `L = 0 < R = 1 < S = 2`. -/
noncomputable def roleWord (B₀ : Finset (Lab k)) (P : BPart k) : List ℕ :=
  (B₀.sort (· ≤ ·)).map (fun b => if b ∈ P.2.1 then 0 else if b ∈ P.2.2 then 1 else 2)

/-- The fixed order of eligible partitions: first by `|B_S|`, then lexicographically by the role
word. `PrecP B₀ P P'` means `P` comes strictly before `P'`. -/
def PrecP (B₀ : Finset (Lab k)) (P P' : BPart k) : Prop :=
  P.1.card < P'.1.card ∨
    (P.1.card = P'.1.card ∧ List.Lex (· < ·) (roleWord B₀ P) (roleWord B₀ P'))

/-- `P` is the first feasible eligible partition of `B₀` in `H` (the partition `P⋆`). -/
def IsFirstFeasible (H : BGraph r k) (B₀ : Finset (Lab k)) (P : BPart k) : Prop :=
  Eligible B₀ P ∧ Feasible H B₀ P ∧
    ∀ P', Eligible B₀ P' → Feasible H B₀ P' → ¬ PrecP B₀ P' P

/-- `x = x⋆ = min H°`: the internal vertex with least output label. -/
def IsXStar (H : BGraph r k) (x : H.V) : Prop := x ∈ H.int ∧ ∀ y ∈ H.int, H.out x ≤ H.out y

/-- `S` is the canonical separator `S⋆(H, B) = ι(B_{S,⋆}) ∪ Y⋆ ∪ {x⋆}`. -/
def IsCanonSep (H : BGraph r k) (S : Finset H.V) : Prop :=
  ∃ P Y x, IsFirstFeasible H H.B P ∧ IsYP H H.B P Y ∧ IsXStar H x ∧ S = H.img P.1 ∪ Y ∪ {x}

/-! ### One-step descriptions (Section 3.1) -/

/-- The first `j` labels of `Λ_k \ B`, the new labels `N = {s₁ < ⋯ < s_j}`. -/
noncomputable def newLabels (B : Finset (Lab k)) (j : ℕ) : Finset (Lab k) :=
  (((Finset.univ \ B).sort (· ≤ ·)).take j).toFinset

/-- The extended boundary map `ι⁺ = ι ∪ η` on `B ∪ N`, for a label assignment `η : N → V`. -/
def extend (H : BGraph r k) (N : Finset (Lab k)) (η : N → H.V) : BGraph r k where
  V := H.V
  G := H.G
  col := H.col
  B := H.B ∪ N
  ι := fun x => if h : x.1 ∈ H.B then H.ι ⟨x.1, h⟩
    else η ⟨x.1, (Finset.mem_union.mp x.2).resolve_left h⟩
  out := H.out

/-- `η` is a label assignment for `S`: a bijection from `N` onto `S_int = S \ ∂H`. -/
def IsLabelAssignment (H : BGraph r k) (S : Finset H.V) (N : Finset (Lab k)) (η : N → H.V) :
    Prop :=
  Disjoint N H.B ∧ Function.Injective η ∧ (∀ s, η s ∈ S \ H.bdry) ∧ ∀ v ∈ S \ H.bdry, ∃ s, η s = v

/-- The naming convention: `N` is the first `j = |S_int|` labels of `Λ_k \ B` and `η` preserves
boundary-label order on `N` and output-label order on `S_int`. -/
def IsConvLabelAssignment (H : BGraph r k) (S : Finset H.V) (N : Finset (Lab k))
    (η : N → H.V) : Prop :=
  IsLabelAssignment H S N η ∧ N = newLabels H.B (S \ H.bdry).card ∧
    ∀ s t : N, s.1 < t.1 → H.out (η s) < H.out (η t)

/-- The labels of `Hx` whose image lies in `U`. -/
def labelsIn (Hx : BGraph r k) (U : Finset Hx.V) : Finset (Lab k) :=
  Hx.B.filter (fun b => ∃ h : b ∈ Hx.B, Hx.ι ⟨b, h⟩ ∈ U)

/-- The piece `H_i = H[D ∪ S] − F_S` of a component vertex set `D` of `H − S`, taken in the
extended graph `Hx` (boundary map `ι⁺`): it keeps as boundary every label whose vertex lies in
`D ∪ S`, i.e. `B_i = J ⊔ I_i`. -/
noncomputable def piece (Hx : BGraph r k) (S D : Finset Hx.V) : BGraph r k where
  V := {v : Hx.V // v ∈ D ∪ S}
  G := SimpleGraph.fromRel (fun u v => Hx.G.Adj u.1 v.1 ∧ ¬ (u.1 ∈ S ∧ v.1 ∈ S))
  col := fun v => Hx.col v.1
  B := labelsIn Hx (D ∪ S)
  ι := fun x => ⟨Hx.ι ⟨x.1, (Finset.mem_filter.mp x.2).2.choose⟩,
    (Finset.mem_filter.mp x.2).2.choose_spec⟩
  out := fun v => Hx.out v.1

/-- The edgeless graph on `S` with the labels of `Hx` that lie on `S`, colored and output-labeled
as in `Hx` (the start of the reconstruction in Lemma 3.1(i)). -/
noncomputable def sepBase (Hx : BGraph r k) (S : Finset Hx.V) : BGraph r k where
  V := {v : Hx.V // v ∈ S}
  G := ⊥
  col := fun v => Hx.col v.1
  B := labelsIn Hx S
  ι := fun x => ⟨Hx.ι ⟨x.1, (Finset.mem_filter.mp x.2).2.choose⟩,
    (Finset.mem_filter.mp x.2).2.choose_spec⟩
  out := fun v => Hx.out v.1

/-- The local edges `F_S = E(H[S])`. -/
noncomputable def localEdges (H : BGraph r k) (S : Finset H.V) : Finset (Sym2 H.V) :=
  H.G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)

/-- The label pattern `F ⊆ (J choose 2)` of the local edges: `{a, b} ∈ F` exactly when
`{ι⁺(a), ι⁺(b)}` is an edge of `H[S]`. -/
noncomputable def labelPattern (Hx : BGraph r k) (J : Finset (Lab k)) : Finset (Sym2 (Lab k)) :=
  ((J ×ˢ J).filter (fun p => ∃ (ha : p.1 ∈ Hx.B) (hb : p.2 ∈ Hx.B),
      Hx.G.Adj (Hx.ι ⟨p.1, ha⟩) (Hx.ι ⟨p.2, hb⟩))).image (fun p => s(p.1, p.2))

/-- Glue a list of boundaried graphs onto a base graph, left to right. -/
noncomputable def glueAll (base : BGraph r k) (Hs : List (BGraph r k)) : BGraph r k :=
  Hs.foldl BGraph.glue base

/-- Anchor key of a component vertex set `D` of `H − S` in `Hx` with old labels `B`: the least
old label whose vertex lies in `D`, if any, and otherwise `|Λ_k|` plus the least output label in
`D` (so that components with an old boundary vertex come first, as in the anchor rule). -/
noncomputable def anchorKey (Hx : BGraph r k) (B : Finset (Lab k)) (D : Finset Hx.V) : ℕ :=
  let L := (B.filter (fun b => ∃ h : b ∈ Hx.B, Hx.ι ⟨b, h⟩ ∈ D)).image (fun b => b.val)
  if h : L.Nonempty then L.min' h
  else 7 * (k + 1) + 1 + (if h' : (D.image Hx.out).Nonempty then (D.image Hx.out).min' h' else 0)

/-- The components of `H − S` in anchor order. -/
noncomputable def anchorOrder (Hx : BGraph r k) (B : Finset (Lab k)) (S : Finset Hx.V) :
    List (Finset Hx.V) :=
  (BGraph.comps Hx.G S).toList.mergeSort (fun D E => decide (anchorKey Hx B D ≤ anchorKey Hx B E))

/-- The pieces of the description of `H` along `S`, in anchor order (`Hx` carries `ι⁺`). -/
noncomputable def descPieces (Hx : BGraph r k) (B : Finset (Lab k)) (S : Finset Hx.V) :
    List (BGraph r k) :=
  (anchorOrder Hx B S).map (piece Hx S)

/-! ### Candidate assemblies (Section 3.2) -/

/-- A candidate assembly for old labels `B`: separator labels `J = B_S ⊔ N` with prescribed
colors, the output labels `η(s)` of the vertices named `s ∈ N`, a label pattern `F ⊆ (J choose 2)`,
and an ordered list of pieces. -/
structure Assembly (r k : ℕ) where
  B : Finset (Lab k)
  BS : Finset (Lab k)
  N : Finset (Lab k)
  colJ : Lab k → Fin r
  η : Lab k → ℕ
  F : Finset (Sym2 (Lab k))
  pieces : List (BGraph r k)

namespace Assembly

/-- Separator labels `J = B_S ⊔ N`. -/
def J (A : Assembly r k) : Finset (Lab k) := A.BS ∪ A.N

/-- The inherited labels `I_i = B_i \ J` of a piece. -/
def inh (A : Assembly r k) (P : BGraph r k) : Finset (Lab k) := P.B \ A.J

/-- The record conditions of Section 3.2: `B_S ⊆ B`, `N ⊆ Λ_k \ B`, `F ⊆ (J choose 2)`; each
piece is a well-formed `(J ⊔ I_i)`-boundaried graph with the prescribed colors on `J`, each
`s ∈ N` on a vertex of output label `η(s)`, no edge inside `ι(J)`, and `P − ι(J)` nonempty and
connected; the `I_i` partition `B \ B_S`; output labels outside the separator are pairwise
disjoint across pieces and disjoint from `η(N)`, and `η` is injective on `N`. -/
def Valid (A : Assembly r k) : Prop :=
  A.BS ⊆ A.B ∧ Disjoint A.N A.B ∧
  (∀ a b, s(a, b) ∈ A.F → a ∈ A.J ∧ b ∈ A.J ∧ a ≠ b) ∧
  Set.InjOn A.η A.N ∧
  (∀ P ∈ A.pieces, P.WF ∧ A.J ⊆ P.B ∧ A.inh P ⊆ A.B \ A.BS ∧
    (∀ (s : Lab k) (h : s ∈ P.B), s ∈ A.J → P.col (P.ι ⟨s, h⟩) = A.colJ s) ∧
    (∀ (s : Lab k) (h : s ∈ P.B), s ∈ A.N → P.out (P.ι ⟨s, h⟩) = A.η s) ∧
    (∀ u ∈ P.img A.J, ∀ v ∈ P.img A.J, ¬ P.G.Adj u v) ∧
    (Finset.univ \ P.img A.J).Nonempty ∧
    (∀ u ∉ P.img A.J, ∀ v ∉ P.img A.J, (BGraph.delV P.G ↑(P.img A.J)).Reachable u v) ∧
    (∀ v ∈ P.int, P.out v ∉ A.η '' ↑A.N)) ∧
  (A.pieces.map A.inh).foldr (· ∪ ·) ∅ = A.B \ A.BS ∧
  (∀ i j (hi : i < A.pieces.length) (hj : j < A.pieces.length), i ≠ j →
    Disjoint (A.inh A.pieces[i]) (A.inh A.pieces[j]) ∧
    Disjoint ((A.pieces[i]).int.image (A.pieces[i]).out)
      ((A.pieces[j]).int.image (A.pieces[j]).out))

/-- The edgeless graph on the separator labels `J`, colored by `colJ`, with `s ∈ N` carrying
output label `η(s)`. -/
def base (A : Assembly r k) : BGraph r k where
  V := A.J
  G := ⊥
  col := fun s => A.colJ s.1
  B := A.J
  ι := id
  out := fun s => A.η s.1

/-- The glued collection with the local edges added: the candidate parent with the extended
boundary map `ι⁺` on `B ∪ N`. -/
noncomputable def parentExt (A : Assembly r k) : BGraph r k :=
  BGraph.addEdges (glueAll A.base A.pieces) A.F

/-- The candidate parent `(H, χ, ι)`: `N` forgotten. -/
noncomputable def parent (A : Assembly r k) : BGraph r k := BGraph.forgetSet A.parentExt A.N

/-- Anchor key of a piece: its least inherited label, or `|Λ_k|` plus its least internal output
label. -/
noncomputable def pieceKey (A : Assembly r k) (P : BGraph r k) : ℕ :=
  if h : (A.inh P).Nonempty then ((A.inh P).image (fun b => b.val)).min' (h.image _)
  else 7 * (k + 1) + 1 +
    (if h' : (P.int.image P.out).Nonempty then (P.int.image P.out).min' h' else 0)

/-- The naming and ordering conventions of Section 3.1: `N` is the first `|N|` labels of
`Λ_k \ B`, `η` is increasing on `N`, and the pieces are listed in anchor order. -/
def FollowsConventions (A : Assembly r k) : Prop :=
  A.N = newLabels A.B A.N.card ∧ (∀ s ∈ A.N, ∀ t ∈ A.N, s < t → A.η s < A.η t) ∧
    (A.pieces.map A.pieceKey).Pairwise (· < ·)

/-- The assembly is the description of its parent along `S`: its separator is `S`, its label
pattern is that of `E(H[S])`, its new labels and their assignment follow the naming convention,
and its pieces are, in order and up to isomorphism preserving colors, boundary labels and output
labels, the pieces of `H` along `S` in anchor order. -/
def IsDescAlong (A : Assembly r k) (S : Finset A.parentExt.V) : Prop :=
  A.parentExt.img A.J = S ∧ A.BS = A.B.filter (fun b => b ∈ A.parentExt.B ∧
      ∃ h : b ∈ A.parentExt.B, A.parentExt.ι ⟨b, h⟩ ∈ S) ∧
    A.F = labelPattern A.parentExt A.J ∧
    A.N = newLabels A.B A.N.card ∧ (∀ s ∈ A.N, ∀ t ∈ A.N, s < t → A.η s < A.η t) ∧
    A.pieces.length = (descPieces A.parentExt A.B S).length ∧
    ∀ (i : ℕ) (h₁ : i < A.pieces.length) (h₂ : i < (descPieces A.parentExt A.B S).length),
      BGraph.IsoOut A.pieces[i] (descPieces A.parentExt A.B S)[i]

/-- The assembly is the canonical description of its parent `H`: its description along the
canonical separator `S⋆(H, B)`. -/
def IsCanonDesc (A : Assembly r k) : Prop :=
  ∃ S : Finset A.parentExt.V, IsCanonSep A.parent S ∧ A.IsDescAlong S

end Assembly

end TwMSOCount.Main


