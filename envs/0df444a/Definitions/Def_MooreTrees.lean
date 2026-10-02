-- Prove2me | Definitions.Def_MooreTrees
-- name    : MooreTrees
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-01T22:51:30.057032+00:00
-- url     : https://prove2.me/theorems/7f2acd04-b5b2-4f58-b5fe-0dfea31307ed
-- title:
--   Moore §2 and §5: finite binary trees, tree diagrams, the action of F and the operation ∂
-- statement:
--   Notions of Moore's §2 (pp. 3–4) and §5 (Definitions 5.1, 5.6, 5.8).
--
--   **Trees.** A finite binary sequence is a `Seq` (a list of bits, `false` for $0$). A finite set $T$ of sequences is a **tree** (`IsTree T`; the collection $\mathscr T$ is `Tree`) when every infinite binary sequence has exactly one element of $T$ as an initial part: $T$ records the addresses of the leaves. `trivialTree` is $\{\langle\rangle\}$. $T/u = \{s : u^\frown s \in T\}$ (`quot T u`); $U$ is **dominated by** $V$ (`Dominated U V`) when every element of $U$ has an extension in $V$; `LexLt` is the lexicographic order and `sorted T` lists $T$ in that order.
--
--   **Tree diagrams (pp. 3–4).** A **tree diagram** (`IsTreeDiagram L R`) is a pair of trees with $|L| = |R|$. It defines the map $s_i^\frown x \mapsto t_i^\frown x$, where $s_i$ and $t_i$ are the $i$th elements of $L$ and $R$: on finite sequences (`diagramAct`, undefined on a sequence extending no element of $L$) and on infinite sequences (`diagramMap`). Two tree diagrams are **equivalent** (`DiagramEquiv`) when they define the same map on infinite sequences, and a tree diagram is **reduced** (`IsReducedDiagram`) when no equivalent tree diagram has fewer leaves. The **product** of tree diagrams (`diagramMul`), Moore's $f \cdot g = g \circ f$, is a chosen reduced tree diagram whose map on infinite sequences is the map of the first followed by the map of the second; that one exists for reduced tree diagrams is part of the milestone `bijOn_Lf_Rf_and_diagramMul`.
--
--   **F.** Moore's $F$ is Thompson's group with the product $f \cdot g = g \circ f$ ("$f$ followed by $g$"): `MooreF` is the opposite group of the published `CannonFloydParry.F` (dyadic piecewise linear homeomorphisms of $[0,1]$), and `toMap` gives the underlying homeomorphism. A tree diagram **describes** a homeomorphism $f$ (`Describes L R f`) when $f$ maps the dyadic interval of $s_i$ affinely onto that of $t_i$, the map $s_i^\frown x \mapsto t_i^\frown x$ on binary expansions. $(L_f, R_f)$ (`Lf`, `Rf`) is a chosen reduced tree diagram describing $f$; that one exists, and that it is unique, follows from the milestone `bijOn_Lf_Rf_and_diagramMul`.
--
--   **The action.** $t \cdot f$ (`seqAct`) is the map of finite sequences defined by $(L_f, R_f)$; $f$ **acts properly** on $t$ (`ActsProperly`) when $t \cdot f$ is defined and ends in the same digit as $t$; for the empty sequence $\langle\rangle$, which Moore does not discuss, this means $\langle\rangle \cdot f = \langle\rangle$. $T \cdot f$ (`treeAct`) is the pointwise image, defined when $f$ is defined on all of $T$; `ActsProperlyOn` means on every element of $T$. The elements $x_0$, $x_1$ (p. 4), $a$, $b$ (p. 14) and $c$, $d$ (p. 16) (`x0`, `x1`, `elemA`–`elemD`) are given by Moore's tree diagrams through `ofDiagram`, a chosen element of $F$ that the diagram describes (for these six diagrams one exists: each is a dyadic piecewise linear map); `gens` is $\Gamma = \{x_0, x_1, x_0^{-1}, x_1^{-1}\}$.
--
--   **The operation ∂ (Definition 5.1).** For trees $T$, $U$, `DeltaConditions T U` says: $U$ has extensions of $01$ and $10$; the interior elements $u <_{lex} v$ of $U$ (all but the least and greatest) satisfy $2|T/u| \le |T/v|$ throughout, or $2|T/v| \le |T/u|$ throughout; and the least interior element ends in $1$ and the greatest in $0$. `delta T` is the maximum, for domination, of the trees dominated by $T$ satisfying these conditions, and the trivial tree when there is no such maximum. Moore takes the trivial tree when no tree satisfies the conditions; the two agree because a maximum exists whenever some tree does (Lemma 5.2, the milestone `exists_max_deltaConditions`).
--
--   **The sets of §5.** `TPlus`: $|T/001| < |T/01| < |T/10|$; `TMinus`: $|T/001| > |T/01| > |T/10|$; `EBad` is $\mathscr E$, the trees satisfying neither (Definition 5.6). `TwoTimes`: $2|T/001| \le |T/01| \le \tfrac12|T/10|$; `HalfTimes`: $\tfrac12|T/001| \ge |T/01| \ge 2|T/10|$; `EStar` is $\mathscr E^*$, the trees satisfying neither (Definition 5.8).
--
--   **Formalization Note.** Moore defines $F$ as the collection of reduced tree diagrams with the product $f \cdot g = g \circ f$. Here $F$ is the published group of piecewise linear homeomorphisms, tied to tree diagrams by `Describes`; Moore's sentence defining $F$ is a milestone (`bijOn_Lf_Rf_and_diagramMul`): $f \mapsto (L_f, R_f)$ is a bijection onto the reduced tree diagrams that turns the product of $F$ into the product of tree diagrams (`diagramMul`). Moore's "unique minimal tree diagram" is read as the one with the fewest leaves. The partial action is defined on all finite sets of sequences; on trees it is Moore's action on $\mathscr T$, and Moore's statement that it preserves trees is a milestone.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), pp. 3–16, §2 and Definitions 5.1, 5.6, 5.8

import Definitions.Def_CannonFloydParry
import Mathlib

/-!
# Moore, *Fast growth in the Følner function for Thompson's group F*, §2 and §5: trees

J. T. Moore, Groups Geom. Dyn. 7 (2013) 633–651, arXiv:0905.1118v7: the finite rooted binary trees
`𝒯` as sets of binary sequences (§2, p. 3), tree diagrams and the partial right action of `F` on
sequences and on `𝒯` (§2, pp. 3–4), the operation `∂` (Definition 5.1) and the sets `E`, `𝒯⁺`,
`𝒯⁻`, `E*` (Definitions 5.6, 5.8). Moore's `F` is the group of reduced tree diagrams with
`f · g = g ∘ f`; here it is `(CannonFloydParry.F)ᵐᵒᵖ`.
-/

namespace MooreFoelner

open Classical CannonFloydParry

/-- A finite binary sequence, a list of digits with `false` for 0 and `true` for 1. -/
abbrev Seq := List Bool

/-- `u` is an initial part of the infinite binary sequence `x`. -/
def IsInitialPart (u : Seq) (x : ℕ → Bool) : Prop :=
  ∀ i (h : i < u.length), u.get ⟨i, h⟩ = x i

/-- p. 3: a **finite rooted binary tree**, as the finite set of the addresses of its leaves: every
infinite binary sequence has a unique element of `T` as an initial part. -/
def IsTree (T : Finset Seq) : Prop :=
  ∀ x : ℕ → Bool, ∃! t, t ∈ T ∧ IsInitialPart t x

/-- `𝒯`, the collection of all finite rooted binary trees (p. 3). -/
def Tree : Type := {T : Finset Seq // IsTree T}

/-- The trivial tree `{⟨⟩}` (p. 3). -/
def trivialTree : Finset Seq := {[]}

/-- `T/u = {s : u⁀s ∈ T}` (p. 3). -/
def quot (T : Finset Seq) (u : Seq) : Finset Seq :=
  (T.filter (u <+: ·)).image (·.drop u.length)

/-- `U` is **dominated by** `V`: every element of `U` has an extension in `V` (p. 3). -/
def Dominated (U V : Finset Seq) : Prop :=
  ∀ u ∈ U, ∃ v ∈ V, u <+: v

/-- The lexicographic order `<_lex` on binary sequences (p. 3), with `0 < 1`. -/
def LexLt (u v : Seq) : Prop := List.Lex (· < ·) u v

/-- The elements of `T` in `<_lex`-order. -/
noncomputable def sorted (T : Finset Seq) : List Seq :=
  (T.toList).mergeSort (fun u v => decide (LexLt u v))

/-- The rational `0.u₀u₁…` of a finite binary sequence: the left end of its dyadic interval. -/
noncomputable def seqVal (u : Seq) : ℝ :=
  ∑ i : Fin u.length, if u.get i then (1 / 2 : ℝ) ^ (i.1 + 1) else 0

/-- p. 3: a **tree diagram** `(L, R)`: two trees with the same number of leaves. -/
def IsTreeDiagram (L R : Finset Seq) : Prop :=
  IsTree L ∧ IsTree R ∧ L.card = R.card

/-- The map of finite sequences described by a tree diagram (p. 3): `sᵢ⁀x ↦ tᵢ⁀x` for the `i`th
elements `sᵢ`, `tᵢ` of `L` and `R`; undefined when `t` extends no element of `L`. -/
noncomputable def diagramAct (L R : Finset Seq) (t : Seq) : Option Seq :=
  let S := sorted L
  let T := sorted R
  match (List.finRange S.length).find? (fun i => decide (S.get i <+: t)) with
  | some i => (T[i.1]?).map (· ++ t.drop (S.get i).length)
  | none => none

/-- The map of infinite sequences described by a tree diagram (p. 3): `sᵢ⁀x ↦ tᵢ⁀x`, where `sᵢ` is
the element of `L` that is an initial part of the sequence. -/
noncomputable def diagramMap (L R : Finset Seq) (x : ℕ → Bool) : ℕ → Bool :=
  let S := sorted L
  let T := sorted R
  match (List.finRange S.length).find? (fun i => decide (IsInitialPart (S.get i) x)) with
  | some i =>
    match T[i.1]? with
    | some t => fun n => if h : n < t.length then t.get ⟨n, h⟩ else x (n - t.length + (S.get i).length)
    | none => x
  | none => x

/-- p. 4: tree diagrams `(L, R)` and `(L', R')` are **equivalent**: they define the same map on
infinite sequences. -/
def DiagramEquiv (L R L' R' : Finset Seq) : Prop :=
  ∀ x : ℕ → Bool, diagramMap L R x = diagramMap L' R' x

/-- p. 4: a tree diagram is **reduced**: no tree diagram in its equivalence class has fewer
leaves. -/
def IsReducedDiagram (L R : Finset Seq) : Prop :=
  IsTreeDiagram L R ∧ ∀ L' R', IsTreeDiagram L' R' → DiagramEquiv L R L' R' → L.card ≤ L'.card

/-- p. 4: the product of tree diagrams in Moore's `F`, `f · g = g ∘ f` ("`f` followed by `g`"): a
reduced tree diagram whose map on infinite sequences is that of `D` followed by that of `D'`. -/
noncomputable def diagramMul (D D' : Finset Seq × Finset Seq) : Finset Seq × Finset Seq :=
  Classical.epsilon (fun E : Finset Seq × Finset Seq => IsReducedDiagram E.1 E.2 ∧
    ∀ x, diagramMap E.1 E.2 x = diagramMap D'.1 D'.2 (diagramMap D.1 D.2 x))

/-- `(L, R)` **describes** the map `f` of `[0,1]`: it is a tree diagram, and for the `i`th elements
`sᵢ`, `tᵢ`, `f` maps the dyadic interval of `sᵢ` affinely onto that of `tᵢ` (the map
`sᵢ⁀x ↦ tᵢ⁀x` on binary expansions). -/
def Describes (L R : Finset Seq) (f : UI ≃o UI) : Prop :=
  IsTreeDiagram L R ∧
    ∀ i (hL : i < (sorted L).length) (hR : i < (sorted R).length) (x : UI),
      seqVal ((sorted L).get ⟨i, hL⟩) ≤ (x : ℝ) →
      (x : ℝ) ≤ seqVal ((sorted L).get ⟨i, hL⟩) + (1 / 2 : ℝ) ^ ((sorted L).get ⟨i, hL⟩).length →
      ((f x : UI) : ℝ) = seqVal ((sorted R).get ⟨i, hR⟩) +
        ((x : ℝ) - seqVal ((sorted L).get ⟨i, hL⟩)) *
          (2 : ℝ) ^ (((sorted L).get ⟨i, hL⟩).length - ((sorted R).get ⟨i, hR⟩).length : ℤ)

/-- `(L_f, R_f)`, the reduced tree diagram of `f` (p. 4): a reduced tree diagram describing `f`. -/
noncomputable def reducedDiagram (f : UI ≃o UI) : Finset Seq × Finset Seq :=
  Classical.epsilon (fun D : Finset Seq × Finset Seq => IsReducedDiagram D.1 D.2 ∧ Describes D.1 D.2 f)

/-- `L_f`. -/
noncomputable def Lf (f : UI ≃o UI) : Finset Seq := (reducedDiagram f).1

/-- `R_f`. -/
noncomputable def Rf (f : UI ≃o UI) : Finset Seq := (reducedDiagram f).2

/-- Moore's `F` (p. 4): Thompson's group with the product `f · g = g ∘ f` ("`f` followed by `g`"),
the opposite of `CannonFloydParry.F`, whose product is composition. -/
abbrev MooreF : Type := (CannonFloydParry.F)ᵐᵒᵖ

/-- The underlying map of an element of Moore's `F`. -/
def toMap (f : MooreF) : UI ≃o UI := (MulOpposite.unop f : F)

/-- `t · f` (p. 3): the map of finite sequences described by `(L_f, R_f)`. -/
noncomputable def seqAct (t : Seq) (f : MooreF) : Option Seq :=
  diagramAct (Lf (toMap f)) (Rf (toMap f)) t

/-- `f` **acts properly** on the finite sequence `t` (p. 3): `t · f` is defined and its final
digit agrees with that of `t`. -/
def ActsProperly (f : MooreF) (t : Seq) : Prop :=
  ∃ t', seqAct t f = some t' ∧ t'.getLast? = t.getLast?

/-- `T · f` (p. 4): the pointwise image of `T` under `f`, defined when `f` is defined on all of
`T`. -/
noncomputable def treeAct (T : Finset Seq) (f : MooreF) : Option (Finset Seq) :=
  if h : ∀ t ∈ T, (seqAct t f).isSome then
    some (T.attach.image fun t => (seqAct t.1 f).get (h t.1 t.2))
  else none

/-- `f` acts properly on `T` (p. 4): on every element of `T`. -/
def ActsProperlyOn (f : MooreF) (T : Finset Seq) : Prop :=
  ∀ t ∈ T, ActsProperly f t

/-- The element of `F` described by a tree diagram, when there is one. -/
noncomputable def ofDiagram (L R : Finset Seq) : MooreF :=
  MulOpposite.op (Classical.epsilon (fun f : F => Describes L R (f : UI ≃o UI)))

/-- Binary sequences written as strings of digits. -/
def bits (w : String) : Seq := w.toList.map (· = '1')

/-- `x₀` (p. 4): `00 ↦ 0`, `01 ↦ 10`, `1 ↦ 11`. -/
noncomputable def x0 : MooreF := ofDiagram {bits "00", bits "01", bits "1"} {bits "0", bits "10", bits "11"}

/-- `x₁` (p. 4): `0 ↦ 0`, `100 ↦ 10`, `101 ↦ 110`, `11 ↦ 111`. -/
noncomputable def x1 : MooreF :=
  ofDiagram {bits "0", bits "100", bits "101", bits "11"} {bits "0", bits "10", bits "110", bits "111"}

/-- The generating set `Γ = {x₀, x₁, x₀⁻¹, x₁⁻¹}` (p. 4). -/
noncomputable def gens : Finset MooreF := {x0, x1, x0⁻¹, x1⁻¹}

/-- `a` (proof of Lemma 5.7, p. 14). -/
noncomputable def elemA : MooreF :=
  ofDiagram {bits "000", bits "0010", bits "0011", bits "01", bits "100", bits "101", bits "11"}
    {bits "000", bits "001", bits "0100", bits "0101", bits "011", bits "10", bits "11"}

/-- `b` (proof of Lemma 5.7, p. 14). -/
noncomputable def elemB : MooreF :=
  ofDiagram {bits "000", bits "0010", bits "0011", bits "01", bits "10", bits "11"}
    {bits "000", bits "001", bits "01", bits "100", bits "101", bits "11"}

/-- `c` (proof of Lemma 5.10, p. 16). -/
noncomputable def elemC : MooreF :=
  ofDiagram {bits "00", bits "01", bits "10", bits "11"} {bits "0", bits "100", bits "101", bits "11"}

/-- `d` (proof of Lemma 5.10, p. 16). -/
noncomputable def elemD : MooreF :=
  ofDiagram {bits "000", bits "001", bits "01", bits "1"} {bits "00", bits "010", bits "011", bits "1"}

/-- The endpoints of `U` are its `<_lex`-least and greatest elements; the others are **interior**
(p. 11). -/
noncomputable def interior (U : Finset Seq) : List Seq := ((sorted U).drop 1).dropLast

/-- The defining conditions of `∂T` for `U` (Definition 5.1). -/
def DeltaConditions (T U : Finset Seq) : Prop :=
  (∃ u ∈ U, bits "01" <+: u) ∧ (∃ u ∈ U, bits "10" <+: u) ∧
  ((∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨i, hi⟩)).card ≤ (quot T ((interior U).get ⟨j, hj⟩)).card) ∨
    (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨j, hj⟩)).card ≤ (quot T ((interior U).get ⟨i, hi⟩)).card)) ∧
  ((interior U).head?.bind List.getLast? = some true) ∧
  ((interior U).getLast?.bind List.getLast? = some false)

/-- Definition 5.1: `∂T` is the maximum `U ∈ 𝒯`, in the order of domination, which is dominated by
`T` and satisfies the defining conditions; if there is none, the trivial tree. -/
noncomputable def delta (T : Finset Seq) : Finset Seq :=
  if h : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U ∧
      ∀ V, IsTree V → Dominated V T → DeltaConditions T V → Dominated V U
  then Classical.choose h else trivialTree

/-- Definition 5.6: `𝒯⁺ = {T : |T/001| < |T/01| < |T/10|}`. -/
def TPlus (T : Finset Seq) : Prop :=
  (quot T (bits "001")).card < (quot T (bits "01")).card ∧ (quot T (bits "01")).card < (quot T (bits "10")).card

/-- Definition 5.6: `𝒯⁻ = {T : |T/001| > |T/01| > |T/10|}`. -/
def TMinus (T : Finset Seq) : Prop :=
  (quot T (bits "001")).card > (quot T (bits "01")).card ∧ (quot T (bits "01")).card > (quot T (bits "10")).card

/-- Definition 5.6: `E`, the trees satisfying neither `(+)` nor `(−)`. -/
def EBad : Set (Finset Seq) := {T | IsTree T ∧ ¬ TPlus T ∧ ¬ TMinus T}

/-- Definition 5.8, `(2×)`: `2|T/001| ≤ |T/01| ≤ ½|T/10|`. -/
def TwoTimes (T : Finset Seq) : Prop :=
  2 * (quot T (bits "001")).card ≤ (quot T (bits "01")).card ∧
    2 * (quot T (bits "01")).card ≤ (quot T (bits "10")).card

/-- Definition 5.8, `(½×)`: `½|T/001| ≥ |T/01| ≥ 2|T/10|`. -/
def HalfTimes (T : Finset Seq) : Prop :=
  (quot T (bits "001")).card ≥ 2 * (quot T (bits "01")).card ∧
    (quot T (bits "01")).card ≥ 2 * (quot T (bits "10")).card

/-- Definition 5.8: `E*`, the trees satisfying neither `(2×)` nor `(½×)`. -/
def EStar : Set (Finset Seq) := {T | IsTree T ∧ ¬ TwoTimes T ∧ ¬ HalfTimes T}

end MooreFoelner


