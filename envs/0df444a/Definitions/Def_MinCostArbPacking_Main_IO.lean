-- Prove2me | Definitions.Def_MinCostArbPacking_Main_IO
-- name    : MinCostArbPacking_Main_IO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:08.958816+00:00
-- url     : https://prove2.me/theorems/597ef95e-bc9c-4bab-890e-a103ac924f5a
-- title:
--   Input and output conventions of the goal and of the subprogram lemmas
-- statement:
--   The input of Theorem 1.1 is the integer list $[n,m,k,r,\mathrm{tail}(0),\dots,\mathrm{tail}(m-1),\mathrm{head}(0),\dots,\mathrm{head}(m-1)]$ and the real list $[c(0),\dots,c(m-1)]$. Output cell $0$ is $0$ exactly when no packing of $k$ arc-disjoint $r$-arborescences exists; otherwise it is $1$, cell $1+i(n-1)+j$ ($j<n-1$) names the arcs of arborescence $i$, and the decoded packing has cost at most that of **every** packing of the input graph. The bound (1.1) is
--   $$k\,m\log(kn)+k^2 n\log n\log^2(kn)+k^4 n\log^2(kn),\qquad \log x=\max\{1,\log_2 x\}.$$
--
--   Analogous layouts are fixed for the subprograms: forest-labelled arc sets and tight-block labels (Lemma 3.4); digraphs and arc labels $0$ (not chosen) or $i+1$ (forest $i$) (Lemma 3.6, Algorithm 2); the block repair of Lemma 4.15; and phase inputs (instance, current set $I$ with forest labels, chosen vertices $U$, prices $h$) with distance and path outputs (Lemma 4.9's proposal step, Lemma 5.4). Each comes with its precondition, the hypotheses the paper states for that step, and its output condition.
--
--   Decoding is a total function of the final memory and performs no computation.
--
--   **Formalization Note** `size` is the sum of the integer header values ($n+m+k$ for a graph), so $k$ may exceed any polynomial in $n$. Paths are output as offsets, lengths and arc lists.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Theorem 1.1, p.1; Lemmas 3.4, 3.6, 3.7, pp.8–9; Lemma 4.9, p.14; Algorithm 2 and Lemmas 4.15–4.16, pp.19–20; Lemma 5.4, p.25

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
import Definitions.Def_MinCostArbPacking_Main_Machine

set_option autoImplicit false

/-!
# Input and output conventions of the programs

Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026): Theorem 1.1 (p.1), Lemmas 3.4, 3.6, 3.7
(pp.8–9), Lemma 4.9 (p.14), Lemmas 4.15–4.16 (pp.19–20), Lemma 5.4 (p.25).

Integer inputs are written to integer memory cells `0, 1, …`, real inputs to real memory cells
`0, 1, …` (`Machine.load`); outputs are read from cells `-1, -2, …` (`Machine.outI`,
`Machine.outR`). Decoding is a total function of the final memory and does no computation.
Vertices and arcs are numbered from `0`. The word bound of a run is `(size + 2)^c`, where `size` is
the sum of the integer header values (`n + m + k` for a graph), so words have `Θ(log size)` bits;
in particular `k` is not assumed polynomial in `n`.
-/

noncomputable section
open Classical

namespace MinCostArbPacking.Main

/-! ### Theorem 1.1 and Lemma 3.7: arborescence packings -/

/-- `size = n + m + k`. -/
def Instance.size (X : Instance) : ℕ := X.n + X.m + X.k

/-- Integer input `[n, m, k, r, tail 0, …, tail (m-1), head 0, …, head (m-1)]`. -/
def Instance.inI (X : Instance) : List ℤ :=
  [(X.n : ℤ), X.m, X.k, (X.r.val : ℤ)] ++ (List.finRange X.m).map (fun e => ((X.tail e).val : ℤ)) ++
    (List.finRange X.m).map (fun e => ((X.head e).val : ℤ))

/-- Real input `[c 0, …, c (m-1)]`. -/
def Instance.inR (X : Instance) : List ℝ := (List.finRange X.m).map X.c

/-- The arc-index cell of position `j` of arborescence `i`: output cell `1 + i(n-1) + j`. -/
def arbCell (X : Instance) (i j : ℕ) : ℕ := 1 + i * (X.n - 1) + j

/-- Decoded arborescence `i`: the arcs named in its `n - 1` output cells. -/
def decodeArb (X : Instance) (o : ℕ → ℤ) (i : Fin X.k) : Finset (Fin X.m) :=
  Finset.univ.filter (fun e => ∃ j, j < X.n - 1 ∧ o (arbCell X i.val j) = (e.val : ℤ))

/-- All arborescence cells hold arc indices in `[0, m)`. -/
def ArbCellsInRange (X : Instance) (o : ℕ → ℤ) : Prop :=
  ∀ i, i < X.k → ∀ j, j < X.n - 1 → 0 ≤ o (arbCell X i j) ∧ o (arbCell X i j) < X.m

/-- The output of Theorem 1.1: cell `0` is `0` exactly when no packing of `k` arc-disjoint
`r`-arborescences exists; otherwise it is `1` and the arborescence cells decode to a packing whose
cost is at most the cost of every packing of the input graph. -/
def PackingOutput (X : Instance) (o : ℕ → ℤ) : Prop :=
  (o 0 = 0 ↔ ¬ X.HasPacking) ∧
    (o 0 = 0 ∨
      (o 0 = 1 ∧ ArbCellsInRange X o ∧ X.G.IsPacking X.r X.k (decodeArb X o) ∧
        ∀ P : Fin X.k → Finset (Fin X.m), X.G.IsPacking X.r X.k P →
          packingCost X.c (decodeArb X o) ≤ packingCost X.c P))

/-- The output of Lemma 3.7 (costs ignored): the arborescence cells decode to a packing. -/
def ExtractionOutput (X : Instance) (o : ℕ → ℤ) : Prop :=
  ArbCellsInRange X o ∧ X.G.IsPacking X.r X.k (decodeArb X o)

/-- The bound (1.1): `k m log(kn) + k² n log n log²(kn) + k⁴ n log²(kn)`, `log x = max{1, log₂ x}`. -/
def boundMain (X : Instance) : ℝ :=
  (X.k : ℝ) * X.m * logL (X.k * X.n) + (X.k : ℝ) ^ 2 * X.n * logL X.n * logL (X.k * X.n) ^ 2 +
    (X.k : ℝ) ^ 4 * X.n * logL (X.k * X.n) ^ 2

/-! ### Plain digraphs (Lemma 3.6), forest-decomposed arc sets (Lemma 3.4) -/

/-- A digraph `H` with `n` vertices, `m` arcs and the integer `k`. -/
structure DigraphInput where
  n : ℕ
  m : ℕ
  k : ℕ
  tail : Fin m → Fin n
  head : Fin m → Fin n

/-- The digraph of a `DigraphInput`. -/
def DigraphInput.G (H : DigraphInput) : Digraph (Fin H.n) (Fin H.m) := ⟨H.tail, H.head⟩

/-- `size = n + m + k`. -/
def DigraphInput.size (H : DigraphInput) : ℕ := H.n + H.m + H.k

/-- Integer input `[n, m, k, tails…, heads…]`. -/
def DigraphInput.inI (H : DigraphInput) : List ℤ :=
  [(H.n : ℤ), H.m, H.k] ++ (List.finRange H.m).map (fun e => ((H.tail e).val : ℤ)) ++
    (List.finRange H.m).map (fun e => ((H.head e).val : ℤ))

/-- Arc-label output: cell `e` is `0` if arc `e` is not chosen and `i + 1` if it is in forest `i`. -/
def labelsInRange (k m : ℕ) (o : ℕ → ℤ) : Prop := ∀ e, e < m → 0 ≤ o e ∧ o e ≤ k

/-- The chosen arc set of a label output. -/
def decodeSet {m : ℕ} (o : ℕ → ℤ) : Finset (Fin m) := Finset.univ.filter (fun e => o e.val ≠ 0)

/-- The forests of a label output. -/
def decodeForests {m k : ℕ} (o : ℕ → ℤ) : Fin k → Finset (Fin m) :=
  fun i => Finset.univ.filter (fun e => o e.val = (i.val : ℤ) + 1)

/-- The output of Lemma 3.6: a union `B` of `k` forests with a forest decomposition, indegree at
most `k` at every vertex, of maximum cardinality among all such subsets of the arcs of `H`; and a
basis of `𝒢^k(H)` when every vertex of `H` has indegree at most `k`. -/
def ForestPackingOutput (H : DigraphInput) (o : ℕ → ℤ) : Prop :=
  labelsInRange H.k H.m o ∧
    H.G.ForestDecomp H.k (decodeSet o) (decodeForests o) ∧
    (∀ v, H.G.inDeg (decodeSet o) v ≤ H.k) ∧
    (∀ X : Finset (Fin H.m), H.G.IndepK H.k X → (∀ v, H.G.inDeg X v ≤ H.k) →
      X.card ≤ (decodeSet (m := H.m) o).card) ∧
    ((∀ v, H.G.inDeg Finset.univ v ≤ H.k) → H.G.IsBasisOf H.k (decodeSet o) Finset.univ)

/-- An arc set (all arcs of the input) on `n` vertices with a labelling into `k` classes (Lemma 3.4:
the set `I` with its forest decomposition). -/
structure LabelledInput where
  n : ℕ
  s : ℕ
  k : ℕ
  tail : Fin s → Fin n
  head : Fin s → Fin n
  lab : Fin s → Fin k

/-- The digraph of a `LabelledInput`. -/
def LabelledInput.G (Y : LabelledInput) : Digraph (Fin Y.n) (Fin Y.s) := ⟨Y.tail, Y.head⟩

/-- The classes of the labelling. -/
def LabelledInput.F (Y : LabelledInput) : Fin Y.k → Finset (Fin Y.s) :=
  fun i => Finset.univ.filter (fun e => Y.lab e = i)

/-- `size = n + s + k`. -/
def LabelledInput.size (Y : LabelledInput) : ℕ := Y.n + Y.s + Y.k

/-- Integer input `[n, k, s, tails…, heads…, labels…]`. -/
def LabelledInput.inI (Y : LabelledInput) : List ℤ :=
  [(Y.n : ℤ), Y.k, Y.s] ++ (List.finRange Y.s).map (fun e => ((Y.tail e).val : ℤ)) ++
    (List.finRange Y.s).map (fun e => ((Y.head e).val : ℤ)) ++
    (List.finRange Y.s).map (fun e => ((Y.lab e).val : ℤ))

/-- The output of Lemma 3.4: vertex labels with `v, w` in the same tight block of `I` (all arcs)
iff their labels agree. -/
def TightBlocksOutput (Y : LabelledInput) (o : ℕ → ℤ) : Prop :=
  ∀ v w : Fin Y.n, o v.val = o w.val ↔
    Y.G.blockOf Y.k Finset.univ v = Y.G.blockOf Y.k Finset.univ w

/-! ### Lemma 4.16 (Extend) and Lemma 4.15 (restoring a mandatory arc) -/

/-- The contracted graph of Algorithm 2: `t` vertices, arcs `H` with tails and heads, `k`, and the
mandatory flags (the arcs of `I^cr`). -/
structure ExtendInput where
  t : ℕ
  h : ℕ
  k : ℕ
  tail : Fin h → Fin t
  head : Fin h → Fin t
  mand : Fin h → Bool

/-- The digraph of an `ExtendInput`. -/
def ExtendInput.G (Z : ExtendInput) : Digraph (Fin Z.t) (Fin Z.h) := ⟨Z.tail, Z.head⟩

/-- The mandatory arcs `I^cr`. -/
def ExtendInput.M (Z : ExtendInput) : Finset (Fin Z.h) := Finset.univ.filter (fun e => Z.mand e)

/-- `size = t + h + k`. -/
def ExtendInput.size (Z : ExtendInput) : ℕ := Z.t + Z.h + Z.k

/-- Integer input `[t, h, k, tails…, heads…, flags…]` (flag `1` = mandatory). -/
def ExtendInput.inI (Z : ExtendInput) : List ℤ :=
  [(Z.t : ℤ), Z.h, Z.k] ++ (List.finRange Z.h).map (fun e => ((Z.tail e).val : ℤ)) ++
    (List.finRange Z.h).map (fun e => ((Z.head e).val : ℤ)) ++
    (List.finRange Z.h).map (fun e => if Z.mand e then (1 : ℤ) else 0)

/-- Algorithm 2's Input line: indegree at most `k` everywhere, `I^cr` independent in `𝒢^k`. -/
def ExtendInput.Pre (Z : ExtendInput) : Prop :=
  (∀ v, Z.G.inDeg Finset.univ v ≤ Z.k) ∧ Z.G.IndepK Z.k Z.M

/-- Algorithm 2's Output line: a largest independent `K` with `I^cr ⊆ K ⊆ I^cr ∪ A`, with a forest
decomposition (label output). -/
def ExtendOutput (Z : ExtendInput) (o : ℕ → ℤ) : Prop :=
  labelsInRange Z.k Z.h o ∧ Z.G.ForestDecomp Z.k (decodeSet o) (decodeForests o) ∧
    Z.M ⊆ decodeSet o ∧
    ∀ X : Finset (Fin Z.h), Z.M ⊆ X → Z.G.IndepK Z.k X → X.card ≤ (decodeSet (m := Z.h) o).card

/-- Lemma 4.15's input: a block `T = Fin t`, the arcs `Fin s` of `B[T]` with their tree labels and
mandatory flags, and the ends `(eu, ev)` of the missing mandatory arc `e`. -/
structure RepairInput where
  t : ℕ
  s : ℕ
  k : ℕ
  tail : Fin s → Fin t
  head : Fin s → Fin t
  lab : Fin s → Fin k
  mand : Fin s → Bool
  eu : Fin t
  ev : Fin t

/-- The digraph `B[T] + e`: arc `some j` is arc `j` of `B[T]`, arc `none` is `e`. -/
def RepairInput.G (R : RepairInput) : Digraph (Fin R.t) (Option (Fin R.s)) :=
  ⟨fun a => match a with | some j => R.tail j | none => R.eu,
   fun a => match a with | some j => R.head j | none => R.ev⟩

/-- The `k` trees `F_i[T]` of `B[T]`. -/
def RepairInput.F (R : RepairInput) : Fin R.k → Finset (Option (Fin R.s)) :=
  fun i => (Finset.univ.filter (fun j => R.lab j = i)).image some

/-- `I^cr ∩ (B[T] + e)`: the mandatory arcs together with `e`. -/
def RepairInput.M (R : RepairInput) : Finset (Option (Fin R.s)) :=
  insert none ((Finset.univ.filter (fun j => R.mand j)).image some)

/-- `size = t + s + k`. -/
def RepairInput.size (R : RepairInput) : ℕ := R.t + R.s + R.k

/-- Integer input `[t, s, k, eu, ev, tails…, heads…, labels…, flags…]`. -/
def RepairInput.inI (R : RepairInput) : List ℤ :=
  [(R.t : ℤ), R.s, R.k, (R.eu.val : ℤ), (R.ev.val : ℤ)] ++
    (List.finRange R.s).map (fun e => ((R.tail e).val : ℤ)) ++
    (List.finRange R.s).map (fun e => ((R.head e).val : ℤ)) ++
    (List.finRange R.s).map (fun e => ((R.lab e).val : ℤ)) ++
    (List.finRange R.s).map (fun e => if R.mand e then (1 : ℤ) else 0)

/-- Lemma 4.15's hypotheses: the trees are spanning trees of `T`, and the mandatory arcs together
with `e` are independent in `𝒢^k` (`e ∈ I^cr`, `I^cr` independent). -/
def RepairInput.Pre (R : RepairInput) : Prop :=
  (∀ i, R.G.IsSpanningTreeOn (R.F i) Finset.univ) ∧ R.G.IndepK R.k R.M

/-- The new tree of index `i` after the repair: output cell `0` is the removed arc `f`, cell `1 + j`
is the new label of arc `j ≠ f` of `B[T]`, cell `1 + s` the label of `e`. -/
def repairForests (R : RepairInput) (o : ℕ → ℤ) : Fin R.k → Finset (Option (Fin R.s)) := fun i =>
  ((Finset.univ.filter (fun j : Fin R.s => (j.val : ℤ) ≠ o 0 ∧ o (1 + j.val) = i.val)).image some) ∪
    (if o (1 + R.s) = i.val then {none} else ∅)

/-- Lemma 4.15's output: an arc `f ∈ B[T] ∖ I^cr` and a decomposition of `B[T] - f + e` into `k`
spanning trees of `T`. -/
def RepairOutput (R : RepairInput) (o : ℕ → ℤ) : Prop :=
  ∃ f : Fin R.s, o 0 = f.val ∧ R.mand f = false ∧
    (∀ j : Fin R.s, j ≠ f → 0 ≤ o (1 + j.val) ∧ o (1 + j.val) < R.k) ∧
    0 ≤ o (1 + R.s) ∧ o (1 + R.s) < R.k ∧
    ∀ i, R.G.IsSpanningTreeOn (repairForests R o i) Finset.univ

/-! ### Phase inputs (Lemma 4.9's proposal step, Lemma 5.4) -/

/-- A phase input: an instance, the current set `I` with its forest decomposition as arc labels
(`0` = not in `I`, `i + 1` = in forest `i`), the chosen vertices `U`, and vertex prices `h`. -/
structure PhaseInput where
  X : Instance
  lab : Fin X.m → ℕ
  U : Finset (Fin X.n)
  h : Fin X.n → ℝ

/-- The current set `I`. -/
def PhaseInput.I (Y : PhaseInput) : Finset (Fin Y.X.m) := Finset.univ.filter (fun e => Y.lab e ≠ 0)

/-- Its forests. -/
def PhaseInput.F (Y : PhaseInput) : Fin Y.X.k → Finset (Fin Y.X.m) :=
  fun i => Finset.univ.filter (fun e => Y.lab e = i.val + 1)

/-- Integer input `X.inI ++ [labels…] ++ [U-flags…]`. -/
def PhaseInput.inI (Y : PhaseInput) : List ℤ :=
  Y.X.inI ++ (List.finRange Y.X.m).map (fun e => (Y.lab e : ℤ)) ++
    (List.finRange Y.X.n).map (fun v => if v ∈ Y.U then (1 : ℤ) else 0)

/-- Real input without prices: the costs. -/
def PhaseInput.inR (Y : PhaseInput) : List ℝ := Y.X.inR

/-- Real input with prices: the costs, then `h 0, …, h (n-1)`. -/
def PhaseInput.inRPrices (Y : PhaseInput) : List ℝ := Y.X.inR ++ (List.finRange Y.X.n).map Y.h

/-- Labels are in `[0, k]` and form a forest decomposition of `I`. -/
def PhaseInput.Decomposed (Y : PhaseInput) : Prop :=
  (∀ e, Y.lab e ≤ Y.X.k) ∧ Y.X.G.ForestDecomp Y.X.k Y.I Y.F

/-- Path output at `base`: for each `u ∈ U`, cell `base + u` holds the offset `s_u ≥ 0`, cell
`base + n + u` the length, and cells `base + 2n + s_u + j` the arcs of a path `P` satisfying
`Spec u P`. -/
def PathsOut (Y : PhaseInput) (o : ℕ → ℤ) (base : ℕ) (Us : Finset (Fin Y.X.n))
    (Spec : Fin Y.X.n → List (Fin Y.X.m) → Prop) : Prop :=
  ∀ u ∈ Us, ∃ P : List (Fin Y.X.m), 0 ≤ o (base + u.val) ∧
    o (base + Y.X.n + u.val) = P.length ∧
    (∀ j (hj : j < P.length),
      o (base + 2 * Y.X.n + (o (base + u.val)).toNat + j) = ((P.get ⟨j, hj⟩).val : ℤ)) ∧
    Spec u P

/-- Input condition of the proposal step of Algorithm 1 (Lemma 4.9): the §4.2 invariants, a forest
decomposition, and `U` consists of one deficient vertex in each deficient tight block. -/
def PhaseInput.ProposalPre (Y : PhaseInput) : Prop :=
  Y.Decomposed ∧ Y.X.G.Standing Y.X.k Y.X.r Y.X.c Y.I ∧
    (∀ u ∈ Y.U, 0 < Y.X.G.defi Y.X.k Y.X.r Y.I u) ∧
    ∀ T, Y.X.G.IsTightBlock Y.X.k Y.I T → 0 < Y.X.G.defiSet Y.X.k Y.X.r Y.I T →
      (Y.U.filter (fun v => v ∈ T)).card = 1

/-- Output of the proposal step: cell `0` is `0` iff some `u ∈ U` has no augmenting path;
otherwise it is `1` and a shortest augmenting path from every `u ∈ U` is listed (base `1`). -/
def PhaseInput.ProposalOutput (Y : PhaseInput) (o : ℕ → ℤ) : Prop :=
  (o 0 = 0 ↔ ∃ u ∈ Y.U, ¬ ∃ P, Y.X.G.AugFrom Y.X.k Y.I u P) ∧
    (o 0 = 0 ∨ (o 0 = 1 ∧
      PathsOut Y o 1 Y.U (fun u P => Y.X.G.ShortestFrom Y.X.k Y.X.c Y.I u P)))

/-- Input condition of Lemma 5.4: forest decomposition, the indegree invariants, the price invariant
(5.1), the reduced graph, and at most one chosen deficient vertex per tight block. -/
def PhaseInput.DijkstraPre (Y : PhaseInput) : Prop :=
  Y.Decomposed ∧ Y.X.G.NoLoopNoRootArc Y.X.r ∧ Y.X.G.inDeg Y.I Y.X.r = 0 ∧
    (∀ v, v ≠ Y.X.r → Y.X.G.inDeg Y.I v ≤ Y.X.k) ∧ Y.X.G.PriceInv Y.X.k Y.X.c Y.h Y.I ∧
    (∀ u ∈ Y.U, 0 < Y.X.G.defi Y.X.k Y.X.r Y.I u) ∧
    ∀ T, Y.X.G.IsTightBlock Y.X.k Y.I T → (Y.U.filter (fun v => v ∈ T)).card ≤ 1

/-- Output of Lemma 5.4: for every vertex `v`, integer cell `v` is `0` iff `δ_v = +∞`, and otherwise
`1` with real cell `v` equal to `δ_v`; and a shortest augmenting path from every `u ∈ U` with finite
`δ_u` (path output at base `n`). -/
def PhaseInput.DijkstraOutput (Y : PhaseInput) (o : ℕ → ℤ) (or : ℕ → ℝ) : Prop :=
  (∀ v : Fin Y.X.n,
    (o v.val = 0 ↔ Y.X.G.delta Y.X.k Y.X.c Y.h Y.I v = ⊤) ∧
      (o v.val = 0 ∨ (o v.val = 1 ∧ ((or v.val : ℝ) : EReal) = Y.X.G.delta Y.X.k Y.X.c Y.h Y.I v))) ∧
    PathsOut Y o Y.X.n (Y.U.filter (fun u => Y.X.G.delta Y.X.k Y.X.c Y.h Y.I u ≠ ⊤))
      (fun u P => Y.X.G.ShortestFrom Y.X.k Y.X.c Y.I u P)

end MinCostArbPacking.Main


