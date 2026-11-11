-- Prove2me | Definitions.Def_OptimalXOR_Total_StandardEmbedding
-- name    : OptimalXOR_Total_StandardEmbedding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:10.854568+00:00
-- url     : https://prove2.me/theorems/8b40319f-9c65-4630-b675-0dc0b2c353aa
-- title:
--   Definition 3.1 — the standard embedding $\pi^{(j)}$ into coordinate $j$ of a protocol on $\mathcal X^t\times\mathcal Y^t$
-- statement:
--   Let $\nu\in\mathcal P(\mathcal X\times\mathcal Y)$, let $t\ge1$, and let $\pi$ be a protocol with input $(X,Y)=((X_1,\dots,X_t),(Y_1,\dots,Y_t))\in\mathcal X^t\times\mathcal Y^t$ and public randomness $R$. For $j\in[t]$, the **standard embedding** $\pi^{(j)}$ into coordinate $j$ of $\pi$ with respect to $\nu$ operates on input $(x,y)\in\mathcal X\times\mathcal Y$ as follows.
--
--   1. The parties publicly sample $(X_{<j},Y_{>j})$ from its distribution under $\nu^t$, and set $(X_j,Y_j)=(x,y)$.
--   2. Alice privately samples $X_{>j}$ from its conditional distribution under $\nu^t$ given $Y_{>j}$; Bob privately samples $Y_{<j}$ from its conditional distribution under $\nu^t$ given $X_{<j}$.
--   3. The parties run $\pi$ on $(X,Y)$, and each party outputs what it outputs in this run of $\pi$.
--
--   The public randomness of $\pi^{(j)}$ is $(R,X_{<j},Y_{>j})$ and its transcript is that of $\pi$. If $(x,y)\sim\nu$, the completed input $(X,Y)$ has law $\nu^t$.
--
--   This is the construction behind Fact 3.2 and the reductions of §3.
--
--   **Formalization Note** Coordinates are `Fin t`. The public tape of `standardEmbedding ν π j` is that of $\pi$ times a draw of $(X_{<j},Y_{>j})$ from `publicLaw ν j`, the image of `pmfPow ν t`. Conditional sampling is realized by a table: Alice's private tape adds, for each $i>j$ and each $y$, an independent draw from $\nu(\cdot\mid Y=y)$ (`aliceLaw`), and she uses the entry at $y=Y_i$, which gives $X_{>j}$ the conditional law $\prod_{i>j}\nu(\cdot\mid Y_i)$ of $X_{>j}$ given $Y_{>j}$ under $\nu^t$; Bob's table is symmetric (`bobLaw`). A conditional law given a null event, which the paper leaves arbitrary, is the marginal (`condFst`, `condSnd`). The added finite tapes carry the discrete σ-algebra.
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 22 (PDF 24), Definition 3.1

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_Compositions

open MeasureTheory

namespace OptimalXOR.Total

open CaiZhuInfo.Matrix

/-! Sherstov, *Optimal XOR Lemmas for Information Complexity*, STOC 2027 submission,
Definition 3.1 (Standard embedding), printed p. 22 / PDF p. 24.

For `ν ∈ P(X × Y)`, a protocol `π` with input `(X, Y) ∈ Xᵗ × Yᵗ` and a coordinate `j`, the protocol
`π^{(j)}` on input `(x, y) ∈ X × Y`:
(a) publicly samples `(X_{<j}, Y_{>j})` from its law under `νᵗ` and sets `(X_j, Y_j) = (x, y)`;
(b) Alice privately samples `X_{>j}` from its conditional law under `νᵗ` given `Y_{>j}`, and Bob
    privately samples `Y_{<j}` from its conditional law under `νᵗ` given `X_{<j}`;
(c) runs `π` on `(X, Y)`, and each party outputs what it outputs in this run of `π`.
Its public randomness is `(R, X_{<j}, Y_{>j})` and its transcript is that of `π`.

Private conditional sampling is realized by a table of independent draws: Alice's private tape
holds, for each coordinate `i > j` and each `y ∈ Y`, an independent sample of `ν(· | Y = y)`, and
she uses the entry at `y = Y_i`. Given `Y_{>j}`, this yields `X_{>j}` with law
`∏_{i>j} ν(· | Y_i)`, the conditional law of `X_{>j}` given `Y_{>j}` under `νᵗ`; Bob's tape is
symmetric. Conditional laws on null events are arbitrary in the paper; here they are the
marginal. Coordinates are `Fin t = {0, …, t−1}`. -/

noncomputable section

/-- A random source with a finite (or countable) law, with the discrete σ-algebra. -/
abbrev sourceOfPMF {α : Type} (p : PMF α) : RandomSource where
  Carrier := α
  measurable := ⊤
  law := @PMF.toMeasure α ⊤ p
  probability := @PMF.toMeasure.isProbabilityMeasure α ⊤ p

variable {X Y Z : Type}

open scoped Classical in
/-- The conditional law of `X` given `Y = y` under `(X, Y) ∼ ν` (the marginal of `X` if
`P[Y = y] = 0`). -/
def condFst (ν : PMF (X × Y)) (y : Y) : PMF X :=
  if h : ∃ p ∈ {p : X × Y | p.2 = y}, p ∈ ν.support then
    (ν.filter {p | p.2 = y} h).map Prod.fst
  else ν.map Prod.fst

open scoped Classical in
/-- The conditional law of `Y` given `X = x` under `(X, Y) ∼ ν` (the marginal of `Y` if
`P[X = x] = 0`). -/
def condSnd (ν : PMF (X × Y)) (x : X) : PMF Y :=
  if h : ∃ p ∈ {p : X × Y | p.1 = x}, p ∈ ν.support then
    (ν.filter {p | p.1 = x} h).map Prod.snd
  else ν.map Prod.snd

variable {t : ℕ}

/-- The publicly sampled part `(X_{<j}, Y_{>j})`. -/
abbrev PublicSample (X Y : Type) (j : Fin t) :=
  ({i : Fin t // i < j} → X) × ({i : Fin t // j < i} → Y)

/-- Alice's private table: for each `i > j` and each `y`, a sample of `ν(· | Y = y)`. -/
abbrev AliceTable (X Y : Type) (j : Fin t) := {i : Fin t // j < i} × Y → X

/-- Bob's private table: for each `i < j` and each `x`, a sample of `ν(· | X = x)`. -/
abbrev BobTable (X Y : Type) (j : Fin t) := {i : Fin t // i < j} × X → Y

variable [Fintype X] [Fintype Y]

/-- The law of `(X_{<j}, Y_{>j})` under `νᵗ`. -/
def publicLaw (ν : PMF (X × Y)) (j : Fin t) : PMF (PublicSample X Y j) :=
  (pmfPow ν t).map (fun p => (fun i => p.1 i.1, fun i => p.2 i.1))

open scoped Classical in
/-- Alice's table: independent entries, entry `(i, y)` with law `ν(· | Y = y)`. -/
def aliceLaw (ν : PMF (X × Y)) (j : Fin t) : PMF (AliceTable X Y j) :=
  pmfPi (fun q : {i : Fin t // j < i} × Y => condFst ν q.2)

open scoped Classical in
/-- Bob's table: independent entries, entry `(i, x)` with law `ν(· | X = x)`. -/
def bobLaw (ν : PMF (X × Y)) (j : Fin t) : PMF (BobTable X Y j) :=
  pmfPi (fun q : {i : Fin t // i < j} × X => condSnd ν q.2)

/-- Alice's completed input: `X_{<j}` public, `X_j = x`, `X_i` (`i > j`) from her table at `Y_i`. -/
def embedX (j : Fin t) (x : X) (s : PublicSample X Y j) (a : AliceTable X Y j) : Fin t → X :=
  fun i => if h : i < j then s.1 ⟨i, h⟩ else if h' : j < i then a (⟨i, h'⟩, s.2 ⟨i, h'⟩) else x

/-- Bob's completed input: `Y_i` (`i < j`) from his table at `X_i`, `Y_j = y`, `Y_{>j}` public. -/
def embedY (j : Fin t) (y : Y) (s : PublicSample X Y j) (b : BobTable X Y j) : Fin t → Y :=
  fun i => if h : i < j then b (⟨i, h⟩, s.1 ⟨i, h⟩) else if h' : j < i then s.2 ⟨i, h'⟩ else y

/-- The standard embedding `π^{(j)}` into coordinate `j` of `π` with respect to `ν`
(Definition 3.1). -/
def standardEmbedding (ν : PMF (X × Y)) (π : Protocol (Fin t → X) (Fin t → Y) Z) (j : Fin t) :
    Protocol X Y Z where
  shared := sourceProd π.shared (sourceOfPMF (publicLaw ν j))
  privateA := sourceProd π.privateA (sourceOfPMF (aliceLaw ν j))
  privateB := sourceProd π.privateB (sourceOfPMF (bobLaw ν j))
  tree := π.tree
  sendA x r a h := π.sendA (embedX j x r.2 a.2) r.1 a.1 h
  sendB y r b h := π.sendB (embedY j y r.2 b.2) r.1 b.1 h
  out y r b h := π.out (embedY j y r.2 b.2) r.1 b.1 h
  sendA_measurable x h := by
    let _ : MeasurableSpace (PublicSample X Y j) := ⊤
    let _ : MeasurableSpace (AliceTable X Y j) := ⊤
    have : MeasurableSingletonClass (PublicSample X Y j) := ⟨fun _ => trivial⟩
    have : MeasurableSingletonClass (AliceTable X Y j) := ⟨fun _ => trivial⟩
    have hg : Measurable (fun w : (π.shared.Carrier × π.privateA.Carrier) ×
        (PublicSample X Y j × AliceTable X Y j) => π.sendA (embedX j x w.2.1 w.2.2) w.1.1 w.1.2 h) :=
      measurable_from_prod_countable_left (fun b => π.sendA_measurable (embedX j x b.1 b.2) h)
    have hr : Measurable (fun u : (π.shared.Carrier × PublicSample X Y j) ×
        (π.privateA.Carrier × AliceTable X Y j) => ((u.1.1, u.2.1), (u.1.2, u.2.2))) :=
      (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
        (measurable_fst.snd.prodMk measurable_snd.snd)
    exact hg.comp hr
  sendB_measurable y h := by
    let _ : MeasurableSpace (PublicSample X Y j) := ⊤
    let _ : MeasurableSpace (BobTable X Y j) := ⊤
    have : MeasurableSingletonClass (PublicSample X Y j) := ⟨fun _ => trivial⟩
    have : MeasurableSingletonClass (BobTable X Y j) := ⟨fun _ => trivial⟩
    have hg : Measurable (fun w : (π.shared.Carrier × π.privateB.Carrier) ×
        (PublicSample X Y j × BobTable X Y j) => π.sendB (embedY j y w.2.1 w.2.2) w.1.1 w.1.2 h) :=
      measurable_from_prod_countable_left (fun b => π.sendB_measurable (embedY j y b.1 b.2) h)
    have hr : Measurable (fun u : (π.shared.Carrier × PublicSample X Y j) ×
        (π.privateB.Carrier × BobTable X Y j) => ((u.1.1, u.2.1), (u.1.2, u.2.2))) :=
      (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
        (measurable_fst.snd.prodMk measurable_snd.snd)
    exact hg.comp hr
  out_measurable y h := by
    let _ : MeasurableSpace (PublicSample X Y j) := ⊤
    let _ : MeasurableSpace (BobTable X Y j) := ⊤
    have : MeasurableSingletonClass (PublicSample X Y j) := ⟨fun _ => trivial⟩
    have : MeasurableSingletonClass (BobTable X Y j) := ⟨fun _ => trivial⟩
    have hg : @Measurable _ Z _ ⊤ (fun w : (π.shared.Carrier × π.privateB.Carrier) ×
        (PublicSample X Y j × BobTable X Y j) => π.out (embedY j y w.2.1 w.2.2) w.1.1 w.1.2 h) :=
      measurable_from_prod_countable_left (fun b => π.out_measurable (embedY j y b.1 b.2) h)
    have hr : Measurable (fun u : (π.shared.Carrier × PublicSample X Y j) ×
        (π.privateB.Carrier × BobTable X Y j) => ((u.1.1, u.2.1), (u.1.2, u.2.2))) :=
      (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
        (measurable_fst.snd.prodMk measurable_snd.snd)
    exact hg.comp hr

end

end OptimalXOR.Total


