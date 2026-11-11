-- Prove2me | Definitions.Def_DynColorWC_Main_OneShot
-- name    : DynColorWC_Main_OneShot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:46:06.514265+00:00
-- url     : https://prove2.me/theorems/f43e1a0c-438d-4831-b741-6036b849de01
-- title:
--   Stage (II): the one-shot random coloring with marking probability 1/100, V(II) and the slack σ₂
-- statement:
--   Each vertex is **marked** independently with probability $1/100$ and draws an independent uniform **proposal** $q_v\in[\Delta+1]$; the marks and proposals are drawn **once** and reused for every graph of the dynamic sequence. In a graph $G$, $V(\mathrm{II})$ is the set of marked $v$ such that no marked neighbor $u$ of $v$ has $q_u=q_v$; such $v$ gets color $q_v$. For a set $S$, $\chi(S)=\{q_u:u\in S\}$. The **slack after stage (II)** is
--   $$\sigma_2(v)=\Delta+1-\deg(v)+|N(v)\cap V(\mathrm{II})|-|\chi(N(v)\cap V(\mathrm{II}))|.$$
--
--   **Formalization Note.** The draw is one uniform pair $(r_v,q_v)\in\{0,\dots,99\}\times[\Delta+1]$ per vertex, all independent, with $v$ marked iff $r_v=0$; this is exactly independent Bernoulli$(1/100)$ marks and independent uniform proposals. Colors $[\Delta+1]$ are `Fin (Δ+1)`.
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, §5.1 stage (II), p. 50 (PDF 52); Eq. (7), p. 52 (PDF 54)

import Mathlib

namespace DynColorWC.Main

/-! # Stage (II): the one-shot random coloring and its slack

Flin and Ghaffari (2026), *Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time*,
STOC 2027 submission, supplied PDF sha256 93ebb2ff…3154300e3, §5.1 stage (II), p. 50 (PDF 52), and
Eq. (7), p. 52 (PDF 54):
"We mark each node randomly with probability 1/100. For each node v, we choose an independent
uniform color q_v ∈ [∆ + 1] … the marks and these proposals remain fixed throughout the dynamic
algorithm. If v is marked and there is no neighbor u ∈ N(v) that is marked and has q_u = q_v, then
node v gets colored with color q_v."

* One draw is made **once**, for the whole run: each vertex `v` independently draws a uniform pair
  `(r_v, q_v) ∈ {0,…,99} × [Δ+1]`; `v` is **marked** iff `r_v = 0` (probability exactly `1/100`), and
  `q_v` is its proposed color. Colors `[Δ+1]` are `Fin (Δ+1)` (`q` stands for color `q + 1`).
* For a graph `G` (any snapshot `G_t` of the dynamic graph, with the same fixed draw),
  `V(II) = {v marked : no marked neighbor u of v has q_u = q_v}`, and the stage-(II) color of
  `v ∈ V(II)` is `q_v`. For a set `S`, `χ(S)` is the set of colors `{q_u : u ∈ S}`.
* The slack after stage (II) is
  `σ₂(v) = Δ + 1 − deg(v) + |N(v) ∩ V(II)| − |χ(N(v) ∩ V(II))|` (Eq. (7)). -/

/-- The per-vertex draw: `r ∈ {0,…,99}` (marked iff `r = 0`) and the proposed color `q ∈ Fin (Δ+1)`. -/
abbrev OneShotDraw (n Δ : ℕ) := Fin n → Fin 100 × Fin (Δ + 1)

/-- The law of the draw: all `n` pairs independent and uniform on `Fin 100 × Fin (Δ+1)` (so marks
are independent `Bernoulli(1/100)`, proposals independent uniform on `[Δ+1]`, and the two are
independent). -/
noncomputable def oneShotMeasure (n Δ : ℕ) : MeasureTheory.Measure (OneShotDraw n Δ) :=
  MeasureTheory.Measure.pi fun _ => (PMF.uniformOfFintype (Fin 100 × Fin (Δ + 1))).toMeasure

/-- `v` is marked. -/
def IsMarked {n Δ : ℕ} (x : OneShotDraw n Δ) (v : Fin n) : Prop := (x v).1 = 0

open Classical in
/-- `V(II)` in the graph `G`: marked vertices with no marked neighbor proposing the same color. -/
noncomputable def stageTwoSet {n Δ : ℕ} (G : SimpleGraph (Fin n)) (x : OneShotDraw n Δ) :
    Finset (Fin n) :=
  Finset.univ.filter fun v =>
    IsMarked x v ∧ ∀ u, G.Adj v u → IsMarked x u → (x u).2 ≠ (x v).2

open Classical in
/-- `σ₂(v) = Δ + 1 − deg(v) + |N(v) ∩ V(II)| − |χ(N(v) ∩ V(II))|` (Eq. (7)), as a real number. -/
noncomputable def stageTwoSlack {n Δ : ℕ} (G : SimpleGraph (Fin n)) (x : OneShotDraw n Δ)
    (v : Fin n) : ℝ :=
  ((Δ : ℝ) + 1 - G.degree v) + ((G.neighborFinset v ∩ stageTwoSet G x).card : ℝ) -
    (((G.neighborFinset v ∩ stageTwoSet G x).image fun u => (x u).2).card : ℝ)

end DynColorWC.Main


