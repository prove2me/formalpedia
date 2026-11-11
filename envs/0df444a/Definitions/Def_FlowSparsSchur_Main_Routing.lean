-- Prove2me | Definitions.Def_FlowSparsSchur_Main_Routing
-- name    : FlowSparsSchur_Main_Routing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:23:40.323779+00:00
-- url     : https://prove2.me/theorems/8f6390b2-8340-4872-95c9-a790c012b4f5
-- title:
--   Multicommodity demands and flows, entrywise-absolute load, congestion, q-embeddings and q-flow sparsifiers on a terminal set
-- statement:
--   Let $G$ be a graph on $V$ with edges $E$ and capacities $u_G$. A **multicommodity demand** with $a$ commodities is a matrix $D\in\mathbb R^{V\times a}$ whose every column sums to zero ($\mathbf 1^\top D=0$). A **multicommodity flow** $F\in\mathbb R^{E\times a}$ **routes** $D$ if $B_G^\top F=D$. Its load on edge $e$ sums absolute values over commodities, so flows of different commodities never cancel:
--   $$\mathrm{load}_e(F)=\sum_{j}|F(e,j)|,\qquad \mathrm{cong}_e(F)=\mathrm{load}_e(F)/u_G(e).$$
--   $D$ **can be routed in $G$ with congestion $q$** if some $F$ routing $D$ has $\mathrm{load}_e(F)\le q\,u_G(e)$ for every edge, i.e. $\|\mathrm{cong}(F)\|_\infty\le q$.
--
--   For a terminal set $S$, an **$S$-multicommodity demand** has zero rows outside $S$; here it is a matrix $D\in\mathbb R^{S\times a}$ with zero column sums, placed in a graph through the map of $S$ into its vertex set (zero rows elsewhere). For graphs $G,H$ containing $S$, **$H$ $q$-embeds into $G$**, $H\overset{q}{\hookrightarrow}G$, if every $S$-multicommodity demand (any number $a$ of commodities) that can be routed in $H$ with congestion $1$ can be routed in $G$ with congestion $q$. A graph $H$ with vertex set exactly $S$ is a **$q$-flow sparsifier** of $G$ for $S$ if
--   $$G\overset{1}{\hookrightarrow}H\quad\text{and}\quad H\overset{q}{\hookrightarrow}G .$$
--
--   **Formalization Note** `QEmbeds q H G ιH ιG` takes the terminal type `K` and its maps into both vertex sets; for a graph on `↥S` the map is the identity, for $G$ it is the inclusion. Congestion is written as `load ≤ q · cap` (no division), which is the source's condition for positive capacities and treats a zero-capacity edge as unusable.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), pp. 13–14, §4.2

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph

/-!
# Multicommodity demands and flows, load, congestion, q-embeddings and q-flow sparsifiers

Goranci, Henzinger, Momeni, Räcke, Sricharan, *Breaking the Quadratic Time Barrier for Flow
Sparsifiers via Schur Complement Localization*, STOC 2027 submission, §4.2 (pp. 13–14).

* A multicommodity demand with `a` commodities is `D ∈ ℝ^{V × a}` with `1ᵀD = 0`; a flow
  `F ∈ ℝ^{E × a}` routes `D` if `B_Gᵀ F = D`.
* `load(F) = F̄ 1` (entrywise absolute values summed over commodities, no cancellation),
  `cong(F) = load(F)/u_G`. "`D` can be routed with congestion `q`" means some `F` routing `D` has
  `‖cong(F)‖_∞ ≤ q`, written here without division as `load_e(F) ≤ q · u_G(e)` for every edge.
* Terminal demands live on a terminal type `K` and are transported to a graph through a map
  `ι : K → V` (zero rows on vertices outside the image): for `K = S ⊆ V(G)` this is the paper's
  `S`-multicommodity demand.
* `H ↪^q G` (terminals `K`): every terminal demand routable in `H` with congestion `1` is
  routable in `G` with congestion `q`, for every number of commodities.
* `H` is a `q`-flow sparsifier of `G` for `S` if `G ↪^1 H` and `H ↪^q G`.
-/

namespace FlowSparsSchur.Main

open Matrix

variable {V E : Type}

/-- `D` is a multicommodity demand: every column sums to `0` (`1ᵀD = 0`). -/
def IsDemand [Fintype V] {a : ℕ} (D : Matrix V (Fin a) ℝ) : Prop :=
  ∀ j, ∑ v, D v j = 0

/-- The multicommodity flow `F` routes `D` in `G`: `B_Gᵀ F = D`. -/
def Routes [Fintype E] [DecidableEq V] (G : CGraph V E) {a : ℕ} (F : Matrix E (Fin a) ℝ)
    (D : Matrix V (Fin a) ℝ) : Prop :=
  (G.incidence)ᵀ * F = D

/-- `load_e(F) = Σ_j |F(e, j)|`, the `e`-entry of `F̄ 1`. -/
def load {a : ℕ} (F : Matrix E (Fin a) ℝ) (e : E) : ℝ := ∑ j, |F e j|

/-- `D` can be routed in `G` with congestion `q`: some flow routing `D` has
`load_e(F) ≤ q · u_G(e)` on every edge (`‖cong(F)‖_∞ ≤ q`). -/
def RoutableWith [Fintype E] [DecidableEq V] (G : CGraph V E) {a : ℕ}
    (D : Matrix V (Fin a) ℝ) (q : ℝ) : Prop :=
  ∃ F : Matrix E (Fin a) ℝ, Routes G F D ∧ ∀ e, load F e ≤ q * G.cap e

/-- Transport a demand on terminals `K` to the vertices `V` along `ι` (rows of vertices outside the
image of `ι` are zero). -/
def extendDemand {K : Type} [Fintype K] [DecidableEq V] (ι : K → V) {a : ℕ}
    (D : Matrix K (Fin a) ℝ) : Matrix V (Fin a) ℝ :=
  fun v j => ∑ k, if ι k = v then D k j else 0

/-- `H ↪^q G` for terminals `K` placed in `H` by `ιH` and in `G` by `ιG`: every terminal
multicommodity demand (any number `a` of commodities) that can be routed in `H` with congestion `1`
can be routed in `G` with congestion `q`. -/
def QEmbeds {W F K : Type} [Fintype F] [Fintype E] [Fintype K] [DecidableEq W] [DecidableEq V]
    (q : ℝ) (H : CGraph W F) (G : CGraph V E) (ιH : K → W) (ιG : K → V) : Prop :=
  ∀ (a : ℕ) (D : Matrix K (Fin a) ℝ), IsDemand D →
    RoutableWith H (extendDemand ιH D) 1 → RoutableWith G (extendDemand ιG D) q

/-- `H` (a graph on the terminal set `S`, `V(H) = S`) is a `q`-flow sparsifier of `G` for `S`:
`G ↪^1 H` and `H ↪^q G`. -/
def IsFlowSparsifier {F : Type} [Fintype F] [Fintype E] [DecidableEq V] (q : ℝ)
    (G : CGraph V E) (S : Finset V) (H : CGraph S F) : Prop :=
  QEmbeds 1 G H (fun s : S => s.val) (fun s : S => s) ∧
    QEmbeds q H G (fun s : S => s) (fun s : S => s.val)

end FlowSparsSchur.Main


