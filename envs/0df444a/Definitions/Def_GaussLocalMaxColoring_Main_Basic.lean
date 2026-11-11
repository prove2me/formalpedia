-- Prove2me | Definitions.Def_GaussLocalMaxColoring_Main_Basic
-- name    : GaussLocalMaxColoring_Main_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:19:50.107284+00:00
-- url     : https://prove2.me/theorems/2e234efb-1adb-4033-afff-b7e595ce804a
-- title:
--   Graphs, vector colorings, Gaussian local maxima $I_F(g)$, $p_F(x)$, edge residuals, neighborhood maxima $M_F(x)$, $\rho_x$, $u_x$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph on $V=\{0,\dots,n-1\}$; the order of $V$ is the paper's fixed total order used to break ties. For $F\subseteq V$, $N_F(x)=\{y\in F: xy\in E\}$, and $\Delta(G[S])=\max_{x\in S}|N_S(x)|$ ($0$ for $S=\emptyset$). Vectors lie in $\mathbb R^d$ for an arbitrary dimension $d$, and $g\sim N(0,I_d)$ is a standard Gaussian vector.
--
--   * **Ordinary vector $k$-coloring** (Definition 11, real $k\ge 2$): unit vectors $\{v_x\}_{x\in V}$ with $\langle v_x,v_y\rangle\le -1/(k-1)$ for every edge. (The strict vector 3-coloring of Definition 10 is the published `StrictVectorColoring`.)
--   * **Local maxima** (p. 11): $I_F(g)=\{x\in F:\ \forall y\in N_F(x),\ (\langle g,v_x\rangle,x)>(\langle g,v_y\rangle,y)\}$, lexicographically; $p_F(x)=\mathbb P_g[x\in I_F(g)]$ (p. 17).
--   * **Edge residual** (§3.2): $v_{xy}=(v_y-\langle v_x,v_y\rangle v_x)/\|v_y-\langle v_x,v_y\rangle v_x\|$.
--   * **Neighborhood maximum** (p. 17): $M_F(x)=\max_{y\in N_F(x)}\langle g,v_{xy}\rangle$, and $M_F(x)=-\infty$ when $N_F(x)=\emptyset$; $\overline\Phi(m/c)$ is extended by $\overline\Phi(-\infty)=1$.
--   * For a root $r$: $\rho_x=\langle v_r,v_x\rangle$ and $u_x=v_x-\rho_xv_r$ (§3.2).
--   * $\ell=\lceil\log n\rceil$ (natural logarithm), and an **$o(1)$ term** is one function $g:\mathbb N\to\mathbb R$ with $g(n)\to 0$.
--
--   **Formalization Note.** $M_F(x)$ takes values in `WithBot ℝ` so that the empty neighborhood gives $-\infty$, not $0$. The residual is defined by the formula for all pairs; it is the paper's $v_{xy}$ whenever $v_y\neq\pm v_x$ (in particular on every edge of a strict vector 3-coloring, where $v_{xy}=(2v_y+v_x)/\sqrt3$), and the zero vector otherwise.
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), §3 (printed pp. 11–13, PDF 13–15), Definition 11 (p. 12), §4.2.1 (p. 17, PDF 19)

import Mathlib
import Definitions.Def_RecGaussColoring_Main_Gaussian
import Definitions.Def_RecGaussColoring_Main_Rounding

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical
noncomputable section

namespace GaussLocalMaxColoring.Main

/-! # Graphs, vector colorings, Gaussian local maxima, edge residuals, neighborhood maxima

Deguchi, Kawarabayashi, Yoneda, Yoneda, *An O(n^0.1537)-Coloring Algorithm for 3-Colorable
Graphs*, arXiv:2610.35859 (SHA-256 9917b0a1…), §3 (printed pp. 11–13, PDF 13–15), §4.2.1
(p. 17, PDF 19).

The vertex set is `Fin n`; its order is the paper's "fixed total order on `V`" used to break
ties between Gaussian projections. Vectors live in `Space d = EuclideanSpace ℝ (Fin d)` for an
arbitrary dimension `d`, and `g` is drawn from Mathlib's `stdGaussian (Space d)` (`gaussProb`). -/

variable {n d : ℕ}

/-- `N_F(x) = {y ∈ F : xy ∈ E}`. -/
def nbr (G : SimpleGraph (Fin n)) (F : Finset (Fin n)) (x : Fin n) : Finset (Fin n) :=
  F.filter fun y => G.Adj x y

/-- `S` is an independent set of `G`. -/
def IsIndep (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y

/-- `Δ(G[S])`: the maximum degree of the subgraph induced by `S` (`0` for `S = ∅`). -/
def maxDegOn (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  S.sup fun x => (nbr G S x).card

/-- `G[S]` has no edge. -/
def Edgeless (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y

/-- **Definition 11** (ordinary vector `k`-coloring), real `k ≥ 2`: unit vectors with
`⟨v_x, v_y⟩ ≤ −1/(k−1)` on every edge. Any dimension `d`. -/
def OrdinaryVectorColoring (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (k : ℝ) : Prop :=
  (∀ x, ‖v x‖ = 1) ∧ ∀ x y, G.Adj x y → ⟪v x, v y⟫ ≤ -(1 / (k - 1))

/-- `I_F(g) = {x ∈ F : ∀ y ∈ N_F(x), (⟨g, v_x⟩, x) > (⟨g, v_y⟩, y)}` (p. 11), the
lexicographic comparison breaking ties by the order of `Fin n`. -/
def localMax (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (F : Finset (Fin n))
    (g : Space d) : Finset (Fin n) :=
  F.filter fun x => ∀ y ∈ nbr G F x,
    ⟪g, v y⟫ < ⟪g, v x⟫ ∨ (⟪g, v y⟫ = ⟪g, v x⟫ ∧ y < x)

/-- `p_F(x) = P_g[x ∈ I_F(g)]`, the local-maximum probability (p. 17). -/
def pLocal (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) :
    ℝ :=
  gaussProb {g : Space d | x ∈ localMax G v F g}

/-- Edge residual `v_xy = (v_y − ⟨v_x, v_y⟩ v_x)/‖v_y − ⟨v_x, v_y⟩ v_x‖` (§3.2, p. 12), defined
there for `v_y ≠ ± v_x` (for a strict vector 3-coloring and an edge `xy`, `v_xy = (2v_y + v_x)/√3`). -/
def residual (v : Fin n → Space d) (x y : Fin n) : Space d :=
  ‖v y - ⟪v x, v y⟫ • v x‖⁻¹ • (v y - ⟪v x, v y⟫ • v x)

/-- Neighborhood maximum `M_F(x) = max_{y ∈ N_F(x)} ⟨g, v_xy⟩`, with `M_F(x) = −∞` (`⊥`) when
`N_F(x) = ∅` (p. 17). -/
def nbrMax (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n)
    (g : Space d) : WithBot ℝ :=
  (nbr G F x).sup fun y => ((⟪g, residual v x y⟫ : ℝ) : WithBot ℝ)

/-- `Φ̄(m / c)` for `m ∈ [−∞, ∞)`, with `Φ̄(−∞) = 1`. -/
def tailOver (c : ℝ) : WithBot ℝ → ℝ
  | ⊥ => 1
  | (a : ℝ) => PhiTail (a / c)

/-- `ρ_x = ⟨v_r, v_x⟩` for the root `r` (§3.2, p. 12). -/
def rho (v : Fin n → Space d) (r x : Fin n) : ℝ := ⟪v r, v x⟫

/-- `u_x = v_x − ρ_x v_r` for the root `r` (§3.2, p. 12). -/
def uvec (v : Fin n → Space d) (r x : Fin n) : Space d := v x - rho v r x • v r

/-- `ℓ = ⌈log n⌉` (natural logarithm), the number of refinement levels (Tables 2, 3). -/
def numLevels (n : ℕ) : ℕ := ⌈Real.log n⌉₊

/-- An `o(1)` term: one function of `n`, fixed before the input, tending to `0`. -/
def IsLittleO1 (g : ℕ → ℝ) : Prop := Tendsto g atTop (nhds 0)

end GaussLocalMaxColoring.Main


