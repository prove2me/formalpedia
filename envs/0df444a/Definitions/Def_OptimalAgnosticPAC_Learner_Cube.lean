-- Prove2me | Definitions.Def_OptimalAgnosticPAC_Learner_Cube
-- name    : OptimalAgnosticPAC_Learner_Cube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:46.847202+00:00
-- url     : https://prove2.me/theorems/02ffe129-836d-4b3a-a3e5-71605f0d492e
-- title:
--   §2 — graphs, orientations, the Boolean cube, Hamming distance to a trace and the signed Rademacher width
-- statement:
--   These definitions set up the one-inclusion analysis of the paper.
--
--   For a finite graph $G=(V,E)$ and $W\subseteq V$, $E_G(W)=\{e\in E:e\subseteq W\}$ is the set of edges inside $W$. An orientation chooses a head $\sigma(e)\in e$ for each edge, and its outdegree at $x$ is
--   $$\mathrm{out}(x;\sigma)=|\{e\in E:x\in e,\ \sigma(e)\ne x\}|.$$
--
--   Let $P$ be a finite coordinate set and $V_P=\{-1,+1\}^P$. For $v\in V_P$ and $p\in P$, $v^{\oplus p}$ is $v$ with coordinate $p$ flipped. The Boolean cube $G_P$ has vertex set $V_P$ and edges $\{v,v^{\oplus p}\}$. For $U\subseteq V_P$, $E_U$ is the set of cube edges inside $U$ and $D_U(v)=\{p\in P:v^{\oplus p}\in U\}$.
--
--   For $u,v\in V_P$, $\mathrm{DIS}(u,v)=\{p:u(p)\ne v(p)\}$. For nonempty $\mathcal F\subseteq V_P$, the Hamming distance from $v$ to $\mathcal F$ is $\rho_{\mathcal F}(v)=\min_{f\in\mathcal F}|\mathrm{DIS}(v,f)|$. For $D\subseteq P$, the unnormalized signed Rademacher width of the projection $\mathcal F|_D$ is
--   $$\mathfrak R_D(\mathcal F)=\mathbb E_\varepsilon\max_{f\in\mathcal F}\sum_{p\in D}\varepsilon_pf(p),$$
--   with $\varepsilon$ uniform on $\{-1,+1\}^P$.
--
--   These are the objects of the edge isoperimetric inequality and of the orientation theorem.
--
--   **Formalization Note** Labels are `Bool`, with `true` standing for $+1$, and `sgn` gives the signed value. Edges are elements of `Sym2`, so each edge is counted once. The expectation is the average over the finite cube. On an empty $\mathcal F$ the minimum and the maximum take the junk value $0$; every statement of the mission assumes $\mathcal F$ nonempty.
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §2, PDF pp. 3 and 6 (printed pp. 2 and 5)

import Mathlib
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- The sign map `Bool → ℝ`: `true` stands for the paper's label `+1`, `false` for `-1`. -/
noncomputable def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- `E_G(W) = {e ∈ E : e ⊆ W}`, the edges of the finite graph `G` with both endpoints in `W`
(PDF p. 6). Each edge is one element of `Sym2 V`, so it is counted once. -/
noncomputable def inducedEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (W : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ W)

/-- An orientation of `G` chooses a head `σ e ∈ e` for each edge `e` (PDF p. 6). The values of
`σ` off the edge set play no role. -/
def IsOrientation {V : Type*} (G : SimpleGraph V) (σ : Sym2 V → V) : Prop :=
  ∀ e ∈ G.edgeSet, σ e ∈ e

/-- `out(x; σ) = |{e ∈ E : x ∈ e, σ(e) ≠ x}|` (PDF p. 6). -/
noncomputable def outdegree {V : Type*} [Fintype V] (G : SimpleGraph V) (σ : Sym2 V → V)
    (x : V) : ℕ :=
  (G.edgeFinset.filter (fun e => x ∈ e ∧ σ e ≠ x)).card

/-- `v^{⊕p}`: the labeling `v` with coordinate `p` flipped (PDF p. 3). -/
noncomputable def flipAt {P : Type} (v : P → Bool) (p : P) : P → Bool :=
  Function.update v p (!v p)

theorem flipAt_flipAt {P : Type} (v : P → Bool) (p : P) : flipAt (flipAt v p) p = v := by
  funext r
  by_cases h : r = p
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

theorem flipAt_ne {P : Type} (v : P → Bool) (p : P) : v ≠ flipAt v p := by
  intro h
  have := congrFun h p
  simp [flipAt] at this

/-- The Boolean cube `G_P = (V_P, E_P)` with `V_P = {-1,+1}^P` and
`E_P = {{v, v^{⊕p}} : v ∈ V_P, p ∈ P}` (PDF p. 3). -/
noncomputable def cubeGraph (P : Type) : SimpleGraph (P → Bool) where
  Adj u v := ∃ p, v = flipAt u p
  symm := ⟨fun u v ⟨p, h⟩ => ⟨p, by rw [h, flipAt_flipAt]⟩⟩
  loopless := ⟨fun u ⟨p, h⟩ => flipAt_ne u p h⟩

/-- `D_U(v) = {p ∈ P : v^{⊕p} ∈ U}`, the directions from `v` to a neighbor in `U` (PDF p. 3).
`deg_U(v)` is its cardinality. -/
noncomputable def dirs {P : Type} [Fintype P] (U : Finset (P → Bool)) (v : P → Bool) : Finset P :=
  Finset.univ.filter (fun p => flipAt v p ∈ U)

/-- `DIS(u, v) = {p ∈ P : u(p) ≠ v(p)}` (PDF p. 3). -/
noncomputable def DIS {P : Type} [Fintype P] (u v : P → Bool) : Finset P :=
  Finset.univ.filter (fun p => u p ≠ v p)

/-- `ρ_F(v) = min_{f ∈ F} |DIS(v, f)|`, the Hamming distance from `v` to `F` (PDF p. 3). For
nonempty `F` the natural-number infimum is an attained minimum; on `F = ∅` it is the junk value
`0`, and every statement of this mission assumes `F` nonempty. -/
noncomputable def rho {P : Type} [Fintype P] (F : Set (P → Bool)) (v : P → Bool) : ℕ :=
  sInf ((fun f => (DIS v f).card) '' F)

/-- The unnormalized signed Rademacher width of the projection `F|_D` (PDF p. 3):
`R_D(F) = E_ε max_{f ∈ F} ∑_{p ∈ D} ε_p f(p)`, with `ε` uniform on `{-1,+1}^P`. The expectation
is the average over the finite cube. `F` is a subset of a finite type, so for nonempty `F` the
real supremum is an attained maximum; on `F = ∅` it is the junk value `0`, and every statement of
this mission assumes `F` nonempty. There is no absolute value and no division by `|D|`. -/
noncomputable def width {P : Type} [Fintype P] (F : Set (P → Bool)) (D : Finset P) : ℝ :=
  (Fintype.card (P → Bool) : ℝ)⁻¹ *
    ∑ ε : P → Bool, sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (ε p) * sgn (f p)) '' F)

end OptimalAgnosticPAC.Learner


