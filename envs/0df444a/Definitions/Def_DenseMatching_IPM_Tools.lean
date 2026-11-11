-- Prove2me | Definitions.Def_DenseMatching_IPM_Tools
-- name    : DenseMatching_IPM_Tools
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:39:18.65965+00:00
-- url     : https://prove2.me/theorems/ca91a81d-eff1-4eb0-842b-7d177197a00c
-- title:
--   §2–§3 — independent edge sampling, spectral approximation ≈_ε, the centered retention variable, and unit-weight degrees, volumes and cuts
-- statement:
--   Objects of §2.2, §2.3 and §3, on the published weighted graphs `EffResSparsify.Sampling.WGraph` (incidence matrix $B$, Laplacian $L(G)=B^\top W B$, Moore–Penrose pseudoinverse $L(G)^\dagger$, effective resistance $R^{\mathrm{eff}}(G)_e=\chi_e^\top L(G)^\dagger\chi_e$).
--
--   - **Independent sampling.** For $p\in[0,1]^E$, `sampleProb p A` is the probability of the event $A$ when every $e\in E$ is retained independently with probability $p_e$:
--   $$\Pr[A]=\sum_{\omega\in\{0,1\}^E}\mathbf 1[A(\omega)]\prod_{e}\big(p_e\ \text{if}\ \omega_e,\ 1-p_e\ \text{otherwise}\big).$$
--   - **Sampled graph** (Lemma 2.3). On the outcome $\omega$, $H$ keeps the retained edges with weight $w_e/p_e$; `sampledLaplacian G p ω` $=L(H)=B^\top\mathrm{Diag}(w')B$ with $w'_e=w_e/p_e$ if $\omega_e$, else $0$.
--   - **Spectral approximation** (§2.2, p. 8). $M\approx_\varepsilon N$ iff $(1-\varepsilon)N\preceq M\preceq(1+\varepsilon)N$ in the Loewner order (both differences positive semidefinite).
--   - **Centered retention variable** (p. 9). For intensity $\varrho>0$ and $p=1-e^{-\varrho}$, $\zeta=1/p-1$ with probability $p$ and $\zeta=-1$ otherwise; `retentionLaw ϱ` is its law $p\,\delta_{1/p-1}+(1-p)\,\delta_{-1}$.
--   - **Unit-weight multigraph quantities** (§3, Lemma 3.5): `UnitMultigraph V E` is a finite multigraph given by the two endpoints of every edge (parallel edges and loops allowed); $\deg_G(u)$ = number of edge ends at $u$ (a loop counts twice); $\mathrm{Vol}_G(S)=\sum_{u\in S}\deg_G(u)$; $|E_G(S,V\setminus S)|$ = number of edges with exactly one endpoint in $S$; $x^\top D(G)x=\sum_u\deg_G(u)x_u^2$; $x^\top L(G)x=\sum_e(x_{\mathrm{head}(e)}-x_{\mathrm{tail}(e)})^2$, the quadratic form of $L(G)=D(G)-A(G)$.
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), pp. 8–9, §2.2–§2.3; p. 20, Lemma 3.5

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace DenseMatching.IPM

open EffResSparsify.Sampling Matrix

/-!
# Tools of §2 and §3: independent edge sampling, the centered retention variable, degrees,
volumes and cuts of a multigraph, and spectral approximation

Dai, Peng, Sleator, Stepin, Yang, *Approaching Optimality for Dense Bipartite Matching*, STOC 2027
submission (manuscript sha256 0bdeb447…), pp. 8–10 and 20. Weighted graphs, the incidence matrix,
the Laplacian `L(G) = B⊤WB`, its Moore–Penrose pseudoinverse and the effective resistance are the
published `EffResSparsify.Sampling.WGraph` objects. The unit-weight multigraphs of Lemma 3.5 (loops
allowed) are `UnitMultigraph`.
-/

open Classical in
/-- The probability that an event `A` holds when every element `e` of the finite set `E` is
retained independently with probability `p e` (the outcome `ω` records which are retained):
`∑_ω 1[A ω] ∏_e (p_e if ω e, else 1 − p_e)`. For `p ∈ [0, 1]^E` this is the product of the
Bernoulli(`p_e`) laws. -/
noncomputable def sampleProb {E : Type*} [Fintype E] (p : E → ℝ) (A : (E → Bool) → Prop) : ℝ :=
  ∑ ω : E → Bool, if A ω then ∏ e, (if ω e then p e else 1 - p e) else 0

/-- The graph `H` of Lemma 2.3 on the outcome `ω`: every retained edge `e` of `G` gets weight
`w_e / p_e`, every other edge weight `0`. This is its Laplacian `L(H) = B⊤ Diag(w') B`. -/
noncomputable def sampledLaplacian {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : WGraph V E) (p : E → ℝ) (ω : E → Bool) : Matrix V V ℝ :=
  G.incidenceᵀ * Matrix.diagonal (fun e => if ω e then G.w e / p e else 0) * G.incidence

/-- Spectral approximation `M ≈_ε N` of symmetric matrices (§2.2, p. 8):
`(1 − ε) N ⪯ M ⪯ (1 + ε) N` in the Loewner order. -/
def LoewnerApprox {V : Type*} [Fintype V] (ε : ℝ) (M N : Matrix V V ℝ) : Prop :=
  (M - (1 - ε) • N).PosSemidef ∧ ((1 + ε) • N - M).PosSemidef

/-- The retention probability `p = 1 − e^{−ϱ}` of intensity `ϱ` (p. 9). -/
noncomputable def retentionProb (ϱ : ℝ) : ℝ := 1 - Real.exp (-ϱ)

/-- The law of the centered retention variable `ζ` of intensity `ϱ > 0` (p. 9): `ζ = 1/p − 1` with
probability `p = 1 − e^{−ϱ}` and `ζ = −1` otherwise, so that `E[ζ] = 0`. -/
noncomputable def retentionLaw (ϱ : ℝ) : MeasureTheory.Measure ℝ :=
  ENNReal.ofReal (retentionProb ϱ) • MeasureTheory.Measure.dirac (1 / retentionProb ϱ - 1) +
    ENNReal.ofReal (1 - retentionProb ϱ) • MeasureTheory.Measure.dirac (-1)

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A finite multigraph with unit weights `G = (V_G, E_G, 1)` (Lemma 3.5, p. 20): every edge `e`
has two endpoints `head e` and `tail e`. Parallel edges are allowed, and so are loops
(`head e = tail e`). -/
structure UnitMultigraph (V E : Type*) where
  /-- one endpoint of the edge `e` -/
  head : E → V
  /-- the other endpoint of the edge `e` -/
  tail : E → V

/-- The degree `deg_G(u)` of a vertex of a unit-weight multigraph: the number of edge ends at `u`
(an edge with endpoints `u ≠ v` counts once at each, a loop at `u` counts twice). -/
def unitDegree (G : UnitMultigraph V E) (u : V) : ℕ :=
  (Finset.univ.filter (fun e => G.head e = u)).card +
    (Finset.univ.filter (fun e => G.tail e = u)).card

/-- The volume `Vol_G(S) = ∑_{u ∈ S} deg_G(u)` with unit edge weights. -/
def unitVolume (G : UnitMultigraph V E) (S : Finset V) : ℕ := ∑ u ∈ S, unitDegree G u

/-- The number `|E_G(S, V \ S)|` of edges with exactly one endpoint in `S`. -/
def cutSize (G : UnitMultigraph V E) (S : Finset V) : ℕ :=
  (Finset.univ.filter (fun e => (G.head e ∈ S ∧ G.tail e ∉ S) ∨ (G.head e ∉ S ∧ G.tail e ∈ S))).card

/-- The quadratic form `x⊤ D(G) x = ∑_u deg_G(u) x_u²` of the degree diagonal (unit weights). -/
def degreeQuad (G : UnitMultigraph V E) (x : V → ℝ) : ℝ := ∑ u, (unitDegree G u : ℝ) * x u ^ 2

/-- The Laplacian quadratic form `x⊤ L(G) x = ∑_{e} (x_{head e} − x_{tail e})²` of the Laplacian
`L(G) = D(G) − A(G)` (`A(G)_{uv}` the number of edges joining `u` and `v`, a loop counted twice in
`A(G)_{uu}`, so that a loop contributes `0`). -/
def lapQuad (G : UnitMultigraph V E) (x : V → ℝ) : ℝ := ∑ e, (x (G.head e) - x (G.tail e)) ^ 2

end DenseMatching.IPM


