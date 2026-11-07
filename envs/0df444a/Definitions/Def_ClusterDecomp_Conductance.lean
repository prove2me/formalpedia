-- Prove2me | Definitions.Def_ClusterDecomp_Conductance
-- name    : ClusterDecomp_Conductance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:27.544195+00:00
-- url     : https://prove2.me/theorems/e2a592a6-4ddf-469f-9dde-de5009e52a5c
-- title:
--   Outer conductance $\phi_G$, conductance $\phi(G)$, $k$-way expansion $\rho_G(k)$, the degree-preserving subgraph $G\{S\}$, relative expansion
-- statement:
--   For a weighted graph $G$ and a set $S$ of positive volume, the outer conductance is $\phi_G(S)=w(S,V\setminus S)/\mathrm{vol}_G(S)$. The conductance and the $k$-way expansion are
--   $$\phi(G)=\min_{0<\mathrm{vol}(S)\le\mathrm{vol}(V)/2}\phi_G(S),\qquad \rho_G(k)=\min_{\substack{A_1,\dots,A_k\text{ pairwise disjoint}\\ \mathrm{vol}(A_i)>0}}\ \max_{1\le i\le k}\phi_G(A_i).$$
--   The degree-preserving induced subgraph $G\{S\}$ is $G[S]$ with a self-loop of weight $w(v,V\setminus S)$ added at each $v\in S$, so every vertex keeps its degree in $G$; the inner conductance of $S$ is $\phi(G\{S\})$. For $U\subseteq B$ with $0<\mathrm{vol}(U)<\mathrm{vol}(B)$, the relative expansion is
--   $$\varphi(U,B)=\frac{w(U,B\setminus U)}{\frac{\mathrm{vol}(B\setminus U)}{\mathrm{vol}(B)}\,w(U,V\setminus B)},$$
--   with $\varphi(U,B)=+\infty$ when $w(U,V\setminus B)=0$. The bundled hypotheses `Family` collect the assumptions of Theorem 1.1 on a graph: positive degrees, $k\ge2$, $0<\varepsilon\le1$, $p>0$, pairwise disjoint $A_i$ of positive volume with $\phi_G(A_i)\le p$, and $\rho_G(k+1)\ge(1+\varepsilon)p$.
--
--   These definitions state the bi-criteria guarantee of Oveis Gharan and Trevisan, and $G\{S\}$ rather than $G[S]$ is the object the paper's bounds concern.
--
--   **Formalization Note** $\phi$ and $\rho$ take values in $[0,\infty]$, with $+\infty$ on an empty family: a singleton $S$ for $\phi(G\{S\})$, and $k$ equal to the number of vertices for $\rho_G(k+1)$.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), §1, p.1 (PDF p.3); relative expansion, p.11 (PDF p.13); hypotheses of Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_ClusterDecomp_WGraph

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-!
# Conductance, k-way expansion, the degree-preserving subgraph

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), §1, p.1 (PDF p.3); relative expansion, §3.1, p.11 (PDF p.13).

**Formalization Note.**
* `phiOut` is a real quotient and is used only at positive volume.
* `phi` and `rho` are minima over families that can be empty: `ϕ(G{S})` for a singleton `S`, and
  `ρ_G(k+1)` when `k` equals the number of vertices. They take values in `ℝ≥0∞`, with the empty family
  giving `⊤`, so no bound on them is trivial and no hypothesis on them is unsatisfiable there.
* `degPres G S` is `G{S}`: its vertex type is `↥S`, and the loop at `v` is `w(v, v) + w(v, V ∖ S)`. Degrees and
  therefore volumes in `degPres G S` agree with those of `G`, so `phi (degPres G S)` is the inner conductance,
  not a formula with the degrees of `G[S]`.
* `relExp` is `φ(U, B)` with the printed convention `+∞` when `w(U, V ∖ B) = 0`, even if `w(U, B ∖ U) = 0`.
-/

namespace WGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V)

/-- The outer conductance `ϕ_G(S) = w(S, V ∖ S) / vol_G(S)` (p.1), used at positive volume. -/
noncomputable def phiOut (S : Finset V) : ℝ := G.cut S Sᶜ / G.vol S

/-- The conductance `ϕ(G) = min { ϕ_G(S) : 0 < vol(S) ≤ vol(V)/2 }` (p.1), with value `⊤` when no `S`
qualifies. -/
noncomputable def phi : ℝ≥0∞ :=
  ⨅ (S : Finset V) (_ : 0 < G.vol S ∧ G.vol S ≤ G.vol univ / 2), ENNReal.ofReal (G.phiOut S)

/-- The `j`-way expansion `ρ_G(j)` (p.1): the minimum, over `j` pairwise disjoint positive-volume sets, of
`max_i ϕ_G(A_i)`, with value `⊤` when no family exists. -/
noncomputable def rho (j : ℕ) : ℝ≥0∞ :=
  ⨅ (A : Fin j → Finset V) (_ : Pairwise fun a b => Disjoint (A a) (A b))
    (_ : ∀ i, 0 < G.vol (A i)), ⨆ i, ENNReal.ofReal (G.phiOut (A i))

/-- The degree-preserving induced subgraph `G{S}` (p.1): `G[S]` with a self-loop of weight `w(v, V ∖ S)` added
at each `v ∈ S`. -/
def degPres (S : Finset V) : WGraph ↥S where
  w u v := if u = v then G.w u v + G.cut {(u : V)} Sᶜ else G.w u v
  symm u v := by
    by_cases h : u = v
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]; exact G.symm _ _
  nonneg u v := by
    split_ifs
    · refine add_nonneg (G.nonneg _ _) ?_
      unfold cut cutCap
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => G.nonneg _ _
    · exact G.nonneg _ _

/-- The relative expansion (p.11): `φ(U, B) = w(U, B ∖ U) / ((vol(B ∖ U)/vol(B)) · w(U, V ∖ B))`, and `+∞` by
convention if `w(U, V ∖ B) = 0`. -/
noncomputable def relExp (U B : Finset V) : ℝ≥0∞ :=
  if G.cut U Bᶜ = 0 then ⊤
  else ENNReal.ofReal (G.cut U (B \ U) / (G.vol (B \ U) / G.vol B * G.cut U Bᶜ))

end WGraph

/-- The hypotheses of Theorem 1.1 (p.2) on a graph, apart from the integrality and polynomial ratio of the weights:
every vertex has positive degree (p.1), `k ≥ 2`, `0 < ε ≤ 1`, `p > 0`, the `A_i` are pairwise disjoint with positive
volume (hence nonempty) and `ϕ_G(A_i) ≤ p`, and `ρ_G(k+1) ≥ (1+ε)p`. -/
structure Family {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) (k : ℕ)
    (A : Fin k → Finset V) (ε p : ℝ) : Prop where
  posDeg : G.PosDeg
  two_le : 2 ≤ k
  ε_pos : 0 < ε
  ε_le : ε ≤ 1
  p_pos : 0 < p
  disjoint : Pairwise fun a b => Disjoint (A a) (A b)
  vol_pos : ∀ i, 0 < G.vol (A i)
  phi_le : ∀ i, G.phiOut (A i) ≤ p
  gap : ENNReal.ofReal ((1 + ε) * p) ≤ G.rho (k + 1)

end ClusterDecomp


