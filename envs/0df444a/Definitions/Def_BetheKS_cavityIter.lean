-- Prove2me | Definitions.Def_BetheKS_cavityIter
-- name    : BetheKS_cavityIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:11.166715+00:00
-- url     : https://prove2.me/theorems/52e6a99e-b5c0-4ad0-8b55-05908a392af2
-- title:
--   Cavity iteration $(\Gamma_u^{(v)})^{(M)}$ and cavity weights $\Gamma_u^{(v)}$
-- statement:
--   On a locally finite graph $G$ (finite or infinite), with $t\ge\sqrt d>1$ and $\delta>0$, set $c_\delta:=t/(t^2+\delta)$ and, for every directed edge $(u,v)$,
--   $$
--   (\Gamma_u^{(v)})^{(0)}:=0,\qquad (\Gamma_u^{(v)})^{(M+1)}:=\frac{t}{t^2+\deg(u)-1+\delta-t\sum_{w\sim u,\,w\ne v}(\Gamma_w^{(u)})^{(M)}}\qquad(3.1).
--   $$
--   The **cavity weight** is $\Gamma_u^{(v)}:=\lim_{M\to\infty}(\Gamma_u^{(v)})^{(M)}$ (Definition 3.3); the limit exists by Lemma 3.2, the iteration being nondecreasing and bounded by $c_\delta$. These are the Green's-function weights $t\langle e_u,(H(t,T^{(v)}_u)+\delta I)^{-1}e_u\rangle$ of the branch at $u$ away from $v$.
--
--   **Formalization Note** Defined for every ordered pair of vertices, on any `SimpleGraph` with finite neighbourhoods.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), §3, p.6; Definition 3.1, (3.1), p.7; Definition 3.3, p.7

import Mathlib

set_option autoImplicit false

open Filter

namespace BetheKS

variable {V : Type} [DecidableEq V]

/-- `c_δ := t/(t² + δ)` (§3, p.6). -/
noncomputable def cDelta (t δ : ℝ) : ℝ := t / (t ^ 2 + δ)

/-- **The cavity iteration `(Γ_u^{(v)})^{(M)}`** — Dong, McKenzie, arXiv:2610.41802 (held version,
sha256 4da41e16…), Definition 3.1, p.7 (PDF p.8), (3.1): on a graph `G` (finite or infinite),
`(Γ_u^{(v)})^{(0)} := 0` and
`(Γ_u^{(v)})^{(M+1)} := t / (t² + deg(u) − 1 + δ − t ∑_{w∼u, w≠v} (Γ_w^{(u)})^{(M)})`.

**Formalization Note.** `cavIter G t δ M u v` is `(Γ_u^{(v)})^{(M)}`. It is defined for every pair
`(u, v)`; the paper uses directed edges `u ∼ v`. Graphs are locally finite (degrees are finite), as
the paper's degrees require. -/
noncomputable def cavIter (G : SimpleGraph V) [G.LocallyFinite] (t δ : ℝ) : ℕ → V → V → ℝ
  | 0, _, _ => 0
  | M + 1, u, v => t / (t ^ 2 + (G.degree u : ℝ) - 1 + δ -
      t * ∑ w ∈ (G.neighborFinset u).erase v, cavIter G t δ M w u)

/-- **The cavity weight `Γ_u^{(v)} := lim_{M→∞} (Γ_u^{(v)})^{(M)}`** (Definition 3.3, p.7).
The limit exists by Lemma 3.2 (monotone and bounded by `c_δ`). -/
noncomputable def cav (G : SimpleGraph V) [G.LocallyFinite] (t δ : ℝ) (u v : V) : ℝ :=
  limUnder atTop (fun M => cavIter G t δ M u v)

end BetheKS


