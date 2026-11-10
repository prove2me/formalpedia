-- Prove2me | Definitions.Def_BorderDiffEq_ABP
-- name    : BorderDiffEq_ABP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:14.519195+00:00
-- url     : https://prove2.me/theorems/b7923308-81a0-47ab-90b5-690320d5558b
-- title:
--   Algebraic branching programs (Definition 4.8)
-- statement:
--   An **algebraic branching program** (ABP) over a field $K$ is a layered directed acyclic graph with layers $V_0,\dots,V_q$ ($q\ge1$), where $V_0=\{s\}$ is a source and $V_q=\{t\}$ a sink. Every edge $e$ goes from a layer $V_{i-1}$ to $V_i$ and carries an affine linear label $W(e)\in K[x]$. The ABP computes
--   $$
--   f=\sum_{\gamma}\prod_{e\in\gamma}W(e),
--   $$
--   the sum over all paths $\gamma$ from $s$ to $t$. Its **depth** is $q$, its width $\max_i|V_i|$, and its **size** is the number of vertices $\sum_i|V_i|$.
--
--   ABPs are the target model of the mission's debordering theorem.
--
--   **Formalization Note** Layer $i$ is `Fin (w i)` with `w 0 = 1` and `w q = 1`. The edges between consecutive layers form a matrix of affine forms; a zero label is a missing edge. Labels are affine over the ABP's own field $K$, so neither polynomial labels of high degree nor labels involving $\varepsilon$ are allowed.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Definition 4.8, p.27

import Mathlib
import Definitions.Def_BorderDiffEq_AffineForm

namespace BorderDiffEq

/-- **Algebraic branching programs** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission),
Definition 4.8, p.27): a layered directed acyclic graph with layers `V₀, …, V_q`, `V₀ = {s}` a
source and `V_q = {t}` a sink; every edge goes from `V_{i-1}` to `V_i` and is labelled by an affine
linear polynomial over `K`. The ABP computes the sum over all source–sink paths of the product of
the labels; its size is the number of vertices.

**Formalization Note.** Layer `i` is `Fin (w i)`, with `w 0 = 1` and `w q = 1`, and `q ≥ 1` (source
and sink are distinct layers). The edges between layers `i` and `i+1` are a matrix `L i` of affine
forms; a zero label is a missing edge. Labels are affine over the ABP's own field `K`. -/
structure ABP (K : Type) (σ : Type) where
  /-- the depth `q` -/
  q : ℕ
  one_le_q : 1 ≤ q
  /-- the number of vertices in each layer -/
  w : Fin (q + 1) → ℕ
  source_layer : w 0 = 1
  sink_layer : w (Fin.last q) = 1
  /-- the edge labels between consecutive layers -/
  L : (i : Fin q) → Matrix (Fin (w i.castSucc)) (Fin (w i.succ)) (AffineForm K σ)

namespace ABP

variable {K σ : Type}

/-- The polynomial computed: the sum, over all choices of one vertex per layer (all of which are
source–sink paths, since the first and last layers are singletons), of the product of the edge
labels along the path. -/
noncomputable def eval [CommRing K] [Fintype σ] (A : ABP K σ) : MvPolynomial σ K :=
  ∑ p : (i : Fin (A.q + 1)) → Fin (A.w i), ∏ e : Fin A.q, (A.L e (p e.castSucc) (p e.succ)).toPoly

/-- The size: the number of vertices `∑ᵢ |Vᵢ|`. -/
def size (A : ABP K σ) : ℕ := ∑ i, A.w i

end ABP

end BorderDiffEq


