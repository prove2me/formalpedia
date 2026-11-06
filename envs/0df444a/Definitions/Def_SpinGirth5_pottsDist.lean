-- Prove2me | Definitions.Def_SpinGirth5_pottsDist
-- name    : SpinGirth5_pottsDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:25.688203+00:00
-- url     : https://prove2.me/theorems/df4dafc8-f0e0-4b6c-9031-44c9e4aa16e6
-- title:
--   Antiferromagnetic Potts distribution $\mu_{G,q,\beta}$ and its interaction matrix $A=\mathbf 1\mathbf 1^\top-(1-\beta)I$
-- statement:
--   Fix an integer $q$, an edge activity $0\le\beta\le1$ and a graph $G=(V,E)$. The **antiferromagnetic Potts distribution** is
--   $$\mu_{G,q,\beta}(\sigma)=\frac{\beta^{|\{uv\in E:\ \sigma_u=\sigma_v\}|}}{\sum_{\tau\in[q]^V}\beta^{|\{uv\in E:\ \tau_u=\tau_v\}|}},\qquad\sigma\in[q]^V,$$
--   with the convention $0^0=1$. Each monochromatic edge contributes a factor $\beta$. At $\beta=1$ it is uniform on $[q]^V$; at $\beta=0$ it is uniform on proper $q$-colourings.
--
--   As a multi-spin system, the Potts model has interaction matrix $A=\mathbf 1\mathbf 1^{\top}-(1-\beta)I$ (diagonal entries $\beta$, off-diagonal entries $1$) and no external field ($\lambda=\mathbf 1$), so $B=(1-\beta)I$.
--
--   **Formalization Note** Lean's $(0:\mathbb R)^0=1$ is the paper's convention. Monochromatic edges are counted once, as unordered edges.
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §1, p.4; §6, pp.32–33

import Mathlib
import Definitions.Def_SpinGirth5_Interaction

namespace SpinGirth5

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number `|{uv ∈ E : σ_u = σ_v}|` of monochromatic edges of `σ`, each edge counted once. -/
def monoEdges (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (σ : V → Fin q) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ u ∈ e, ∀ w ∈ e, σ u = σ w)).card

/-- The Gibbs distribution `μ_{G,q,β}` of the **antiferromagnetic Potts model**:
`μ(σ) ∝ β^{|{uv∈E : σ_u = σ_v}|}` on `[q]^V`, with `0⁰ = 1`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, §1, p.4: "Fix an integer q ≥ 2 and an edge activity parameter
0 ≤ β ≤ 1. The Gibbs distribution µ = µG,q,β of the antiferromagnetic Potts model on G = (V, E)
is defined as µ(σ) ∝ β^{|{uv∈E:σu=σv}|}, σ ∈ [q]^V"; §6, pp.32–33 ("When β = 0, we use the
convention 0⁰ = 1").

**Formalization Note** Lean's `(0 : ℝ) ^ 0 = 1` is the paper's convention. At `β = 0` the
distribution is uniform on proper colourings, which exist when `q ≥ Δ + 1`; the normalizer is
then positive. -/
noncomputable def pottsDist (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (β : ℝ)
    (σ : V → Fin q) : ℝ :=
  β ^ monoEdges G σ / ∑ τ : V → Fin q, β ^ monoEdges G τ

/-- The Potts model as a multi-spin system: `A = 11ᵀ − (1 − β) I` (entries `β` on the diagonal,
`1` off it) and `λ = 1` (Chen, Liu, arXiv:2608.25491, §6, p.32: "The interaction matrix and its
deficit matrix are A = 11ᵀ − ϑI, B := 11ᵀ − A = ϑI", with `ϑ = 1 − β`; there is no external
field). -/
def pottsInteraction (q : ℕ) (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) : Interaction q where
  A := fun a b => if a = b then β else 1
  lam := fun _ => 1
  symm := fun a b => by
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  nonneg := fun a b => by
    by_cases h : a = b <;> simp [h, h0]
  le_one := fun a b => by
    by_cases h : a = b <;> simp [h, h1]
  lam_nonneg := fun _ => zero_le_one

end SpinGirth5


