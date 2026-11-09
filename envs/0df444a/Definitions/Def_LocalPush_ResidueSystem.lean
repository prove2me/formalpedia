-- Prove2me | Definitions.Def_LocalPush_ResidueSystem
-- name    : LocalPush_ResidueSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:28.622226+00:00
-- url     : https://prove2.me/theorems/fbea0a0f-d4a9-4ff7-a528-174d452dc998
-- title:
--   Residue $r(x)=e_s-\frac1\alpha L_\alpha x$, restricted matrix $L_{\alpha,S}$, exact state $x^{(S)}$, objective $\psi_\lambda$
-- statement:
--   Fix a seed $s$, $\alpha\in(0,1)$ and an internal threshold $\lambda$.
--
--   1. The residue of $x\in\mathbb R^V$ is $r(x):=e_s-\frac1\alpha L_\alpha x$ (eq. (8)).
--   2. For $S\subseteq V$, $L_{\alpha,S}:=D_S-(1-\alpha)A_S$ is the principal submatrix of $L_\alpha$ indexed by $S$.
--   3. For $S\ni s$, the exact state $x^{(S)}\in\mathbb R^V$ is
--   $$x^{(S)}_S:=\alpha L_{\alpha,S}^{-1}\big(e_s|_S-\lambda d_S\big),\qquad x^{(S)}_{V\setminus S}:=0.\tag{11}$$
--   4. The $\ell_1$-regularized PageRank objective with $\rho=\lambda$ is
--   $$\psi_\lambda(x)=\tfrac12x^\top L_\alpha x-\alpha x(s)+\alpha\lambda\sum_{v}d(v)|x(v)|,$$
--   which is eq. (18) on $x\ge0$.
--
--   The exact state $x^{(S)}$ is the limit of infinitely many pushes inside $S$, and $\psi_\lambda$ is the potential whose decrease bounds the number of expansions.
--
--   **Formalization Note** Vectors on $S$ are functions on the subtype $S$; `restr` restricts and `ext` extends by zero. The Lean identifier `lam` is the paper's $\lambda$. The inverse $L_{\alpha,S}^{-1}$ exists for $\alpha\in(0,1)$ on a graph without isolated nodes, which every statement assumes.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §4, p.14 (PDF p.14); eq. (8), p.16; eq. (11), p.17; eq. (2), p.5; eq. (18), p.20

import Mathlib
import Definitions.Def_LocalPush_GraphMatrices

open Finset Matrix

namespace LocalPush

/-!
# The residue map `r(x)`, the restricted system `L_{α,S}`, the exact state `x^(S)` and the objective `ψ_λ`

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…): `L_{α,S}`, §4, p.14 (PDF p.14);
eq. (8), p.16; eq. (11), p.17; eq. (2), p.5, and eq. (18), p.20.

* (8): `r(x) := e_s − (1/α) L_α x`.
* §4: `L_{α,S} := D_S − (1 − α)A_S`, the principal submatrix of `L_α` indexed by `S`.
* (11): for a set `S` containing `s`, `x^(S)_S := α L_{α,S}⁻¹ (e_s|_S − λ d_S)` and `x^(S)_{V∖S} := 0`.
* (2) with `ρ = λ`: `ψ_λ(x) := ½ xᵀ(D − (1 − α)A)x − α e_sᵀx + αλ‖Dx‖₁`; on `x ≥ 0` this is (18).

**Formalization Note.**
* Vectors on `S` are functions on the subtype `S`; `restr S x` is `x|_S` and `ext S y` extends `y` by zero.
* `bvec G s α lam S` is the right-hand side `α(e_s|_S − λ d_S)` of line 6 of Algorithm 3, and
  `xS G s α lam S = ext S (L_{α,S}⁻¹ bvec)`. The Lean identifier `lam` stands for the paper's `λ` (a keyword
  in Lean).
* The inverse `L_{α,S}⁻¹` is a genuine inverse for `α ∈ (0, 1)` on a graph without isolated nodes
  (`L_{α,S} ⪰ αD_S ≻ 0`, §A.2, p.55); every statement of the mission assumes both.
* `‖Dx‖₁ = ∑_v d(v)|x(v)|` since degrees are nonnegative.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `L_{α,S} := D_S − (1 − α)A_S`, the principal submatrix of `L_α` indexed by `S` (§4, p.14). -/
def LαS (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (S : Finset V) : Matrix S S ℝ :=
  (Lα G α).submatrix Subtype.val Subtype.val

/-- The restriction `x|_S` of a vector to `S`. -/
def restr (S : Finset V) (x : V → ℝ) : S → ℝ :=
  fun v => x v

/-- The extension of a vector on `S` by zero outside `S`. -/
def ext (S : Finset V) (y : S → ℝ) : V → ℝ :=
  fun v => if h : v ∈ S then y ⟨v, h⟩ else 0

/-- The residue `r(x) := e_s − (1/α) L_α x` (eq. (8), p.16). -/
noncomputable def resid (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (s : V) (x : V → ℝ) : V → ℝ :=
  e s - α⁻¹ • (Lα G α *ᵥ x)

/-- The right-hand side `α(e_s|_S − λ d_S)` of the restricted system (line 6 of Algorithm 3, p.18). -/
noncomputable def bvec (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ) (S : Finset V) :
    S → ℝ :=
  α • fun v : S => e s v - lam * deg G v

/-- The exact state `x^(S)` of eq. (11), p.17: `α L_{α,S}⁻¹(e_s|_S − λ d_S)` on `S`, zero outside `S`. -/
noncomputable def xS (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ) (S : Finset V) :
    V → ℝ :=
  ext S ((LαS G α S)⁻¹ *ᵥ bvec G s α lam S)

/-- The `ℓ₁`-regularized PageRank objective `ψ_λ(x) = ½ xᵀL_α x − α x(s) + αλ ∑_v d(v)|x(v)|`
(eq. (2), p.5, with `ρ = λ`; eq. (18), p.20, on `x ≥ 0`). -/
noncomputable def psi (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ) (x : V → ℝ) : ℝ :=
  (1 / 2) * (x ⬝ᵥ (Lα G α *ᵥ x)) - α * x s + α * lam * ∑ v, deg G v * |x v|

end LocalPush


