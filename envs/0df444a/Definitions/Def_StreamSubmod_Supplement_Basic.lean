-- Prove2me | Definitions.Def_StreamSubmod_Supplement_Basic
-- name    : StreamSubmod_Supplement_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:42:15.356398+00:00
-- url     : https://prove2.me/theorems/d31e2789-1a3e-5112-9d89-c578e5838e97
-- title:
--   Indicator vectors, support, $\ell_1$-norm and the partial derivative $\partial_eF$ of the multilinear extension
-- statement:
--   Let $V$ be a finite ground set and $f:2^V\to\mathbb R$. For a vector $x\in\mathbb R^V$ this module defines:
--
--   1. the indicator vector $\mathbf 1_S$ of a set $S\subseteq V$, with $(\mathbf 1_S)_e=1$ for $e\in S$ and $0$ otherwise;
--   2. the support $\operatorname{supp}(x)=\{e\in V\mid x_e>0\}$;
--   3. the norm $\|x\|_1=\sum_{e\in V}x_e$, the sum of the coordinates of $x$ (the paper's usage for non-negative vectors);
--   4. the partial derivative of the multilinear extension $F$ of $f$,
--
--   $$
--   \partial_eF(x)=F(x\vee\mathbf 1_e)-F\bigl(x\wedge\mathbf 1_{V\setminus\{e\}}\bigr),
--   $$
--
--   where $\vee$ and $\wedge$ are the coordinate-wise maximum and minimum.
--
--   These are the quantities in which Algorithm 3 and its analysis are written.
--
--   **Formalization Note** $F$ is the published multilinear extension $F(x)=\sum_{A\subseteq V}f(A)\prod_{e\in A}x_e\prod_{e\notin A}(1-x_e)$, evaluated exactly by this sum; this models the value oracle for $F$ that Appendix C assumes.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, §2, p.5 (basic notation) and p.6 (multilinear extension, ∂_eF); Appendix C, p.22 (supp, ‖x‖₁)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The indicator vector `𝟏_S ∈ {0,1}^V` of a set `S ⊆ V` (Alaluf, Ene, Feldman, Nguyen & Suh, An
Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint,
arXiv:1911.12959v3, §2, "Basic notation", p.5). -/
noncomputable def ind (S : Finset E) : E → ℝ := fun e => if e ∈ S then 1 else 0

/-- The support `supp(x) = {e ∈ V | x_e > 0}` of a vector `x` (arXiv:1911.12959v3, Appendix C,
p.22). -/
noncomputable def supp (x : E → ℝ) : Finset E := Finset.univ.filter fun e => 0 < x e

/-- The `ℓ₁`-norm `‖x‖₁`, which Appendix C uses as "the sum of the coordinates of `x`"
(arXiv:1911.12959v3, Appendix C, p.22). -/
noncomputable def l1 (x : E → ℝ) : ℝ := ∑ e, x e

/-- The partial derivative `∂_eF(x) = F(x ∨ 𝟏_e) − F(x ∧ 𝟏_{V∖{e}})` of the multilinear extension
`F` of `f` (arXiv:1911.12959v3, §2, p.6), where `∨` and `∧` are the coordinate-wise maximum and
minimum (§2, p.5).

**Formalization Note.** `F` is the published multilinear extension
`NonmonotoneSubmod.Shared.F`, `F(x) = Σ_{A ⊆ V} f(A) Π_{e∈A} x_e Π_{e∉A} (1 − x_e)`, evaluated
exactly: this is the value oracle for `F` that Appendix C assumes (p.21). -/
noncomputable def partialDeriv (f : Finset E → ℝ) (x : E → ℝ) (e : E) : ℝ :=
  F f (fun i => max (x i) (ind {e} i)) - F f (fun i => min (x i) (ind (Finset.univ \ {e}) i))

end StreamSubmod.Supplement


