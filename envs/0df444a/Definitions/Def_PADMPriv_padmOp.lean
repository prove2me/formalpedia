-- Prove2me | Definitions.Def_PADMPriv_padmOp
-- name    : PADMPriv_padmOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:57.694458+00:00
-- url     : https://prove2.me/theorems/9af459cb-0642-4475-92ce-98f8ef2f2bcd
-- title:
--   The PADM operator $T_F$ of (15)
-- statement:
--   Let $F:\mathbb R^p\to\mathbb R$, $g:\mathbb R^l\to\mathbb R$, $A\in\mathbb R^{m\times p}$, $B\in\mathbb R^{m\times l}$, $c\in\mathbb R^m$ and $\beta>0$. With the projection onto $W=\{(u,v): u+v=c\}$,
--   $\Pi_W(u,v) = \big(\tfrac12(u-v+c),\ \tfrac12(v-u+c)\big)$ (10), and $H=[I_m\ 0]$, the **PADM operator** is
--   $$
--   T_F(u) := H\cdot \Pi_W\begin{pmatrix} A\circ P_{\beta,F,A}(u)\\ B\circ P_{\beta,g,B}(c-u)\end{pmatrix}
--   = \frac12\Big(A\circ P_{\beta,F,A}(u) - B\circ P_{\beta,g,B}(c-u) + c\Big).
--   $$
--   Non-private PADM iterates $u^{(k)} = T_F(u^{(k-1)})$; the sample operator $T_{f_k}$ of the private method is $T_F$ with $F$ replaced by the loss $f_k$ of the $k$-th record.
--
--   **Formalization Note** Defined directly by the closed form on the right.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Eqs. (10) and (15), pp.6–7

import Mathlib
import Definitions.Def_PADMPriv_proxImage

namespace PADMPriv

/-- The PADM operator `T_F : ℝᵐ → ℝᵐ` of (15) in Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.7:
`T_F(u) = H · Π_W(A ∘ P_{β,F,A}(u), B ∘ P_{β,g,B}(c − u))`, which by the projection formula (10)
(`Π_W(u, v) = ((u − v + c)/2, (v − u + c)/2)`, p.6) and `H = [I_m 0]` equals
`T_F(u) = (A P_{β,F,A}(u) − B P_{β,g,B}(c − u) + c)/2`.
The sample operator `T_{f_k}` of (20) is `padmOp β f_k g A B c`.

**Formalization Note** Written directly in the closed form `(a − b + c)/2` of `H Π_W(a, b)`. -/
noncomputable def padmOp {m p l : ℕ} (β : ℝ) (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin l) → ℝ) (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  (1 / 2 : ℝ) • (proxImage β F A u - proxImage β g B (c - u) + c)

end PADMPriv


