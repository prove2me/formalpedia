-- Prove2me | Definitions.Def_ApproxDegComp_mulOp
-- name    : ApproxDegComp_mulOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:37.847303+00:00
-- url     : https://prove2.me/theorems/3deb3ddd-d2ba-43a2-8f63-6ecbcd6e1ef4
-- title:
--   Multiplication operators $M_h$, $P_b=M_{\mathbf 1\{g=b\}}$ and $M_p$ on $\mathbb R^{\mathcal X}$
-- statement:
--   Let $\mathcal X\subseteq\{0,1\}^m$ be finite. For $h:\{0,1\}^m\to\mathbb R$, the **multiplication operator** $M_h$ on $\mathbb R^{\mathcal X}$ is the diagonal matrix with $(M_hv)_x=h(x)v_x$. Two instances are used:
--
--   1. for $g:\{0,1\}^m\to\{0,1\}$ and $b\in\{0,1\}$, the projector $P_b=M_{\mathbf 1\{g=b\}}$ onto the coordinates $x\in\mathcal X$ with $g(x)=b$;
--   2. for a real polynomial $p$ in $m$ variables, $M_p$, multiplication by the values of $p$ at the 0/1 points of $\mathcal X$.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), §2.1, p.10; Lemma 20, p.22

import Mathlib
import Definitions.Def_ApproxDegComp_cubePt

namespace ApproxDegComp

/-- **Diagonal multiplication operator** `M_h` on `ℝ^X` (§2.1, p.10; Lemma 20, p.22).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), §2.1, p.10: "We denote the diagonal multiplication operator associated with h by M_h, so
that (M_h v)_x = h(x) v_x."

**Formalization Note** `X` is a finite subset of `{0,1}^m` and `ℝ^X` has the coordinates
`x ∈ X` (the subtype of `X`). -/
def mulOp {m : ℕ} (X : Finset (Fin m → Bool)) (h : (Fin m → Bool) → ℝ) : Matrix X X ℝ :=
  Matrix.diagonal (fun x => h x.1)

/-- The projector `P_b = M_{1{g=b}}` on `ℝ^X` (Lemma 20, (10), p.22: "where P_b = M_{1{g=b}}"). -/
def pmat {m : ℕ} (g : (Fin m → Bool) → Bool) (X : Finset (Fin m → Bool)) (b : Bool) :
    Matrix X X ℝ :=
  mulOp X (fun x => if g x = b then 1 else 0)

/-- The multiplication operator `M_p` on `ℝ^X` by a real polynomial `p` in the `m` bits,
evaluated at the 0/1 points of `X` (Lemma 20, (9), p.22). -/
noncomputable def mpoly {m : ℕ} (X : Finset (Fin m → Bool)) (p : MvPolynomial (Fin m) ℝ) :
    Matrix X X ℝ :=
  mulOp X (fun x => MvPolynomial.eval (cubePt x) p)

end ApproxDegComp


