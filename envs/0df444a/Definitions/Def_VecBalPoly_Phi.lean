-- Prove2me | Definitions.Def_VecBalPoly_Phi
-- name    : VecBalPoly_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:15:27.924222+00:00
-- url     : https://prove2.me/theorems/784c99ae-539f-429e-9c8b-fd833ebbc21c
-- title:
--   The spectral potential $\Phi=(L-1)_+^3-\eta\|x\|_2^2$ and its derivatives
-- statement:
--   The spectral potential of a state is
--   $$\Phi=(L-1)_+^3-\eta\|x\|_2^2,\qquad t_+=\max\{t,0\}.$$
--   As a function of the coloring $y$, with $V,T_i,c_i,r_i$ fixed, it is $\Phi(y)$; its first derivative $\langle\nabla\Phi,h\rangle$ and second derivative $h^{\mathsf T}\nabla^2\Phi h$ along a direction $h$ at the state's coloring, the gradient $\nabla\Phi\in\mathbb R^V$ and the Hessian $\nabla^2\Phi$ on $\mathbb R^V$ are taken in that sense.
--
--   The cubic term penalizes $L>1$ and the quadratic term rewards progress toward signs.
--
--   **Formalization Note** $\|x\|_2$ runs over all $n$ coordinates, as the proofs require. Derivatives are Fréchet derivatives on $\mathbb R^n$, applied to directions supported on $V$; the gradient and Hessian are their entries in the active coordinates.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), (2.7), p.5 (PDF p.6); §2.4, p.5; Appendix D.1, p.15

import Mathlib
import Definitions.Def_VecBalPoly_L

namespace VecBalPoly

variable {m n : ℕ}

/-- **The spectral potential (2.7)** `Φ = (L − 1)³₊ − η‖x‖₂²`, `t₊ = max{t, 0}`.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.3, (2.7), p.5 (PDF p.6).

**Formalization Note** `‖x‖₂` is over all `n` coordinates (frozen ones included): the proofs use
`‖x‖₂² ≤ n` (p.12) and "the quadratic term is unchanged at fixed x" across freezing (p.13). -/
noncomputable def Phi (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : ℝ :=
  (max (L A st - 1) 0) ^ 3 - eta n * ∑ j, st.x j ^ 2

/-- `Φ` as a function of the coloring `y`, with `V, Tᵢ, cᵢ, rᵢ` fixed.
Source: ibid., §2.4, p.5 (PDF p.6): "When taking derivatives, we keep V, Ti, ci, and ri fixed." -/
noncomputable def phiAt (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (y : Fin n → ℝ) : ℝ :=
  Phi A { st with x := y }

/-- **The first derivative `⟨∇Φ, h⟩`** of `Φ` at the state's coloring along `h`
(`V, Tᵢ, cᵢ, rᵢ` fixed). Source: ibid., Lemma 2.1, p.6; Appendix D, p.15.

**Formalization Note** The Fréchet derivative of `phiAt` on `ℝⁿ`; the statements apply it to
directions `h` supported on `V`, which is the gradient in the active coordinates. -/
noncomputable def dPhi (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (h : Fin n → ℝ) : ℝ :=
  fderiv ℝ (phiAt A st) st.x h

/-- **The second derivative `hᵀ∇²Φh`** of `Φ` at the state's coloring along `h`
(`V, Tᵢ, cᵢ, rᵢ` fixed). Source: ibid., Lemma 2.1, p.6; Proposition 4.5, p.10. -/
noncomputable def d2Phi (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (h : Fin n → ℝ) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ (phiAt A st) y h) st.x h

/-- **The gradient `∇Φ ∈ ℝ^V`**: the partial derivatives in the active coordinates, zero off `V`.
Source: ibid., Appendix D.1, p.15 (PDF p.16). -/
noncomputable def gradPhi (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : Fin n → ℝ :=
  fun j => if j ∈ st.V then dPhi A st (Pi.single j 1) else 0

/-- **The Hessian `∇²Φ` on `ℝ^V`**: the second partial derivatives in the active coordinates,
zero outside `V × V`. Source: ibid., Appendix D.1, p.15 (PDF p.16). -/
noncomputable def hessPhi (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j k => if j ∈ st.V ∧ k ∈ st.V then
    fderiv ℝ (fun y => fderiv ℝ (phiAt A st) y (Pi.single k 1)) st.x (Pi.single j 1) else 0

end VecBalPoly


