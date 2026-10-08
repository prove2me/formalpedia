-- Prove2me | Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator
-- name    : DouglasRachfordPPA_GenDR_SplittingOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:03:38.701155+00:00
-- url     : https://prove2.me/theorems/580e3d0a-133c-4475-990c-060226ba6ea7
-- title:
--   The splitting operator $S_{\lambda,A,B}$, the set $Z^*_\lambda$ and the Douglas–Rachford map
-- statement:
--   Let $\mathcal H$ be a real inner product space, $\lambda\in\mathbb R$ (the paper takes $\lambda>0$), and let $A,B$ be operators on $\mathcal H$ (subsets of $\mathcal H\times\mathcal H$).
--
--   1. The **splitting operator** of $A$ and $B$ with respect to $\lambda$ is
--   $$S_{\lambda,A,B}=\{(v+\lambda b,\ u-v)\mid (u,b)\in B,\ (v,a)\in A,\ v+\lambda a=u-\lambda b\}.$$
--   2. The set
--   $$Z^*_\lambda=\{u+\lambda b\mid b\in Bu,\ -b\in Au\}.$$
--   3. Given maps $J_A,J_B:\mathcal H\to\mathcal H$ (in use, the single-valued resolvents $J_{\lambda A}$ and $J_{\lambda B}$), the **Douglas–Rachford map** is
--   $$G(z)=J_A\bigl(2J_B(z)-z\bigr)+\bigl(z-J_B(z)\bigr),$$
--   that is, $G_{\lambda,A,B}=J_{\lambda A}\circ(2J_{\lambda B}-I)+(I-J_{\lambda B})$.
--
--   The splitting operator is the operator whose proximal point iteration is Douglas–Rachford splitting; its zeros are $Z^*_\lambda$, and applying $J_{\lambda B}$ to a zero yields a zero of $A+B$.
--
--   **Formalization Note** $S_{\lambda,A,B}$ is defined by the explicit set formula of p. 16, not as $G^{-1}-I$, so that the identification $(I+S_{\lambda,A,B})^{-1}=G_{\lambda,A,B}$ is a theorem (Theorem 6) and not an unfolding. The Douglas–Rachford map takes the resolvent maps as arguments; $\lambda$ enters only through them. The paper's $\lambda$ is written `lam`.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 16 (G_{λ,A,B} and S_{λ,A,B}), p. 17 (Z*_λ, Theorem 5)

import Mathlib

open InnerProductSpace

namespace DouglasRachfordPPA.GenDR

/-- The splitting operator of `A` and `B` with respect to `lam` (Eckstein–Bertsekas, p. 16):
`S_{lam,A,B} = {(v + lam b, u - v) | (u, b) ∈ B, (v, a) ∈ A, v + lam a = u - lam b}`. -/
def splittingOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam : ℝ) (A B : H → Set H) : H → Set H :=
  fun w => {s | ∃ u b v a : H, b ∈ B u ∧ a ∈ A v ∧ v + lam • a = u - lam • b ∧
    w = v + lam • b ∧ s = u - v}

/-- The set `Z*_lam = {u + lam b | b ∈ B u, -b ∈ A u}` (Theorem 5, p. 17). -/
def Zstar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam : ℝ) (A B : H → Set H) : Set H :=
  {z | ∃ u b : H, b ∈ B u ∧ -b ∈ A u ∧ z = u + lam • b}

/-- The Douglas–Rachford map `G = J_{lam A} ∘ (2 J_{lam B} - I) + (I - J_{lam B})` (p. 16),
built from given single-valued resolvent maps `JA`, `JB`. -/
def drMap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (JA JB : H → H) : H → H :=
  fun z => JA ((2 : ℝ) • JB z - z) + (z - JB z)

end DouglasRachfordPPA.GenDR


