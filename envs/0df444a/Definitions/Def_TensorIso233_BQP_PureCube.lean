-- Prove2me | Definitions.Def_TensorIso233_BQP_PureCube
-- name    : TensorIso233_BQP_PureCube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:17.013459+00:00
-- url     : https://prove2.me/theorems/c73c8f5e-2827-4848-b17a-224f2b4cd5c3
-- title:
--   The canonical flag of a nilpotent operator, adapted pairs (5.6), and the linear system (5.14)–(5.17)
-- statement:
--   For $D\in\mathrm{Mat}_3(\mathbb Q)$ set (5.5)
--
--   $$
--   F_1(D)=\operatorname{im}D\cap\ker D,\qquad F_2(D)=\operatorname{im}D+\ker D .
--   $$
--
--   The standard basis is **adapted** to the flag of $D$ when $F_1(D)=\langle e_1\rangle$ and $F_2(D)=\langle e_1,e_2\rangle$. A pair is of **shape (5.6)** when
--
--   $$
--   A=\begin{pmatrix}a&p&r\\0&d&q\\0&0&c\end{pmatrix},\quad B=\begin{pmatrix}0&e&h\\0&0&g\\0&0&0\end{pmatrix},\qquad a,d,c>0,
--   $$
--
--   and it is an **adapted pair** when moreover the standard bases are adapted to the flags of both $D=A^{-1}B$ and $E=BA^{-1}$.
--
--   For two pairs of shape (5.6) with the same $a,d,c,e,g$ (primed entries $p',q',r',h'$ for the second), the unknowns $\xi=(u,x,v,y,t)^{\mathsf T}$ satisfy the system (5.14) $K\xi=b$ with
--
--   $$
--   K=\begin{pmatrix}d&-a&0&0&e\\0&0&c&-d&g\\g&0&0&-e&0\end{pmatrix},\qquad b=\begin{pmatrix}p'-p\\q'-q\\h'-h\end{pmatrix}.
--   $$
--
--   For a solution $\xi_0$, (5.15) is $r_1=r+ht_0+qu_0+gu_0t_0-p'y_0$; on $L=\ker_{\mathbb Z}K$, (5.16) is $\Psi(\xi)=h't+q'u-p'y+gut$; and for a family $\ell_1,\dots,\ell_m$, (5.17) is $\eta=\gcd(\rho,\Psi(\ell_1),\dots,\Psi(\ell_m))$ with $\rho=\gcd(a,c)$. The pairs are **unitriangularly equivalent** when $P(A+tB)=A'Q$ and $PB=B'Q$ for some $t\in\mathbb Z$ and upper unitriangular $P,Q\in\mathrm{Mat}_3(\mathbb Z)$ (p. 23).
--
--   These objects reduce the pure-cube comparison to one linear system and one congruence.
--
--   **Formalization Note** Adaptedness is the flag condition, not the matrix shape: shape (5.6) alone does not force the flags (for $D=E_{12}$, $F_2(D)=\langle e_1,e_3\rangle$).
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), §5.2, pp. 19–21, (5.5)–(5.6); §5.3, pp. 22–24, (5.9), (5.14)–(5.17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_Tensor

/-!
# Pure cubes: the canonical flag, adapted pairs, and the linear system of §5.3

Thomas Huffstutler, *Integral 2 × 3 × 3 Tensor Isomorphism is in BQP*, STOC 2027 submission #319
(October 2026), §5.2 (pp. 19–22), §5.3 (pp. 22–25).
-/

namespace TensorIso233.BQP

/-- (5.5), p. 19: `F₁(D) = im D ∩ ker D ⊆ ℚ³`. -/
noncomputable def F1 (D : Matrix (Fin 3) (Fin 3) ℚ) : Submodule ℚ (Fin 3 → ℚ) :=
  LinearMap.range D.mulVecLin ⊓ LinearMap.ker D.mulVecLin

/-- (5.5), p. 19: `F₂(D) = im D + ker D ⊆ ℚ³`. -/
noncomputable def F2 (D : Matrix (Fin 3) (Fin 3) ℚ) : Submodule ℚ (Fin 3 → ℚ) :=
  LinearMap.range D.mulVecLin ⊔ LinearMap.ker D.mulVecLin

/-- The standard basis vector `e₁ ∈ ℚ³`. -/
def e1 : Fin 3 → ℚ := Pi.single 0 1

/-- The standard basis vector `e₂ ∈ ℚ³`. -/
def e2 : Fin 3 → ℚ := Pi.single 1 1

/-- p. 20: the standard basis is adapted to the flag of `D`:
`F₁(D) = ⟨e₁⟩` and `F₂(D) = ⟨e₁, e₂⟩`. -/
def HasStdFlags (D : Matrix (Fin 3) (Fin 3) ℚ) : Prop :=
  F1 D = Submodule.span ℚ {e1} ∧ F2 D = Submodule.span ℚ {e1, e2}

/-- (5.6), p. 21: `A = (a p r; 0 d q; 0 0 c)` with `a, d, c > 0` and
`B = (0 e h; 0 0 g; 0 0 0)`. -/
def IsShape56 (T : Tensor) : Prop :=
  T.1 1 0 = 0 ∧ T.1 2 0 = 0 ∧ T.1 2 1 = 0 ∧ 0 < T.1 0 0 ∧ 0 < T.1 1 1 ∧ 0 < T.1 2 2 ∧
  T.2 0 0 = 0 ∧ T.2 1 0 = 0 ∧ T.2 1 1 = 0 ∧ T.2 2 0 = 0 ∧ T.2 2 1 = 0 ∧ T.2 2 2 = 0

/-- Lemma 5.3, p. 21: an adapted pair: of the shape (5.6), with the standard bases adapted to
the flags of both `D = A⁻¹B` and `E = BA⁻¹`. -/
def IsAdapted (T : Tensor) : Prop :=
  IsShape56 T ∧ HasStdFlags (opD T) ∧ HasStdFlags (opE T)

/-- The pair (5.6) with the given entries. -/
def shape56 (a p r d q c e h g : ℤ) : Tensor :=
  (!![a, p, r; 0, d, q; 0, 0, c], !![0, e, h; 0, 0, g; 0, 0, 0])

/-- (5.9), p. 24: `P` is upper unitriangular. -/
def IsUnitUpper (P : Mat3) : Prop :=
  P 0 0 = 1 ∧ P 1 1 = 1 ∧ P 2 2 = 1 ∧ P 1 0 = 0 ∧ P 2 0 = 0 ∧ P 2 1 = 0

/-- p. 23: after the sign choice and relabelling, the pairs `(A, B)` and `(A', B')` are
equivalent by upper-unitriangular changes of basis and an integral shear:
`P(A + tB) = A'Q` and `PB = B'Q` for some `t ∈ ℤ` and upper unitriangular `P, Q ∈ Mat₃(ℤ)`. -/
def UnitriEquiv (T T' : Tensor) : Prop :=
  ∃ t : ℤ, ∃ P Q : Mat3, IsUnitUpper P ∧ IsUnitUpper Q ∧
    P * (T.1 + t • T.2) = T'.1 * Q ∧ P * T.2 = T'.2 * Q

/-- (5.14), p. 24: the coefficient matrix
`K = (d −a 0 0 e; 0 0 c −d g; g 0 0 −e 0)` acting on `ξ = (u, x, v, y, t)ᵀ`. -/
def Kmat (a d c e g : ℤ) : Matrix (Fin 3) (Fin 5) ℤ :=
  !![d, -a, 0, 0, e; 0, 0, c, -d, g; g, 0, 0, -e, 0]

/-- (5.14), p. 24: the right-hand side `b = (p' − p, q' − q, h' − h)ᵀ`. -/
def bvec (p q h p' q' h' : ℤ) : Fin 3 → ℤ := ![p' - p, q' - q, h' - h]

/-- (5.15), p. 24: `r₁ = r + h t₀ + q u₀ + g u₀ t₀ − p' y₀` for `ξ₀ = (u₀, x₀, v₀, y₀, t₀)ᵀ`. -/
def r1 (r h q g p' : ℤ) (ξ : Fin 5 → ℤ) : ℤ :=
  r + h * ξ 4 + q * ξ 0 + g * ξ 0 * ξ 4 - p' * ξ 3

/-- (5.16), p. 24: `Ψ(ξ) = h' t + q' u − p' y + g u t` for `ξ = (u, x, v, y, t)ᵀ`. -/
def Psi (h' q' p' g : ℤ) (ξ : Fin 5 → ℤ) : ℤ :=
  h' * ξ 4 + q' * ξ 0 - p' * ξ 3 + g * ξ 0 * ξ 4

/-- (5.17), p. 24: `η = gcd(ρ, Ψ(ℓ₁), …, Ψ(ℓₘ))` with `ρ = gcd(a, c)`, for a finite family
`ℓ₁, …, ℓₘ` of vectors (for `m = 0`, `η = ρ`). -/
def eta (a c h' q' p' g : ℤ) {m : ℕ} (ℓ : Fin m → Fin 5 → ℤ) : ℕ :=
  Int.gcd (Int.gcd a c : ℤ) (Finset.univ.gcd fun i => Psi h' q' p' g (ℓ i))

/-- `L = ker_ℤ K ⊆ ℤ⁵`. -/
def kerZ (a d c e g : ℤ) : Submodule ℤ (Fin 5 → ℤ) :=
  LinearMap.ker (Matrix.mulVecLin (Kmat a d c e g))

end TensorIso233.BQP


