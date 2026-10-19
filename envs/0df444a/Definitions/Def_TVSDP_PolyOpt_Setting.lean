-- Prove2me | Definitions.Def_TVSDP_PolyOpt_Setting
-- name    : TVSDP_PolyOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:19.181306+00:00
-- url     : https://prove2.me/theorems/83f62b39-8499-45b6-b3ec-09ef8c72269c
-- title:
--   (1)–(3), pp. 1–3, Definition 2, p. 11 — time-varying SDP with polynomial data: $\mathbf L^n$, $\mathbf S^m$, the operator $\mathcal F$, feasibility, opt, strict feasibility
-- statement:
--   This file sets up the **time-varying semidefinite program (TV-SDP)** of Ahmadi and El Khadir with polynomial data.
--
--   **Function spaces.** $\mathbf L^n$ is the set of measurable functions $x:[0,1]\to\mathbb R^n$ that are bounded, $\sup_{t\in[0,1],\,i}|x_i(t)|<\infty$. $\mathbf S^m$ is the set of functions $X:[0,1]\to\mathbb R^{m\times m}$ with $X(t)$ symmetric for every $t\in[0,1]$ and $\sup_{t\in[0,1],\,i,j}|X_{ij}(t)|<\infty$.
--
--   **Data.** The data are polynomial: an objective $c=(c_1,\dots,c_n)$ of univariate polynomials, symmetric $m\times m$ matrices $A_0(t),A_1(t),\dots,A_n(t)$ whose entries are polynomials in $t$, and symmetric $m\times m$ kernels $D_1(t,s),\dots,D_n(t,s)$ whose entries are polynomials in $(t,s)$.
--
--   **The operator and the program.** For $x\in\mathbf L^n$,
--
--   $$\mathcal Fx(t) = A_0(t)+\sum_{i=1}^n x_i(t)A_i(t)+\sum_{i=1}^n\int_0^t x_i(s)\,D_i(t,s)\,ds .$$
--
--   A function $x$ is **feasible** if $x\in\mathbf L^n$ and $\mathcal Fx(t)\succeq 0$ for almost every $t\in[0,1]$. The objective is $\langle c,x\rangle_{\mathbf L^n}=\int_0^1\langle c(t),x(t)\rangle\,dt$, and the optimal value is
--
--   $$\mathrm{opt}=\sup\{\langle c,x\rangle_{\mathbf L^n} : x \text{ feasible}\}\in[-\infty,+\infty].$$
--
--   The TV-SDP is **strictly feasible** (Definition 2) if there are $x^s\in\mathbf L^n$ and $\varepsilon>0$ with $\mathcal Fx^s(t)\succeq\varepsilon I$ for almost every $t\in[0,1]$. Finally, a vector $p=(p_1,\dots,p_n)$ of polynomials defines the **polynomial solution** $t\mapsto(p_1(t),\dots,p_n(t))$.
--
--   These are the objects of Theorem 4 and of its proof.
--
--   **Formalization Note** Functions are total maps on $\mathbb R$ and only their values on $[0,1]$ matter; "almost every $t\in[0,1]$" is with respect to Lebesgue measure restricted to $[0,1]$. $\mathcal F$ is defined entrywise, with the kernel term an interval integral. The optimal value is an extended real (`EReal`), so that $\mathrm{opt}=+\infty$ is represented. Polynomial data is the paper's standing assumption (p. 3). The polynomial matrices are symmetric as polynomial matrices, which is equivalent to $A_i(t)$, $D_i(t,s)$ being symmetric for all $t,s$. The Loewner inequality $X\succeq\varepsilon I$ is written as positive semidefiniteness of $X-\varepsilon I$.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, pp. 1–2, (1)–(3) and the definitions of L^n, S^m, S^m+; p. 3 (polynomial data); p. 11, Definition 2

import Mathlib

namespace TVSDP.PolyOpt

open MeasureTheory

/-- The space `L^n` of p. 1: maps `x : [0,1] → ℝⁿ` that are measurable and bounded,
`sup_{t ∈ [0,1], i} |x_i(t)| < ∞`. The maps are total on `ℝ`; only their values on `[0,1]` matter.
The norm on `Fin n → ℝ` is the sup norm, i.e. `‖·‖_∞`. -/
def Ln (n : ℕ) : Set (ℝ → Fin n → ℝ) :=
  {x | Measurable x ∧ ∃ M : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, ‖x t‖ ≤ M}

/-- The space `S^m` of p. 2: matrix functions `X : [0,1] → ℝ^{m×m}` with `X(t)` symmetric for every
`t ∈ [0,1]` and `sup_{t ∈ [0,1], i, j} |X_{ij}(t)| < ∞`. -/
def Sm (m : ℕ) : Set (ℝ → Matrix (Fin m) (Fin m) ℝ) :=
  {X | (∀ t ∈ Set.Icc (0:ℝ) 1, (X t).IsSymm) ∧
    ∃ B : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ j k, |X t j k| ≤ B}

/-- The polynomial data of a TV-SDP (pp. 2–3): the objective `c = (c_1, …, c_n)`, the symmetric
matrices `A 0 = A_0, A 1 = A_1, …, A n = A_n` of polynomials in `t`, and the symmetric kernels
`D_1, …, D_n` (indexed by `Fin n`) of polynomials in two variables, variable `0` being `t`
and variable `1` being `s`. -/
structure Data (n m : ℕ) where
  c : Fin n → Polynomial ℝ
  A : Fin (n + 1) → Matrix (Fin m) (Fin m) (Polynomial ℝ)
  D : Fin n → Matrix (Fin m) (Fin m) (MvPolynomial (Fin 2) ℝ)
  A_symm : ∀ i, (A i).transpose = A i
  D_symm : ∀ i, (D i).transpose = D i

variable {n m : ℕ}

/-- The real matrix `A(t)` obtained by evaluating a polynomial matrix at `t`. -/
noncomputable def evalMat (A : Matrix (Fin m) (Fin m) (Polynomial ℝ)) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  A.map (Polynomial.eval t)

/-- The real matrix `D(t, s)` obtained by evaluating a matrix of bivariate polynomials at `(t, s)`. -/
noncomputable def evalMat₂ (D : Matrix (Fin m) (Fin m) (MvPolynomial (Fin 2) ℝ)) (t s : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  D.map (MvPolynomial.eval ![t, s])

/-- The operator `𝓕` of (2), entrywise:
`𝓕x(t) = A_0(t) + ∑ᵢ xᵢ(t) Aᵢ(t) + ∑ᵢ ∫₀ᵗ xᵢ(s) Dᵢ(t, s) ds`. -/
noncomputable def F (P : Data n m) (x : ℝ → Fin n → ℝ) (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k =>
    evalMat (P.A 0) t j k + ∑ i : Fin n, x t i * evalMat (P.A i.succ) t j k
      + ∑ i : Fin n, ∫ s in (0:ℝ)..t, x s i * evalMat₂ (P.D i) t s j k

/-- Feasibility (3): `x ∈ L^n` and `𝓕x(t) ⪰ 0` for almost every `t ∈ [0,1]`. -/
def Feasible (P : Data n m) (x : ℝ → Fin n → ℝ) : Prop :=
  x ∈ Ln n ∧ ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)), (F P x t).PosSemidef

/-- Definition 2 (p. 11): the TV-SDP is strictly feasible if some `xˢ ∈ L^n` and `ε > 0` satisfy
`𝓕xˢ(t) ⪰ εI` for almost every `t ∈ [0,1]`. -/
def StrictlyFeasible (P : Data n m) : Prop :=
  ∃ xs ∈ Ln n, ∃ ε : ℝ, 0 < ε ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      (F P xs t - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef

/-- The objective `⟨c, x⟩_{L^n} = ∫₀¹ ⟨c(t), x(t)⟩ dt` of (1). -/
noncomputable def obj (P : Data n m) (x : ℝ → Fin n → ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, ∑ i : Fin n, (P.c i).eval t * x t i

/-- The optimal value `opt` of (1): the supremum of the objective over the feasible set, in `EReal`
(it is `+∞` when the objective is unbounded above and `⊥` when there is no feasible solution). -/
noncomputable def opt (P : Data n m) : EReal :=
  ⨆ (x : ℝ → Fin n → ℝ) (_ : Feasible P x), ((obj P x : ℝ) : EReal)

/-- The solution `t ↦ (p_1(t), …, p_n(t))` given by a vector of polynomials. -/
noncomputable def polySol (p : Fin n → Polynomial ℝ) : ℝ → Fin n → ℝ :=
  fun t i => (p i).eval t

end TVSDP.PolyOpt


