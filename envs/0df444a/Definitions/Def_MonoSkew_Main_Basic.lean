-- Prove2me | Definitions.Def_MonoSkew_Main_Basic
-- name    : MonoSkew_Main_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:22.424473+00:00
-- url     : https://prove2.me/theorems/d3178b7c-841c-4aad-bd5b-59adf2e0b45f
-- title:
--   Problems 1.1 and 1.2: the primal and dual inclusions, $\mathcal P$, $\mathcal D$, $M$ and $S$ on $\mathcal H\oplus\mathcal G$, uniform monotonicity at a point, and the iterations (2.3), (3.1)
-- statement:
--   Let $\mathcal H$ and $\mathcal G$ be real Hilbert spaces, let $A:\mathcal H\to2^{\mathcal H}$ and $B:\mathcal G\to2^{\mathcal G}$ be set-valued operators, let $L:\mathcal H\to\mathcal G$ be a bounded linear operator with adjoint $L^*$, and let $z\in\mathcal H$, $r\in\mathcal G$. A set-valued operator $M$ has graph $\operatorname{gra}M=\{(x,u)\mid u\in Mx\}$ and inverse $M^{-1}$ with graph $\{(u,x)\mid u\in Mx\}$. This file fixes the objects of Problems 1.1 and 1.2 of Briceño-Arias and Combettes.
--
--   1. The **primal operator** is $x\mapsto Ax+L^*B(Lx-r)=\{a+L^*w\mid a\in Ax,\ w\in B(Lx-r)\}$, and the **primal solution set** is
--   $$\mathcal P=\{x\in\mathcal H\mid z\in Ax+L^*B(Lx-r)\}.\qquad(1.2)$$
--   2. The **dual operator** is $v\mapsto -LA^{-1}(z-L^*v)+B^{-1}v=\{-Ly+t\mid y\in A^{-1}(z-L^*v),\ t\in B^{-1}v\}$, and the **dual solution set** is
--   $$\mathcal D=\{v\in\mathcal G\mid -r\in -LA^{-1}(z-L^*v)+B^{-1}v\}.\qquad(1.3)$$
--   3. $\mathcal K=\mathcal H\oplus\mathcal G$ is the Hilbert direct sum, with inner product $\langle (x,v)\mid(x',v')\rangle=\langle x\mid x'\rangle+\langle v\mid v'\rangle$. On it,
--   $$M:(x,v)\mapsto(-z+Ax)\times(r+B^{-1}v),\qquad S:(x,v)\mapsto(L^*v,-Lx).\qquad(1.8)$$
--   For a set-valued $T$ and a single-valued $C$, $(T+C)x=\{u+Cx\mid u\in Tx\}$.
--   4. $M$ is **uniformly monotone at $x$** if there is an increasing function $\phi:[0,+\infty[\to[0,+\infty]$ that vanishes only at $0$ such that
--   $$(\forall u\in Mx)(\forall (y,v)\in\operatorname{gra}M)\quad \langle x-y\mid u-v\rangle\ge\phi(\|x-y\|).$$
--   5. $w$ is a **sequential weak cluster point** of $(x_n)_{n\in\mathbb N}$ if some subsequence of $(x_n)$ converges weakly to $w$.
--   6. A **run of the inexact forward–backward–forward iteration** (2.3), for a single-valued $B$, step sizes $\gamma_n$, maps $J_n$ (to be resolvents of $\gamma_nA$) and error sequences $a_n,b_n,c_n$, is a family of sequences with, for every $n\in\mathbb N$,
--   $$y_n=x_n-\gamma_n(Bx_n+a_n),\quad p_n=J_ny_n+b_n,\quad q_n=p_n-\gamma_n(Bp_n+c_n),\quad x_{n+1}=x_n-y_n+q_n.$$
--   7. A **run of the primal–dual iteration** (3.1), for step sizes $\gamma_n$, maps $J^A_n$ and $J^{B^{-1}}_n$ (to be the resolvents of $\gamma_nA$ and $\gamma_nB^{-1}$) and error sequences $a_{i,n},b_{i,n},c_{i,n}$, is a family of sequences with, for every $n\in\mathbb N$,
--   $$\begin{aligned}y_{1,n}&=x_n-\gamma_n(L^*v_n+a_{1,n}), & y_{2,n}&=v_n+\gamma_n(Lx_n+a_{2,n}),\\ p_{1,n}&=J^A_n(y_{1,n}+\gamma_nz)+b_{1,n}, & p_{2,n}&=J^{B^{-1}}_n(y_{2,n}-\gamma_nr)+b_{2,n},\\ q_{1,n}&=p_{1,n}-\gamma_n(L^*p_{2,n}+c_{1,n}), & q_{2,n}&=p_{2,n}+\gamma_n(Lp_{1,n}+c_{2,n}),\\ x_{n+1}&=x_n-y_{1,n}+q_{1,n}, & v_{n+1}&=v_n-y_{2,n}+q_{2,n}.\end{aligned}$$
--
--   These objects are shared by every statement of the mission: Problem 1.1 is the pair of inclusions (1.2)–(1.3), Problem 1.2 is the inclusion $0\in Mx+Sx$ on $\mathcal K$, and Theorems 2.5 and 3.1 are about the two iterations.
--
--   **Formalization Note** Set-valued operators are maps `E → Set E`; the inverse $M^{-1}$ and the sum $A+B$ of two set-valued operators are the published `opInv` and `opAdd`, and monotonicity, maximal monotonicity, `zer`, resolvents and weak convergence are the published `ThreeOpSplitting.Convergence` notions. $\mathcal K$ is `WithLp 2 (H × G)` (the plain product `H × G` carries the sup norm). $\phi$ is a map $\mathbb R_{\ge0}\to[0,+\infty]$ (`ℝ≥0 → ℝ≥0∞`), "increasing" is read as nondecreasing (the convention of the authors' reference [6]), and the inequality is compared in `EReal`, since $\phi$ may take the value $+\infty$. The run predicates leave the initial points free and take the resolvents as given maps; the theorems constrain them by the resolvent property. Indices start at $0$.
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, pp. 2–5, 10, Problem 1.1 (1.2)–(1.3), Problem 1.2 (1.8), notation p. 4, Lemma 2.4(i), iterations (2.3) and (3.1)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

namespace MonoSkew.Main

open InnerProductSpace NNReal ENNReal
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-! Briceño-Arias and Combettes, *A Monotone+Skew Splitting Model for Composite Monotone
Inclusions in Duality*, arXiv:1011.5517v1, Problems 1.1 and 1.2 (pp. 2–3), notation (p. 4),
Lemma 2.4(i) (p. 4), iterations (2.3) (p. 5) and (3.1) (p. 10).

Set-valued operators `M : E → 2^E` are maps `E → Set E` with graph `{(x, u) | u ∈ M x}`.
Monotonicity, maximal monotonicity, `zer`, resolvents (`IsResolvent`), weak convergence
(`WeakTendsto`), the inverse `opInv` and the sum `opAdd` are the published notions. -/

section Problem

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The composite term `x ↦ L*(B(Lx − r)) = {L*w | w ∈ B(Lx − r)}` of (1.2). -/
noncomputable def compositeOp (B : G → Set G) (L : H →L[ℝ] G) (r : G) : H → Set H :=
  fun x => {u | ∃ w ∈ B (L x - r), u = ContinuousLinearMap.adjoint L w}

/-- The primal operator `A + L* ∘ B ∘ (L · − r)` of (1.2) and Proposition 2.8(ii). -/
noncomputable def primalOp (A : H → Set H) (B : G → Set G) (L : H →L[ℝ] G) (r : G) :
    H → Set H :=
  opAdd A (compositeOp B L r)

/-- The dual operator `−L ∘ A⁻¹ ∘ (z − L*·) + B⁻¹` of (1.3) and Proposition 2.8(vi):
`v ↦ {−Ly + t | y ∈ A⁻¹(z − L*v), t ∈ B⁻¹v}`. -/
noncomputable def dualOp (A : H → Set H) (B : G → Set G) (L : H →L[ℝ] G) (z : H) :
    G → Set G :=
  fun v => {w | ∃ y ∈ opInv A (z - ContinuousLinearMap.adjoint L v),
                ∃ t ∈ opInv B v, w = -(L y) + t}

/-- `𝒫` (Problem 1.1): the set of solutions of the primal inclusion (1.2),
`z ∈ Ax + L*B(Lx − r)`. -/
noncomputable def primalSet (A : H → Set H) (B : G → Set G) (L : H →L[ℝ] G) (z : H) (r : G) :
    Set H :=
  {x | z ∈ primalOp A B L r x}

/-- `𝒟` (Problem 1.1): the set of solutions of the dual inclusion (1.3),
`−r ∈ −LA⁻¹(z − L*v) + B⁻¹v`. -/
noncomputable def dualSet (A : H → Set H) (B : G → Set G) (L : H →L[ℝ] G) (z : H) (r : G) :
    Set G :=
  {v | -r ∈ dualOp A B L z v}

end Problem

/-- `𝒦 = ℋ ⊕ 𝒢`, the Hilbert direct sum, with inner product `⟨x, x'⟩ + ⟨v, v'⟩`
(`WithLp 2`, not the sup-normed product). -/
abbrev K (H G : Type*) := WithLp 2 (H × G)

section Problem2

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The operator `M` of (1.8): `(x, v) ↦ (−z + Ax) × (r + B⁻¹v)`. -/
def opM (A : H → Set H) (B : G → Set G) (z : H) (r : G) : K H G → Set (K H G) :=
  fun p => {w | w.fst + z ∈ A p.fst ∧ w.snd - r ∈ opInv B p.snd}

/-- The operator `S` of (1.8): `(x, v) ↦ (L*v, −Lx)`. -/
noncomputable def opS (L : H →L[ℝ] G) : K H G → K H G :=
  fun p => WithLp.toLp 2 (ContinuousLinearMap.adjoint L p.snd, -(L p.fst))

end Problem2

/-- The sum of a set-valued operator `T` and a single-valued operator `C`:
`(T + C)x = {u + Cx | u ∈ Tx}`. -/
def addSingle {E : Type*} [Add E] (T : E → Set E) (C : E → E) : E → Set E :=
  fun x => {w | ∃ u ∈ T x, w = u + C x}

/-- `M` is uniformly monotone at `x` (Lemma 2.4(i)): there is an increasing (nondecreasing)
`φ : [0, +∞[ → [0, +∞]` vanishing only at `0` such that `⟨x − y | u − v⟩ ≥ φ(‖x − y‖)` for every
`u ∈ Mx` and every `(y, v) ∈ gra M`. The comparison is made in `EReal`. -/
def IsUniformlyMonotoneAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E → Set E) (x : E) : Prop :=
  ∃ φ : ℝ≥0 → ℝ≥0∞, Monotone φ ∧ (∀ t, φ t = 0 ↔ t = 0) ∧
    ∀ u ∈ M x, ∀ y v, v ∈ M y →
      ((φ ‖x - y‖₊ : ℝ≥0∞) : EReal) ≤ ((⟪x - y, u - v⟫_ℝ : ℝ) : EReal)

/-- `w` is a sequential weak cluster point of `(x_n)`: some subsequence of `(x_n)` converges
weakly to `w`. -/
def IsSeqWeakClusterPt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℕ → E) (w : E) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakTendsto (x ∘ φ) w

/-- A run of the inexact forward–backward–forward iteration (2.3) (Theorem 2.5), where
`J n` is a resolvent of `γ_n A` supplied separately (`IsResolvent (γ n) A (J n)`):
`y_n = x_n − γ_n(Bx_n + a_n)`, `p_n = J_{γ_n A} y_n + b_n`, `q_n = p_n − γ_n(Bp_n + c_n)`,
`x_{n+1} = x_n − y_n + q_n`. The initial point `x 0` is free. -/
def IsFBFRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E → E) (γ : ℕ → ℝ) (J : ℕ → E → E) (a b c x y p q : ℕ → E) : Prop :=
  ∀ n, y n = x n - γ n • (B (x n) + a n) ∧ p n = J n (y n) + b n ∧
    q n = p n - γ n • (B (p n) + c n) ∧ x (n + 1) = x n - y n + q n

section Run

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- A run of the primal–dual iteration (3.1) (Theorem 3.1), where `JA n` is a resolvent of
`γ_n A` and `JBinv n` a resolvent of `γ_n B⁻¹`, supplied separately. The initial points
`x 0`, `v 0` are free. -/
def IsPDRun (L : H →L[ℝ] G) (z : H) (r : G) (γ : ℕ → ℝ)
    (JA : ℕ → H → H) (JBinv : ℕ → G → G)
    (a₁ b₁ c₁ : ℕ → H) (a₂ b₂ c₂ : ℕ → G)
    (x y₁ p₁ q₁ : ℕ → H) (v y₂ p₂ q₂ : ℕ → G) : Prop :=
  ∀ n,
    y₁ n = x n - γ n • (ContinuousLinearMap.adjoint L (v n) + a₁ n) ∧
    y₂ n = v n + γ n • (L (x n) + a₂ n) ∧
    p₁ n = JA n (y₁ n + γ n • z) + b₁ n ∧
    p₂ n = JBinv n (y₂ n - γ n • r) + b₂ n ∧
    q₁ n = p₁ n - γ n • (ContinuousLinearMap.adjoint L (p₂ n) + c₁ n) ∧
    q₂ n = p₂ n + γ n • (L (p₁ n) + c₂ n) ∧
    x (n + 1) = x n - y₁ n + q₁ n ∧
    v (n + 1) = v n - y₂ n + q₂ n

end Run

end MonoSkew.Main


