-- Prove2me | Definitions.Def_ReflNewton_LocalQuad_Setting
-- name    : ReflNewton_LocalQuad_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:05.213158+00:00
-- url     : https://prove2.me/theorems/3da2a2b2-bb17-42c6-b259-7e057492996c
-- title:
--   Definition 1–2, (2.3)–(2.5), Fig. 6 and (6.3)–(6.4): local reflective Newton setting
-- statement:
--   Let $\mathcal F=\{x\in\mathbb R^n:l\le x\le u\}$ be a box with potentially infinite coordinate bounds, and let $f$ be twice continuously differentiable near it. The strict interior is defined coordinatewise by $l_i<x_i<u_i$. Write $g(x)=\nabla f(x)$ and $H(x)=\nabla^2 f(x)$.
--
--   Definition 2 selects a signed distance $v_i(x)$ according to the sign of $g_i(x)$: it is $x_i-u_i$ when $g_i<0$ and the upper bound is finite, $x_i-l_i$ when $g_i\ge0$ and the lower bound is finite, and respectively $-1$ or $1$ when the selected bound is infinite. Thus $D(x)=\operatorname{diag}(|v_i(x)|^{1/2})$. The free indices at $x_*$ satisfy $l_i<x_{*i}<u_i$. Nondegeneracy means $g_i(x_*)=0$ only at free indices; second-order sufficiency requires feasibility, $D(x_*)^2g(x_*)=0$, and positivity of the Hessian quadratic form on every nonzero direction supported on free indices.
--
--   The reflective map $R$ folds each real coordinate into its bound interval as in Fig. 6, and the path is $p_{x,d}(\alpha)=R(x+\alpha d)-x$. The local run of Fig. 11 solves $\widehat B(x)\widehat d=-D(x)g(x)$, takes $d=D(x)\widehat d$, chooses $\alpha$ with $|\alpha-1|\le\chi_\alpha\|D(x)^2g(x)\|$, and moves by $p_{x,d}(\alpha)$ to another interior point. The finite family $F_\nu(x)=\operatorname{diag}(\nu(x))g(x)$ uses the four choices of (6.4), restricted to choices valid at $x_*$.
--
--   These definitions distinguish the scaled Newton equation, the family used to analyze it, and the reflected update; each is reused by the local convergence statements.
--
--   **Formalization Note** Coordinates are indexed by $\mathrm{Fin}(n)$; the paper's $x_1$ is index zero. Infinite bounds are represented by extended reals, but all distance arithmetic is performed in $\mathbb R$ on finite branches. At a zero gradient, Definition 2 uses the nonnegative branch. The diagonal correction is $|g_i|$ when the selected bound is finite and zero otherwise, matching (2.5) after accounting for the sign of the literal Jacobian of $|v|$. The modulus in the finite-bound reflection uses fractional-part arithmetic. A coincident pair of bounds has empty strict interior, so no local run starts there. Fig. 11 prints the step-size rule as $|\alpha_k-1|=O(\|D_kg_k\|)$; the run uses $\|D(x)^2g(x)\|$ instead, because the printed rule does not give the quadratic rate of Theorem 13: on $[0,\infty)$ with $f(x)=x$, $x_*=0$, the Newton step is $d=-x$, $\|D(x)g(x)\|=\sqrt x$, and $\alpha=1-\chi_\alpha\sqrt x$ gives $x_+=\chi_\alpha x^{3/2}$. The paper's proof (p. 212) uses $|\alpha_k-1|=O(\|x_k-x_*\|)$, which the corrected rule supplies.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), pp. 189–194, 197–199, 211–212, problem (1.1), Definition 1, Definition 2, (2.3)–(2.5), Fig. 6, Fig. 11, (6.3)–(6.4)

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_FirstOrder_Setting

namespace ReflNewton.LocalQuad

noncomputable def hess {n : ℕ} (f : ReflNewton.FirstOrder.E n → ℝ) (x : ReflNewton.FirstOrder.E n) : ReflNewton.FirstOrder.E n →L[ℝ] ReflNewton.FirstOrder.E n :=
  fderiv ℝ (gradient f) x

def freeSet {n : ℕ} (l u : Fin n → EReal) (x : ReflNewton.FirstOrder.E n) : Set (Fin n) :=
  {i | l i < ((x i : ℝ) : EReal) ∧ ((x i : ℝ) : EReal) < u i}

noncomputable def IsNondegenerate {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (x : ReflNewton.FirstOrder.E n) : Prop :=
  ∀ i, gradient f x i = 0 → i ∈ freeSet l u x

noncomputable def SecondOrderSufficient {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (x : ReflNewton.FirstOrder.E n) : Prop :=
  x ∈ LewisTorczon.BoundPS.box l u ∧
  ReflNewton.FirstOrder.dSqG l u f x = 0 ∧
  ∀ w : ReflNewton.FirstOrder.E n, w ≠ 0 → (∀ i ∉ freeSet l u x, w i = 0) →
    0 < inner ℝ ((hess f x) w) w

noncomputable def finiteBound {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (x : ReflNewton.FirstOrder.E n) (i : Fin n) : Prop :=
  (gradient f x i < 0 ∧ u i ≠ ⊤) ∨ (0 ≤ gradient f x i ∧ l i ≠ ⊥)

/-- The diagonal of `diag(g) Jᵛ`, equivalently the corrected `Jᵛ Dᵍ` convention. -/
noncomputable def jvDg {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (x : ReflNewton.FirstOrder.E n) : ReflNewton.FirstOrder.E n := by
  classical
  exact WithLp.toLp 2 fun i => if finiteBound l u f x i then |gradient f x i| else 0

noncomputable def bHat {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (x dh : ReflNewton.FirstOrder.E n) : ReflNewton.FirstOrder.E n :=
  WithLp.toLp 2 fun i =>
    Real.sqrt |ReflNewton.FirstOrder.vVec l u f x i| *
      (hess f x (WithLp.toLp 2 fun j => Real.sqrt |ReflNewton.FirstOrder.vVec l u f x j| * dh j)) i +
    jvDg l u f x i * dh i

noncomputable def newtonEq {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (x d : ReflNewton.FirstOrder.E n) : Prop :=
  (WithLp.toLp 2 fun i => |ReflNewton.FirstOrder.vVec l u f x i| * (hess f x d) i + jvDg l u f x i * d i) =
    -ReflNewton.FirstOrder.dSqG l u f x

/-- Fig. 11 (p. 212), with the step-size rule `|α_k − 1| = O(‖D_k g_k‖)` corrected to
`|α_k − 1| ≤ χα ‖D_k² g_k‖`. As printed the rule is too weak for Theorem 13: on `[0, ∞)` with
`f(x) = x`, `x_* = 0`, the Newton step is `d = −x`, `‖D g‖ = √x`, and `α = 1 − χα √x` gives
`x₊ = χα x^{3/2}`, not quadratic. The proof (p. 212) uses `|α_k − 1| = O(‖x_k − x_*‖)` via the
claim `‖D_k g_k‖ = O(‖x_k − x_*‖)`, which fails there; `‖D_k² g_k‖ = O(‖x_k − x_*‖)` holds. -/
noncomputable def IsLocalNewtonRun {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (χα : ℝ) (x : ℕ → ReflNewton.FirstOrder.E n) (α : ℕ → ℝ) : Prop :=
  x 0 ∈ ReflNewton.FirstOrder.intBox l u ∧
  ∀ k, ∃ dh : ReflNewton.FirstOrder.E n,
    bHat l u f (x k) dh = -ReflNewton.FirstOrder.dG l u f (x k) ∧
    let d : ReflNewton.FirstOrder.E n := WithLp.toLp 2 fun i => Real.sqrt |ReflNewton.FirstOrder.vVec l u f (x k) i| * dh i
    |α k - 1| ≤ χα * ‖ReflNewton.FirstOrder.dSqG l u f (x k)‖ ∧
    x k + ReflNewton.FirstOrder.reflPath l u (x k) d (α k) ∈ ReflNewton.FirstOrder.intBox l u ∧
    x (k + 1) = x k + ReflNewton.FirstOrder.reflPath l u (x k) d (α k)

inductive NuChoice where
  | plus | minus | upper | lower
  deriving DecidableEq

instance : Fintype NuChoice :=
  ⟨{.plus, .minus, .upper, .lower}, by intro x; cases x <;> simp⟩

noncomputable def Admissible {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (xstar : ReflNewton.FirstOrder.E n) (c : Fin n → NuChoice) : Prop :=
  ∀ i,
    (gradient f xstar i = 0 →
      (c i = .upper → u i ≠ ⊤) ∧ (c i = .lower → l i ≠ ⊥)) ∧
    (gradient f xstar i < 0 → c i = .upper) ∧
    (0 < gradient f xstar i → c i = .lower)

noncomputable def nu {n : ℕ} (l u : Fin n → EReal)
    (c : Fin n → NuChoice) (x : ReflNewton.FirstOrder.E n) : ReflNewton.FirstOrder.E n :=
  WithLp.toLp 2 fun i =>
    match c i with
    | .plus => 1
    | .minus => -1
    | .upper => (u i).toReal - x i
    | .lower => x i - (l i).toReal

noncomputable def Fnu {n : ℕ} (l u : Fin n → EReal)
    (f : ReflNewton.FirstOrder.E n → ℝ) (c : Fin n → NuChoice) (x : ReflNewton.FirstOrder.E n) : ReflNewton.FirstOrder.E n :=
  WithLp.toLp 2 fun i => nu l u c x i * gradient f x i

end ReflNewton.LocalQuad


