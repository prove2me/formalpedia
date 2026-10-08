-- Prove2me | Definitions.Def_BregmanPPA_ProxMult_Saddle
-- name    : BregmanPPA_ProxMult_Saddle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:55.803739+00:00
-- url     : https://prove2.me/theorems/173919f4-6d6d-4b2b-b880-741a9917ef5d
-- title:
--   §5 — the Lagrangian l, saddle pairs, the saddle operator K on ℝⁿ⁺ᵐ, h_x ⊕ h_p, and runs of recursion (12)
-- statement:
--   For problem (10) (see the `Program` definitions), the **Lagrangian** of §5 is
--
--   $$l(x,p)=\begin{cases} f(x)+\sum_{i=1}^m p_i g_i(x), & x\in C,\ p\in\overline{\Omega^+},\\ -\infty, & x\in C,\ p\notin\overline{\Omega^+},\\ +\infty, & x\notin C.\end{cases}$$
--
--   A pair $(x^*,p^*)\in\mathbb R^n\times\mathbb R^m$ is a **saddle pair** if $l(x^*,p)\le l(x^*,p^*)\le l(x,p^*)$ for all $x\in\mathbb R^n$, $p\in\mathbb R^m$; the paper identifies these with the optimal solution–Lagrange multiplier pairs of (10) (p. 220).
--
--   $\partial_x l(x,p)$ is the set of subgradients of the convex function $l(\cdot,p)$ at $x$, and $\hat\partial_p l(x,p)$ the set of supergradients of the concave function $l(x,\cdot)$ at $p$: the $v$ with $l(x,p)>-\infty$ and $l(x,q)\le l(x,p)+\langle v,q-p\rangle$ for all $q$. On $\mathbb R^{n+m}=\mathbb R^n\times\mathbb R^m$ with the Euclidean inner product $\langle(x,p),(y,q)\rangle=\langle x,y\rangle+\langle p,q\rangle$, the **saddle operator** is
--
--   $$K(x,p)=\partial_x l(x,p)\times\big(-\hat\partial_p l(x,p)\big).$$
--
--   For Bregman functions $h_x$ on $\mathbb R^n$ and $h_p$ on $\mathbb R^m$, $h=h_x\oplus h_p$ is $h(x,p)=h_x(x)+h_p(p)$, with candidate zone $S_x\times S_p$.
--
--   Finally, for positive scalars $c_k$, a sequence $\{(x^k,p^k)\}_{k\ge0}$ **conforms to the recursions (12)** if $x^0\in S_x$, every $p^k\in S_p$, and for every $k\ge0$, $x^{k+1}\in C$ minimizes over $C$
--
--   $$f(x)+\frac1{c_k}h_p^{*+}\big(\nabla h_p(p^k)+c_k g(x)\big)+\frac1{c_k}D_{h_x}(x,x^k),$$
--
--   and $p^{k+1}=\nabla h_p^{*+}\big(\nabla h_p(p^k)+c_kg(x^{k+1})\big)$.
--
--   These definitions carry Theorem 8: (12) is the Bregman proximal point algorithm applied to $K$ with $h=h_x\oplus h_p$.
--
--   **Formalization Note** $\mathbb R^{n+m}$ is `WithLp 2 (E n × E m)` (not the sup-norm product). Subgradients and supergradients use the published `IsSubgradient`; a supergradient $v$ of $l(x,\cdot)$ at $p$ is a subgradient $-v$ of $-l(x,\cdot)$. At $x\in C$, $p\notin\overline{\Omega^+}$, the improper function $l(\cdot,p)$ equals $-\infty$ at $x$ and every vector satisfies the subgradient inequality, but $\hat\partial_p l(x,p)=\emptyset$ there, so $K(x,p)=\emptyset$ off $C\times\overline{\Omega^+}$, as in the paper. The paper writes $x^{k+1}=\arg\min$, unique by strict convexity of $D_{h_x}(\cdot,x^k)$ (p. 222); a minimality predicate is equivalent. $h_p^{*+}$ is used through `toReal` both in the objective and in its gradient; Lemma 3 (a milestone) proves $h_p^{*+}$ finite and differentiable everywhere, so this is exact. The run requires $x^0\in S_x$ (not $x^0\in C$) and $p^k\in S_p$, so that $\nabla h_x(x^0)$, $D_{h_x}(\cdot,x^0)$ and $\nabla h_p(p^k)$ are defined; these are implicit in "conforms to the recursions".
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 220–222, §5 (Lagrangian l, operator K), Theorem 8 recursion (12), proof of Theorem 8 (h = h_x ⊕ h_p), https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program

open InertialFB.IFB

namespace BregmanPPA.ProxMult

/-- The Lagrangian `l` of problem (10), §5 (p. 220):
`l(x, p) = f(x) + Σᵢ pᵢ gᵢ(x)` for `x ∈ C, p ∈ Ω̄⁺`; `l(x, p) = -∞` for `x ∈ C, p ∉ Ω̄⁺`;
`l(x, p) = +∞` for `x ∉ C`. (On `C` every `gᵢ` is finite, so `(gᵢ x).toReal = gᵢ x` there.) -/
noncomputable def lagr {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (x : BregmanPPA.IneqMult.E n) (p : BregmanPPA.IneqMult.E m) : EReal := by
  classical
  exact
  if x ∈ C then
    (if p ∈ BregmanPPA.IneqMult.nonnegOrthant m then f x + ((∑ i, p i * (g i x).toReal : ℝ) : EReal) else ⊥)
  else ⊤

/-- `(x*, p*)` is a saddle point of `l` (p. 220):
`l(x*, p) ≤ l(x*, p*) ≤ l(x, p*)` for all `x ∈ ℝⁿ`, `p ∈ ℝᵐ`; equivalently, `x*` is optimal
for (10) and `p*` is a Lagrange multiplier. -/
def IsSaddlePair {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (x' : BregmanPPA.IneqMult.E n) (p' : BregmanPPA.IneqMult.E m) : Prop :=
  ∀ (x : BregmanPPA.IneqMult.E n) (p : BregmanPPA.IneqMult.E m), lagr C f g x' p ≤ lagr C f g x' p' ∧ lagr C f g x' p' ≤ lagr C f g x p'

/-- `∂ₓ l(x, p)`: the subgradients of the convex function `l(·, p)` at `x`. -/
def subdiffX {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (x : BregmanPPA.IneqMult.E n) (p : BregmanPPA.IneqMult.E m) : Set (BregmanPPA.IneqMult.E n) :=
  {u | IsSubgradient (fun y => lagr C f g y p) x u}

/-- `∂̂ₚ l(x, p)`: the supergradients of the concave function `l(x, ·)` at `p`, i.e. the `v` with
`-v ∈ ∂(-l(x, ·))(p)`, that is `l(x, q) ≤ l(x, p) + ⟪v, q - p⟫` for all `q`, with `l(x, p) > -∞`. -/
def supdiffP {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (x : BregmanPPA.IneqMult.E n) (p : BregmanPPA.IneqMult.E m) : Set (BregmanPPA.IneqMult.E m) :=
  {v | IsSubgradient (fun q => -(lagr C f g x q)) p (-v)}

/-- `ℝⁿ⁺ᵐ = ℝⁿ × ℝᵐ` with the Euclidean inner product `⟪(x, p), (y, q)⟫ = ⟪x, y⟫ + ⟪p, q⟫`. -/
abbrev PD (n m : ℕ) := WithLp 2 (BregmanPPA.IneqMult.E n × BregmanPPA.IneqMult.E m)

/-- The pair `(x, p) ∈ ℝⁿ⁺ᵐ`. -/
noncomputable abbrev pair {n m : ℕ} (x : BregmanPPA.IneqMult.E n) (p : BregmanPPA.IneqMult.E m) : PD n m := WithLp.toLp 2 (x, p)

/-- The operator `K(x, p) = ∂ₓ l(x, p) × (-∂̂ₚ l(x, p))` on `ℝⁿ⁺ᵐ` (p. 220). -/
def opK {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal) :
    PD n m → Set (PD n m) := fun z =>
  {w | w.ofLp.1 ∈ subdiffX C f g z.ofLp.1 z.ofLp.2 ∧
    -w.ofLp.2 ∈ supdiffP C f g z.ofLp.1 z.ofLp.2}

/-- `h = h_x ⊕ h_p`, `h(x, p) = h_x(x) + h_p(p)` (proof of Theorem 8, p. 221). -/
def sumFn {n m : ℕ} (hx : BregmanPPA.IneqMult.E n → ℝ) (hp : BregmanPPA.IneqMult.E m → ℝ) : PD n m → ℝ :=
  fun z => hx z.ofLp.1 + hp z.ofLp.2

/-- The product zone `S_x × S_p ⊆ ℝⁿ⁺ᵐ`. -/
def prodZone {n m : ℕ} (Sx : Set (BregmanPPA.IneqMult.E n)) (Sp : Set (BregmanPPA.IneqMult.E m)) : Set (PD n m) :=
  {z | z.ofLp.1 ∈ Sx ∧ z.ofLp.2 ∈ Sp}

/-- The objective of the `x`-step of (12) at step `k`, for `y ∈ C`:
`f(y) + (1/c_k) h_p*⁺(∇h_p(p^k) + c_k g(y)) + (1/c_k) D_{h_x}(y, x^k)`.
The value `h_p*⁺(·)` is used through `toReal`; Lemma 3 shows it is finite everywhere. -/
noncomputable def proxMultObj {n m : ℕ} (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (hx : BregmanPPA.IneqMult.E n → ℝ) (hp : BregmanPPA.IneqMult.E m → ℝ) (c : ℝ) (xk : BregmanPPA.IneqMult.E n) (pk : BregmanPPA.IneqMult.E m) (y : BregmanPPA.IneqMult.E n) : EReal :=
  f y + ((c⁻¹ * (BregmanPPA.IneqMult.monoConj hp (gradient hp pk + c • BregmanPPA.IneqMult.gvec g y)).toReal
    + c⁻¹ * BregmanPPA.Convergence.bregmanD hx y xk : ℝ) : EReal)

/-- A sequence `{(x^k, p^k)}` conforming to the recursions (12) (Theorem 8, p. 220):
`x⁰` lies in the zone `S_x` of `h_x`, every `p^k` lies in the zone `S_p` of `h_p`, and for every
`k ≥ 0`, `x^{k+1} ∈ C` minimizes the objective of (12) over `C`, and
`p^{k+1} = ∇h_p*⁺(∇h_p(p^k) + c_k g(x^{k+1}))`. -/
def IsProxMultRun {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ) (c : ℕ → ℝ)
    (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m) : Prop :=
  x 0 ∈ Sx ∧ ∀ k, p k ∈ Sp ∧ x (k + 1) ∈ C ∧
    (∀ y ∈ C, proxMultObj f g hx hp (c k) (x k) (p k) (x (k + 1))
      ≤ proxMultObj f g hx hp (c k) (x k) (p k) y) ∧
    p (k + 1) = gradient (fun z => (BregmanPPA.IneqMult.monoConj hp z).toReal)
      (gradient hp (p k) + c k • BregmanPPA.IneqMult.gvec g (x (k + 1)))

end BregmanPPA.ProxMult


