-- Prove2me | Definitions.Def_GhostPenalty_AssumptionA
-- name    : GhostPenalty_AssumptionA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:53.147104+00:00
-- url     : https://prove2.me/theorems/121abcc8-76a2-45a6-80e4-027138089e14
-- title:
--   Assumption A on the surrogates $\tilde f,\tilde g$
-- statement:
--   Let $O_d$ and $O_x$ be open neighbourhoods of $\beta\mathbb B^n_\infty$ and $K$, and let $\tilde f$ and $\tilde g_i$ ($i=1,\dots,m$) be continuously differentiable on $O_d$ with respect to the first argument, for every second argument in $O_x$. Assumption A requires:
--
--   1. (A1) $\tilde f(\cdot;x)$ is strongly convex with modulus $c>0$ independent of $x\in K$;
--   2. (A2) $\tilde f(\cdot;\cdot)$ is continuous on $O_d\times O_x$;
--   3. (A3) $\nabla_1\tilde f(\cdot;\cdot)$ is continuous on $O_d\times O_x$;
--   4. (A4) $\nabla_1\tilde f(0;x)=\nabla f(x)$ for every $x\in K$;
--   5. (A5) $\tilde g_i(\cdot;x)$ is convex for every $x\in K$;
--   6. (A6) $\tilde g_i(\cdot;\cdot)$ is continuous on $\mathbb R^n\times O_x$;
--   7. (A7) $\tilde g_i(0;x)=g_i(x)$ for every $x\in K$;
--   8. (A8) $\nabla_1\tilde g_i(\cdot;\cdot)$ is continuous on $O_d\times O_x$;
--   9. (A9) $\nabla_1\tilde g_i(0;x)=\nabla g_i(x)$ for every $x\in K$.
--
--   Here $\nabla_1$ is the gradient in the first argument. The classical SQP choice $\tilde f(d;x)=\nabla f(x)^Td+\tfrac12 d^TH(x)d$, $\tilde g(d;x)=g(x)+\nabla g(x)^Td$ with uniformly positive definite $H(x)$ satisfies it.
--
--   **Formalization Note** Strong convexity is Mathlib's `StrongConvexOn` with modulus $c$: $\tilde f(td+(1-t)d')\le t\tilde f(d)+(1-t)\tilde f(d')-\tfrac c2t(1-t)\|d-d'\|^2$, the convention under which the paper's (19) reads $(\nabla_1\tilde f(d;x)-\nabla_1\tilde f(0;x))^Td\ge c\|d\|^2$. The source states A1 and A5 "on $O_d$"; since $O_d$ need not be convex, they are imposed on the convex box $\beta\mathbb B^n_\infty\subseteq O_d$, where every use takes place (a weaker requirement). $\tilde f,\tilde g$ are total functions on $\mathbb R^n\times\mathbb R^n$; all conditions refer only to $O_d$, $O_x$.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Assumption A, p.7

import Mathlib
import Definitions.Def_GhostPenalty_box

namespace GhostPenalty

/-- **Assumption A** on the surrogates `f̃` and `g̃`.
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, Assumption A, p.7: "Let `O_d` and `O_x` be open neighborhoods of `βBⁿ∞` and `K`,
respectively, and `f̃ : O_d × O_x → ℝ` and `g̃_i : ℝⁿ × O_x → ℝ` for every `i = 1,...,m` be
continuously differentiable on `O_d` with respect to the first argument and such that
A1) `f̃(•;x)` is a strongly convex function on `O_d` for every `x ∈ K` with modulus of strong
convexity `c > 0` independent of `x`; A2) `f̃(•;•)` is continuous on `O_d × O_x`;
A3) `∇₁f̃(•;•)` is continuous `O_d × O_x`; A4) `∇₁f̃(0;x) = ∇f(x)` for every `x ∈ K`;
A5) `g̃_i(•;x)` is a convex function on `O_d` for every `x ∈ K`; A6) `g̃_i(•;•)` is continuous on
`ℝⁿ × O_x`; A7) `g̃_i(0;x) = g_i(x)` for every `x ∈ K`; A8) `∇₁g̃_i(•;•)` is continuous on
`O_d × O_x`; A9) `∇₁g̃_i(0;x) = ∇g_i(x)`, for every `x ∈ K`; where `∇₁f̃(u;x)` and `∇₁g̃_i(u;x)`
denote the partial gradient of `f̃(•;x)` and `g̃_i(•;x)` evaluated at `u`."

**Formalization Note.** `f̃(d;x)` is `ft d x` and `g̃_i(d;x)` is `gt i d x` (first argument the
direction), defined on all of `ℝⁿ × ℝⁿ`; every condition refers only to `O_d`, `O_x` as on the
page. "Continuously differentiable on `O_d` with respect to the first argument" is
`ContDiffOn ℝ 1 (· ; x) O_d` for each `x ∈ O_x`. `∇₁` is `gradient` of the partial function.
A1 is Mathlib's `StrongConvexOn (box n β) c`, i.e.
`f̃(td+(1−t)d') ≤ t f̃(d) + (1−t) f̃(d') − (c/2) t(1−t)‖d−d'‖²`, the convention under which the
paper's (19) reads `(∇₁f̃(d;x) − ∇₁f̃(0;x))ᵀd ≥ c‖d‖²`. A1 and A5 are imposed on the convex box
`βBⁿ∞ ⊆ O_d` rather than on `O_d` (which need not be convex): every use of A1 and A5 in the
paper is at points of `βBⁿ∞`, and the requirement is weaker than "on `O_d`". -/
def AssumptionA {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (K : Set (EuclideanSpace ℝ (Fin n))) (β : ℝ)
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (Od Ox : Set (EuclideanSpace ℝ (Fin n))) (c : ℝ) : Prop :=
  IsOpen Od ∧ box n β ⊆ Od ∧ IsOpen Ox ∧ K ⊆ Ox ∧ 0 < c ∧
  (∀ x ∈ Ox, ContDiffOn ℝ 1 (fun u => ft u x) Od ∧ ∀ i, ContDiffOn ℝ 1 (fun u => gt i u x) Od) ∧
  -- A1
  (∀ x ∈ K, StrongConvexOn (box n β) c (fun u => ft u x)) ∧
  -- A2
  ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ft p.1 p.2)
    (Od ×ˢ Ox) ∧
  -- A3
  ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    gradient (fun u => ft u p.2) p.1) (Od ×ˢ Ox) ∧
  -- A4
  (∀ x ∈ K, gradient (fun u => ft u x) 0 = gradient f x) ∧
  -- A5
  (∀ x ∈ K, ∀ i, ConvexOn ℝ (box n β) (fun u => gt i u x)) ∧
  -- A6
  (∀ i, ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    gt i p.1 p.2) (Set.univ ×ˢ Ox)) ∧
  -- A7
  (∀ x ∈ K, ∀ i, gt i 0 x = g i x) ∧
  -- A8
  (∀ i, ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    gradient (fun u => gt i u p.2) p.1) (Od ×ˢ Ox)) ∧
  -- A9
  (∀ x ∈ K, ∀ i, gradient (fun u => gt i u x) 0 = gradient (g i) x)

end GhostPenalty


