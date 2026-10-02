-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_operatorGraph
-- name    : TeschlQM_SturmLiouville_operatorGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:45:13.878984+00:00
-- url     : https://prove2.me/theorems/7918fa54-ac3f-44d8-8c9f-a609de392f6e
-- title:
--   The operator $f \mapsto \tau f$ with boundary conditions (9.19)–(9.21)
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data and let $v, w$ be functions (boundary functions at $a$ and $b$). For a set $D \subseteq \mathfrak{D}(\tau)$ the **operator** $f \mapsto \tau f$ on $D$ has graph
--   $$\{ (f, \tau f) \mid f \in D \} \subseteq L^2(I, r\,dx) \times L^2(I, r\,dx).$$
--   The two domains used in Theorem 9.6 are
--   $$\mathfrak{D}(A) = \{ f \in \mathfrak{D}(\tau) \mid W_a(v, f) = 0 \text{ if l.c. at } a,\ W_b(w, f) = 0 \text{ if l.c. at } b\} \tag{9.20}$$
--   and
--   $$\mathfrak{D}_1 = \{ f \in \mathfrak{D}(\tau) \mid \exists x_0 \in I: \forall x \in (a, x_0),\ W_x(v, f) = 0,\ \exists x_1 \in I: \forall x \in (x_1, b),\ W_x(w, f) = 0\}. \tag{9.21}$$
--
--   These are the self-adjoint realization of $\tau$ with separated boundary conditions and its core.
--
--   **Formalization Note.** `operatorGraph L D` is the graph as a set of pairs of $L^2$ classes; `bcDomain L v w` is (9.20) and `coreDomain L v w` is (9.21). As in (9.20), each condition of (9.21) is imposed only at an endpoint where $\tau$ is l.c., since $v$ (resp. $w$) is only given there.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 187, Section 9.2, Eqs. (9.19)–(9.21)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl (9.19), p. 187: the graph `{(f, τ f) | f ∈ D}` of the operator `f ↦ τ f` on a set
`D ⊆ D(τ)` of functions, as a subset of `L²(I, r dx) × L²(I, r dx)` (elements of `Lp` are
a.e.-classes; `f` is the `AC_loc` representative and `g = τ f`). -/
def operatorGraph (L : SLData) (D : (ℝ → ℂ) → Prop) :
    Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure) :=
  {x | ∃ (f g : ℝ → ℂ) (hf : MemLp f 2 L.measure) (hg : MemLp g 2 L.measure),
    D f ∧ SolvesTau L f g ∧ x = (hf.toLp f, hg.toLp g)}

/-- Teschl (9.20), p. 187: the domain
`𝔇(A) = {f ∈ D(τ) | W_a(v, f) = 0 if l.c. at a, W_b(w, f) = 0 if l.c. at b}`
of the self-adjoint operator of Theorem 9.6, for the boundary functions `v` (at `a`) and `w`
(at `b`). -/
def bcDomain (L : SLData) (v w : ℝ → ℂ) (f : ℝ → ℂ) : Prop :=
  InMaxDomain L f ∧ (IsLimitCircleLeft L → wronskianLeft L v f = 0) ∧
    (IsLimitCircleRight L → wronskianRight L w f = 0)

/-- Teschl (9.21), p. 187: the set
`D₁ = {f ∈ D(τ) | ∃ x₀ ∈ I : ∀ x ∈ (a, x₀), W_x(v, f) = 0, ∃ x₁ ∈ I : ∀ x ∈ (x₁, b), W_x(w, f) = 0}`.
As in (9.20), the condition at an endpoint is imposed only if `τ` is l.c. there (the functions
`v`, `w` exist only in that case). -/
def coreDomain (L : SLData) (v w : ℝ → ℂ) (f : ℝ → ℂ) : Prop :=
  InMaxDomain L f ∧
    (IsLimitCircleLeft L → ∃ x₀ ∈ L.I, ∀ x ∈ L.I, x < x₀ → wronskian L x v f = 0) ∧
    (IsLimitCircleRight L → ∃ x₁ ∈ L.I, ∀ x ∈ L.I, x₁ < x → wronskian L x w f = 0)

end TeschlQM.SturmLiouville


