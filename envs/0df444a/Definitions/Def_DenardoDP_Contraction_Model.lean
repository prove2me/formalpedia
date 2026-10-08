-- Prove2me | Definitions.Def_DenardoDP_Contraction_Model
-- name    : DenardoDP_Contraction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:29:50.73643+00:00
-- url     : https://prove2.me/theorems/8c4db3fd-0031-4df2-baef-33f57648647b
-- title:
--   Denardo's abstract return model, operators, and assumptions
-- statement:
--   This file fixes the abstract dynamic-programming model of Denardo (1967), §2–§4, shared by every mission of the paper.
--
--   Let $\Omega$ be a set of **points**. Each point $x$ carries a **decision set** $D_x$, and the **policy space** is the Cartesian product $\Delta=\times_{x\in\Omega}D_x$: a **policy** $\delta$ picks one decision $\delta_x\in D_x$ at every point, and every such choice is a policy.
--
--   1. **The space $V$.** $V$ is the set of bounded functions $v:\Omega\to\mathbb R$, with the metric $\rho(u,v)=\sup_{x\in\Omega}|u(x)-v(x)|$. For $u,v\in V$ one writes $u\ge v$ when $u(x)\ge v(x)$ for every $x$.
--   2. **Modulus.** An operator $B$ on $V$ *has modulus $c$ or less* when $\rho(Bu,Bv)\le c\,\rho(u,v)$ for all $u,v\in V$.
--   3. **The return and the policy operators.** The **return** $h$ assigns a real number $h(x,d_x,v)$ to every $x\in\Omega$, $d_x\in D_x$, $v\in V$. For each policy $\delta$, the operator $H_\delta$ on $V$ is given by display (1), $$[H_\delta(v)](x)=h(x,\delta_x,v),$$ and its range is assumed to lie in $V$.
--   4. **The maximization operator.** $A$ is the operator on $V$ given by display (3), $$(Av)(x)=\sup_{d_x\in D_x}h(x,d_x,v),$$ and its range is assumed to lie in $V$.
--   5. **The contraction assumption** (p. 166) for a number $c$: $0\le c<1$ and $$|h(x,d_x,u)-h(x,d_x,v)|\le c\,\rho(u,v)$$ for every $u,v\in V$, $x\in\Omega$ and $d_x\in D_x$.
--   6. **The monotonicity assumption** (p. 168): if $u\ge v$, then $H_\delta(u)\ge H_\delta(v)$ for each $\delta\in\Delta$.
--   7. **The optimal return.** For a family $(v_\delta)_{\delta\in\Delta}$ of return functions, $f$ is the **optimal return** when $f(x)=\sup_{\delta\in\Delta}v_\delta(x)$ for every $x$ (p. 167).
--
--   These are the objects about which Theorems 1–4, Corollaries 1–2 and Lemmas 1–2 of the paper are stated; the N-stage contraction assumption of §5 is built on top of them.
--
--   **Formalization Note** $V$ is Mathlib's `lp (fun _ : Ω => ℝ) ⊤`, whose distance is exactly $\rho$; it has no order instance, so $u\ge v$ is the pointwise predicate `PLe v u`. The operators $H_\delta$ and $A$ are data of type $V\to V$ (this is the paper's "range contained in $V$"), tied to $h$ by `IsPolicyOperator` (display (1)) and `IsMaxOperator` (display (3)). Every supremum, including the one defining $f$ (`IsOptimalReturn`), is a genuine real least upper bound (`IsLUB`), never Lean's `sSup`/`⨆`, which return a junk value on unbounded or empty sets; in particular `IsMaxOperator h A` forces every $D_x$ to be nonempty, and `IsOptimalReturn v w` asserts that $f$ is real-valued and bounded. "Modulus $c$ or less" is the inequality itself (`ModulusLE`); the smallest such $c$ is never needed. The contraction assumption takes $c$ as a parameter, so "for some $c$" is an existential in the theorems that use it. The monotonicity assumption is stated on $H_\delta$, as printed; the paper's equivalent form on $h$ is not used.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), pp. 166–168, §2–§4, equations (1)–(3) and the Contraction and Monotonicity Assumptions; https://doi.org/10.1137/1009030

import Mathlib

namespace DenardoDP.Contraction

/-- The space `V` of bounded real functions on `Ω`, with the uniform metric `ρ` (p. 166). -/
abbrev BFun (Ω : Type*) := lp (fun _ : Ω => ℝ) ⊤

/-- Pointwise order on `V` (p. 168). -/
def PLe {Ω : Type*} (u v : BFun Ω) : Prop := ∀ x, u x ≤ v x

/-- An operator has modulus at most `c` (p. 168). -/
def ModulusLE {Ω : Type*} (B : BFun Ω → BFun Ω) (c : ℝ) : Prop :=
  ∀ u v, dist (B u) (B v) ≤ c * dist u v

/-- Equation (1), including the assumption that each policy operator maps `V` to `V`. -/
def IsPolicyOperator {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω) : Prop :=
  ∀ δ v x, H δ v x = h x (δ x) v

/-- Equation (3): `A v` is the pointwise real supremum of available returns and lies in `V`. -/
def IsMaxOperator {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ) (A : BFun Ω → BFun Ω) : Prop :=
  ∀ v x, IsLUB (Set.range fun d : D x => h x d v) (A v x)

/-- The contraction assumption on the return function `h` (p. 166). -/
def ContractionAssumption {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ c < 1 ∧
    ∀ (u v : BFun Ω) (x : Ω) (d : D x),
      |h x d u - h x d v| ≤ c * dist u v

/-- The monotonicity assumption, on the policy operators as stated on p. 168. -/
def MonotonicityAssumption {Ω : Type*} {D : Ω → Type*}
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω) : Prop :=
  ∀ δ u v, PLe v u → PLe (H δ v) (H δ u)

/-- The pointwise supremum of the policy return functions, denoted `f` on p. 167. -/
def IsOptimalReturn {Ω : Type*} {D : Ω → Type*}
    (v : ((x : Ω) → D x) → BFun Ω) (w : BFun Ω) : Prop :=
  ∀ x, IsLUB (Set.range fun δ => v δ x) (w x)

end DenardoDP.Contraction


