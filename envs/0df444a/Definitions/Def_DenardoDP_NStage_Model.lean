-- Prove2me | Definitions.Def_DenardoDP_NStage_Model
-- name    : DenardoDP_NStage_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:39:56.442985+00:00
-- url     : https://prove2.me/theorems/10fb392e-f9e2-41f1-9148-8338e7831a34
-- title:
--   Denardo's model under the N-stage contraction assumption: V, ρ, H_δ, A, E, the optimal return f, and the monotonicity and N-stage contraction assumptions (§2–§5)
-- statement:
--   This file fixes the abstract dynamic-programming model of Denardo (1967), §2–§5, in the form used under the N-stage contraction assumption.
--
--   Let $\Omega$ be a set of **points**. Each point $x$ carries a **decision set** $D_x$, and the **policy space** is the Cartesian product $\Delta=\times_{x\in\Omega}D_x$: a **policy** $\delta$ picks one decision $\delta_x\in D_x$ at every point, and every such choice is a policy.
--
--   1. **The space $V$.** $V$ is the set of bounded functions $v:\Omega\to\mathbb R$ with the metric $\rho(u,v)=\sup_{x\in\Omega}|u(x)-v(x)|$; it is complete. We write $u\ge v$ when $u(x)\ge v(x)$ for every $x$.
--   2. **Modulus.** An operator $B$ on $V$ *has modulus $c$ or less* when $\rho(Bu,Bv)\le c\,\rho(u,v)$ for all $u,v\in V$.
--   3. **The return and the policy operators.** The **return** $h$ assigns a real number $h(x,d_x,v)$ to every $x\in\Omega$, $d_x\in D_x$, $v\in V$. For each policy $\delta$ the operator $H_\delta$ on $V$ is $$[H_\delta(v)](x)=h(x,\delta_x,v),$$ display (1), whose range is assumed to lie in $V$.
--   4. **The maximization operator.** $A$ is the operator on $V$ given by display (3), $$(Av)(x)=\sup_{d_x\in D_x}h(x,d_x,v),$$ whose range is assumed to lie in $V$.
--   5. **The monotonicity assumption** (p. 168): if $u\ge v$ then $H_\delta(u)\ge H_\delta(v)$ for each $\delta\in\Delta$.
--   6. **The N-stage contraction assumption** (p. 169): there are a positive integer $N$ and a number $c<1$, both independent of $\delta$, such that for every $\delta$ the $N$-fold composition $H_\delta^N$ has modulus $c$ or less and $H_\delta$ itself has modulus $1$ or less.
--   7. **The optimal return.** For a family $(v_\delta)_{\delta\in\Delta}$ of return functions, $f$ is the **optimal return** when $f(x)=\sup_{\delta}v_\delta(x)$ for every $x$.
--   8. **The operator $E$** (p. 169): $(Ev)(x)=\sup_{\delta}(H_\delta^Nv)(x)$.
--
--   These are the objects about which Lemma 1, Lemma 2 and Theorem 4 of the paper are stated.
--
--   **Formalization Note** $V$ is Mathlib's `lp (fun _ : Ω => ℝ) ⊤`, whose `dist` is exactly $\rho$; it has no order instance, so $u\ge v$ is the pointwise predicate `PLe v u`. The operators $H_\delta$, $A$ and $E$ are taken as functions $V\to V$ (this is the paper's "range contained in $V$") and are tied to $h$ by the predicates `IsPolicyOperator` (equation (1)), `IsMaxOperator` and `IsNStageSupOperator`; every supremum, including the one defining $f$ (`IsOptimalReturn`), is a genuine least upper bound (`IsLUB`), never Lean's `sSup`/`⨆`, which return junk values on unbounded or empty sets. In particular `IsMaxOperator h A` forces every $D_x$ to be nonempty. "Modulus $c$ or less" is `ModulusLE`, the inequality itself; the smallest such $c$ is never needed. `NStageContractionAssumption H N c` contains $0<N$, $c<1$, the modulus bound on `(H δ)^[N]` and the modulus-$1$ bound on `H δ`. The monotonicity assumption is stated on $H_\delta$, as printed.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), pp. 166–169, §2 (display (1)), §3 (display (3), definition of modulus, p. 168), §4 (Monotonicity Assumption, p. 168), §5 (N-Stage Contraction Assumption, definitions of v_δ, f and E, p. 169)

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

namespace DenardoDP.NStage

/-- The N-stage contraction assumption (p. 169): N is a positive integer, c < 1, every
H_δ^N has modulus c or less, and every H_δ has modulus 1 or less (c and N independent of δ). -/
def NStageContractionAssumption {Ω : Type*} {D : Ω → Type*}
    (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (N : ℕ) (c : ℝ) : Prop :=
  0 < N ∧ c < 1 ∧ (∀ δ, DenardoDP.Contraction.ModulusLE (H δ)^[N] c) ∧ ∀ δ, DenardoDP.Contraction.ModulusLE (H δ) 1

/-- `E` is the operator (Ev)(x) = sup_δ (H_δ^N v)(x) of §5 (p. 169), the supremum taken as a
genuine least upper bound at every point. -/
def IsNStageSupOperator {Ω : Type*} {D : Ω → Type*}
    (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (N : ℕ) (E : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) : Prop :=
  ∀ w x, IsLUB (Set.range fun δ => (H δ)^[N] w x) (E w x)

end DenardoDP.NStage


