-- Prove2me | Definitions.Def_ChanceStateCtrl_AlmostSure_Setting
-- name    : ChanceStateCtrl_AlmostSure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:54.070977+00:00
-- url     : https://prove2.me/theorems/e223969f-8134-4b6b-b0f8-fe64a047aae0
-- title:
--   §1.2, §3.1, pp. 3–4, 20–21 — class-S domain, weak Dirichlet solution, L∞_P(Ω, C(D̄)), 𝒮, 𝒢, 𝒦, 𝒦⁻, the CQ, absolutely continuous and singular functionals
-- statement:
--   This file fixes the objects of the almost-surely state-constrained control problem (51) of Geiersbach and Henrion.
--
--   **The domain and the state equation.** Let $D\subseteq\mathbb R^d$ be open and bounded. The class-S condition on $D$, the space $L^2(D)$ and the notion of a *weak solution* $y\in H^1_0(D)\cap\mathcal C(\bar D)$ of $-\Delta y=F$ in $D$, $y=0$ on $\partial D$, i.e. $y$ continuous on $\bar D$, zero on $\partial D$, in $L^2(D)$ with weak first derivatives in $L^2(D)$ and
--   $$\int_D \nabla y\cdot\nabla\varphi\,dx=\int_D F\varphi\,dx\qquad\text{for all }\varphi\in C_c^\infty(D),$$
--   are those of the imported module `ChanceStateCtrl.PDE.Model`. This file defines: a continuous linear map $A^{-1}:L^2(D)\to\mathcal C(\bar D)$ is a *solution operator* if $A^{-1}F$ is, for every $F\in L^2(D)$, the restriction to $\bar D$ of such a weak solution (by the uniqueness part of Lemma 1.2 it is then the paper's $A^{-1}$).
--
--   **The random setting.** $(\Omega,\mathcal F,\mathbb P)$ is a probability space, $L^\infty_{\mathbb P}(\Omega,X)$ the Bochner space of essentially bounded strongly measurable $X$-valued random elements, and $\tilde f\in L^\infty_{\mathbb P}(\Omega,L^2(D))$ the random source. With $\mathcal B:L^2(D)\to L^\infty_{\mathbb P}(\Omega,L^2(D))$ the embedding of $u$ as a constant random element and $[\mathcal A^{-1}y](\omega)=A^{-1}y(\cdot,\omega)$, the control-to-state operator and the constraint map are
--   $$\mathcal S(u)=\mathcal A^{-1}(\mathcal Bu+\tilde f),\qquad \mathcal G(u)=\mathcal S(u)-\boldsymbol\alpha ,$$
--   where $\boldsymbol\alpha$ is the constant function $\alpha\in\mathbb R$ seen in $L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D))$. The cone and its polar are
--   $$\mathcal K=\{y\in L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D)) : y(x,\omega)\le 0\ \text{for all }x\in\bar D,\ \mathbb P\text{-a.s.}\},\qquad \mathcal K^-=\{y^*\in(L^\infty_{\mathbb P}(\Omega,\mathcal C(\bar D)))^* : \langle y^*,y\rangle\le 0\ \forall y\in\mathcal K\}.$$
--   The feasible set of (51) is $\{u\in L^2(D):\mathcal G(u)\in\mathcal K\}$ (a *solution* of (51) is a global minimizer of $F$ over it, the predicate `IsSolution` of the imported `ChanceStateCtrl.General.Setting`), and the constraint qualification is $0\in\operatorname{int}\{\mathcal G(L^2(D))-\mathcal K\}$.
--
--   **Decomposition of $(L^\infty_{\mathbb P}(\Omega,X))^*$.** For a Banach space $X$, $\Lambda_1(X^*)$ is the set of weakly measurable $x^*:\Omega\to X^*$ (each $\omega\mapsto\langle x^*(\omega),x\rangle$ measurable) with $\int_\Omega\|x^*(\omega)\|\,d\mathbb P<\infty$. A functional $v\in(L^\infty_{\mathbb P}(\Omega,X))^*$ is *absolutely continuous* if $\langle v,x\rangle=\int_\Omega\langle x^*(\omega),x(\omega)\rangle\,d\mathbb P(\omega)$ for all $x$ and some $x^*\in\Lambda_1(X^*)$, and *singular* (relative to $\mathbb P$) if there are measurable sets $F_{n+1}\subseteq F_n$ with $\mathbb P(F_n)\to0$ such that $\langle v,x\rangle=0$ for every $x$ that vanishes on some $F_n$.
--
--   These are the objects of Lemma 3.6, Lemma 3.7, Theorem 3.9 and Theorem 3.10.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, weak derivatives are the published `HunterPDE.Shared.HasWeakDeriv` with test functions `HunterPDE.Shared.IsTestFunction`. An $H^1(D)$ function continuous on $\bar D$ and vanishing on $\partial D$ lies in $H^1_0(D)$, so `IsDirichletSol` is the paper's class $H^1_0(D)\cap\mathcal C(\bar D)$. $\mathcal C(\bar D)$ is `C(closure D, ℝ)`; its norm needs `CompactSpace (closure D)` as an instance argument, which follows from boundedness of $D$. $L^\infty_{\mathbb P}$ is `Lp _ ⊤ P`, whose elements are a.e. classes. The paper's "$y(x,\omega)\le0$ a.e. in $D$" is read as "for all $x\in\bar D$" (equivalent for functions continuous on $\bar D$ with $D$ open). The $L^1$ norm in $\Lambda_1$ is a lower Lebesgue integral of $\|x^*(\omega)\|$, which is measurable when $X$ is separable. $\mathcal B u$ and $\boldsymbol\alpha$ are `Lp.const`; $\mathcal A^{-1}$ is `ContinuousLinearMap.compLp`.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 3–4 (§1.1, §1.2: class S, Lemma 1.2, A⁻¹) and pp. 20–21 (problem (51), Assumption 3.5, 𝒮, 𝒢, 𝒦, 𝒦⁻, Lemma 3.7's constraint qualification, (55), Λ∘(X∗), Λ₁(X∗))

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology

namespace ChanceStateCtrl.AlmostSure

/-- `Ainv : L²(D) → C(D̄)` is the solution operator `A⁻¹` of p. 4: for every `F ∈ L²(D)`, the
continuous function `Ainv F` on `D̄` is (the restriction to `D̄` of) a weak solution of
`−Δy = F` in `D`, `y = 0` on `∂D`. -/
def IsSolutionOperator {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) : Prop :=
  ∀ F : ChanceStateCtrl.PDE.L2 D, ∃ y, ChanceStateCtrl.PDE.IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x

section Decomposition

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Λ₁(X*)` (p. 21): weakly measurable `x* : Ω → X*` (each `ω ↦ ⟨x*(ω), x⟩` is measurable)
with `‖x*‖_{L¹_P(Ω, X*)} = ∫ ‖x*(ω)‖ dP(ω) < ∞`. -/
def Lambda1 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (P : Measure Ω) :
    Set (Ω → StrongDual ℝ X) :=
  {xs | (∀ x : X, Measurable fun ω => xs ω x) ∧ ∫⁻ ω, ‖xs ω‖ₑ ∂P < ⊤}

/-- (55), p. 21: `v ∈ (L∞_P(Ω, X))*` is absolutely continuous if
`⟨v, x⟩ = ∫_Ω ⟨x*(ω), x(ω)⟩ dP(ω)` for all `x ∈ L∞_P(Ω, X)`, for some `x* ∈ Λ₁(X*)`. -/
def IsAbsCont {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (P : Measure Ω)
    (v : StrongDual ℝ (Lp X ⊤ P)) : Prop :=
  ∃ xs ∈ Lambda1 X P, ∀ x : Lp X ⊤ P, v x = ∫ ω, xs ω (x ω) ∂P

/-- p. 21: `v° ∈ (L∞_P(Ω, X))*` is singular relative to `P` if there is a decreasing sequence of
measurable sets `Fₙ` with `P(Fₙ) → 0` such that `⟨v°, x⟩ = 0` for every `x ∈ L∞_P(Ω, X)` that
vanishes (a.s.) on some `Fₙ`. -/
def IsSingular {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (P : Measure Ω)
    (v : StrongDual ℝ (Lp X ⊤ P)) : Prop :=
  ∃ Fs : ℕ → Set Ω, (∀ n, MeasurableSet (Fs n)) ∧ (∀ n, Fs (n + 1) ⊆ Fs n) ∧
    Tendsto (fun n => P (Fs n)) atTop (𝓝 0) ∧
    ∀ x : Lp X ⊤ P, (∃ n, ∀ᵐ ω ∂P, ω ∈ Fs n → x ω = 0) → v x = 0

end Decomposition

section Operators

variable {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- `L∞_P(Ω, C(D̄))`. -/
abbrev Linf (D : Set (EuclideanSpace ℝ (Fin d))) [CompactSpace (closure D)] (P : Measure Ω) :
    Type _ :=
  Lp C(closure D, ℝ) ⊤ P

/-- `ℬ : L²(D) → L∞_P(Ω, L²(D))`: `u` as the constant (in `ω`) random element. -/
noncomputable def Bconst (P : Measure Ω) [IsFiniteMeasure P] (u : ChanceStateCtrl.PDE.L2 D) : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P :=
  Lp.const ⊤ P u

/-- A function `c ∈ C(D̄)` as the constant element of `L∞_P(Ω, C(D̄))`; the constant function
`α` gives the paper's bold `𝛂`. -/
noncomputable def constLinf (P : Measure Ω) [IsFiniteMeasure P] (c : C(closure D, ℝ)) :
    Linf D P :=
  Lp.const ⊤ P c

/-- The control-to-state operator `𝒮(u) = 𝒜⁻¹(ℬu + f̃)` (p. 20), with
`[𝒜⁻¹y](ω) = A⁻¹ y(·, ω)`. -/
noncomputable def Ssol (P : Measure Ω) [IsFiniteMeasure P] (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (u : ChanceStateCtrl.PDE.L2 D) : Linf D P :=
  Ainv.compLp (Bconst P u + ftil)

/-- `𝒢(u) = 𝒮(u) − 𝛂` (p. 20). -/
noncomputable def Gop (P : Measure Ω) [IsFiniteMeasure P] (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (u : ChanceStateCtrl.PDE.L2 D) : Linf D P :=
  Ssol P Ainv ftil u - constLinf P (ContinuousMap.const (closure D) α)

/-- The cone `𝒦 = {y ∈ L∞_P(Ω, C(D̄)) : y(x, ω) ≤ 0 on D̄, P-a.s.}` (p. 20). -/
def Kcone (D : Set (EuclideanSpace ℝ (Fin d))) [CompactSpace (closure D)] (P : Measure Ω) :
    Set (Linf D P) :=
  {y | ∀ᵐ ω ∂P, ∀ x : closure D, y ω x ≤ 0}

/-- The polar cone `𝒦⁻ = {y* ∈ (L∞_P(Ω, C(D̄)))* : ⟨y*, y⟩ ≤ 0 ∀ y ∈ 𝒦}` (p. 20). -/
def Kpolar (D : Set (EuclideanSpace ℝ (Fin d))) [CompactSpace (closure D)] (P : Measure Ω) :
    Set (StrongDual ℝ (Linf D P)) :=
  {ys | ∀ y ∈ Kcone D P, ys y ≤ 0}

/-- The feasible set of (51): `{u ∈ L²(D) : 𝒢(u) ∈ 𝒦}`. -/
def feasible (P : Measure Ω) [IsFiniteMeasure P] (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) : Set (ChanceStateCtrl.PDE.L2 D) :=
  {u | Gop P Ainv ftil α u ∈ Kcone D P}

/-- The constraint qualification of Lemma 3.7: `0 ∈ int{𝒢(L²(D)) − 𝒦}`. -/
def CQ (P : Measure Ω) [IsFiniteMeasure P] (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) : Prop :=
  (0 : Linf D P) ∈ interior {w | ∃ u : ChanceStateCtrl.PDE.L2 D, ∃ k ∈ Kcone D P, w = Gop P Ainv ftil α u - k}

end Operators

end ChanceStateCtrl.AlmostSure


