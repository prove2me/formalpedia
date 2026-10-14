-- Prove2me | Definitions.Def_ChanceStateCtrl_Robust_Setting
-- name    : ChanceStateCtrl_Robust_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:56.422613+00:00
-- url     : https://prove2.me/theorems/3b20df4f-aa76-42f5-9cd7-623dbd3de219
-- title:
--   §1.2, §3.2, pp. 3–4, 23–24 — class-S domain, weak Dirichlet solution, Ŝ, Ĝ, 𝒦̂, 𝒦̂⁻, the CQ and M(u)
-- statement:
--   This file fixes the objects of the robust state-constrained control problem (63).
--
--   **Domain and state equation.** $D\subseteq\mathbb R^d$ is open and bounded. It is of *class S* if there are $\gamma\in(0,1)$ and $r_0>0$ with $\operatorname{meas}(B_r(x)\setminus D)\ge\gamma\operatorname{meas}(B_r(x))$ for all $x\in\partial D$ and $0<r<r_0$. $L^2(D)$ is the Lebesgue space on $D$. A function $y$ is a *weak solution in $H^1_0(D)\cap C(\bar D)$* of
--   $$-\Delta y = F \ \text{in } D,\qquad y=0 \ \text{on } \partial D$$
--   if $y$ is continuous on $\bar D$, vanishes on $\partial D$, lies in $L^2(D)$, has weak first partial derivatives $G_i\in L^2(D)$, and $\int_D \nabla y\cdot\nabla\varphi\,dx=\int_D F\varphi\,dx$ for every $\varphi\in C_c^\infty(D)$. A bounded linear map $A^{-1}:L^2(D)\to C(\bar D)$ is the *solution operator* if $A^{-1}F$ is such a solution for every $F\in L^2(D)$.
--
--   **Robust objects.** Let $\Xi\subset\mathbb R^m$ be compact, $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $f(\cdot,z)=f_0+\sum_i z_i\varphi_i$ (eq. (3)). A function $\hat y\in C(\bar D\times\Xi)$ solves (63b)–(63c) if for every $z\in\Xi$ the slice $\hat y(\cdot,z)$ is the weak solution of $-\Delta\hat y(\cdot,z)=u+f(\cdot,z)$, $\hat y(\cdot,z)=0$ on $\partial D$. With $\alpha\in\mathbb R$:
--   $$[\hat{\mathcal S}(u)](x,z)=[A^{-1}(u+f(\cdot,z))](x),\qquad \hat{\mathcal G}(u)=\hat{\mathcal S}(u)-\alpha,\qquad [\hat{\mathcal A}^{-1}\hat{\mathcal B}h](x,z)=[A^{-1}h](x),$$
--   $$\hat{\mathcal K}=\{y\in C(\bar D\times\Xi): y\le 0\},\qquad \hat{\mathcal K}^-=\{y^*\in C(\bar D\times\Xi)^*:\langle y^*,y\rangle\le 0\ \ \forall y\in\hat{\mathcal K}\}.$$
--   The feasible set of (63) is $\{u\in L^2(D):\hat{\mathcal G}(u)\in\hat{\mathcal K}\}$, the constraint qualification is $0\in\operatorname{int}\{\hat{\mathcal G}(L^2(D))-\hat{\mathcal K}\}$, and
--   $$M(u)=\{(x,z)\in\bar D\times\Xi : [\hat{\mathcal S}(u)](x,z)=\max_{(x',z')\in\bar D\times\Xi}[\hat{\mathcal S}(u)](x',z')\}.$$
--   Finally, $u_x\in L^2(D)$ denotes the Riesz representer of the functional $h\mapsto[A^{-1}h](x)$, so that $(u_x,h)_{L^2(D)}=[A^{-1}h](x)$. A point $u^*$ *solves* a minimization problem if it is feasible and $F(u^*)\le F(u)$ for every feasible $u$.
--
--   These objects are shared by every statement of the mission (Lemmas 3.13–3.16, (66)).
--
--   **Formalization Note** $\bar D$ and $\Xi$ enter as subtypes carrying `CompactSpace` instances (the type-level form of compactness; for $\bar D$ it follows from boundedness of $D$), so that $C(\bar D\times\Xi)$ carries its sup norm. "$y\le0$ in $D\times\Xi$" is encoded as $y\le 0$ on $\bar D\times\Xi$, which is the same for continuous $y$. A slice $\hat y(\cdot,z)$ is extended by $0$ outside $\bar D$, values the weak formulation never reads. The paper's $M(u)$ is named `argmaxSet` to keep it apart from the sets $M$ of (11) and (35). The weak-derivative notions are the published `HunterPDE.Shared` definitions.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 3–4 (§1.2, class S, Assumption 1.1, (3), Lemma 1.2, (5)) and pp. 23–24 (§3.2, (63), Ŝ, Ĝ, 𝒦̂, 𝒦̂⁻, M(u))

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology

namespace ChanceStateCtrl.Robust

section Robust

variable {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}

/-- The source term (3) as an element of `L²(D)` for the parameter `z ∈ ℝᵐ`:
`f(·, z) = f₀ + ∑ᵢ zᵢ φᵢ`. -/
noncomputable def srcTerm (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D) (z : EuclideanSpace ℝ (Fin m)) :
    ChanceStateCtrl.PDE.L2 D :=
  f0 + ∑ i, z i • phi i

lemma continuous_srcTerm (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D) :
    Continuous (srcTerm f0 phi) := by
  unfold srcTerm
  refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
  exact ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).continuous).smul
    continuous_const

open Classical in
/-- `ŷ` solves the parametrized problem (63b)–(63c) in `C(D̄ × Ξ)`: for every `z ∈ Ξ`, the
function `ŷ(·, z)` (extended by `0` outside `D̄`, which `IsDirichletSol` never reads) is the weak
solution in `H¹₀(D) ∩ C(D̄)` of `−Δŷ(·, z) = u + f(·, z)` in `D`, `ŷ(·, z) = 0` on `∂D`. -/
def IsRobustStateSol [CompactSpace (closure D)] [CompactSpace Ξ] (f0 : ChanceStateCtrl.PDE.L2 D)
    (phi : Fin m → ChanceStateCtrl.PDE.L2 D) (u : ChanceStateCtrl.PDE.L2 D) (yhat : C(closure D × Ξ, ℝ)) : Prop :=
  ∀ z : Ξ, ChanceStateCtrl.PDE.IsDirichletSol D (⇑(u + srcTerm f0 phi z.1))
    (fun x => if hx : x ∈ closure D then yhat (⟨x, hx⟩, z) else 0)

/-- The robust control-to-state operator `Ŝ : L²(D) → C(D̄ × Ξ)` (p. 23),
`Ŝ(u) = Â⁻¹(ℬ̂u + f)`, i.e. `[Ŝ(u)](x, z) = [A⁻¹(u + f₀ + ∑ᵢ zᵢ φᵢ)](x)`. -/
noncomputable def Shat [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D) (u : ChanceStateCtrl.PDE.L2 D) :
    C(closure D × Ξ, ℝ) where
  toFun q := Ainv (u + srcTerm f0 phi q.2.1) q.1
  continuous_toFun := by
    have hz : Continuous fun z : Ξ => Ainv (u + srcTerm f0 phi z.1) :=
      Ainv.continuous.comp
        (continuous_const.add ((continuous_srcTerm f0 phi).comp continuous_subtype_val))
    exact continuous_eval.comp ((hz.comp continuous_snd).prodMk continuous_fst)

/-- `Ĝ(u) = Ŝ(u) − α` (p. 23). -/
noncomputable def Ghat [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D) (α : ℝ) (u : ChanceStateCtrl.PDE.L2 D) :
    C(closure D × Ξ, ℝ) :=
  Shat Ainv f0 phi u - ContinuousMap.const _ α

/-- `Â⁻¹ℬ̂h ∈ C(D̄ × Ξ)` (p. 23): the function `(x, z) ↦ [A⁻¹h](x)`, constant in `z`. -/
noncomputable def AhatBhat [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (h : ChanceStateCtrl.PDE.L2 D) : C(closure D × Ξ, ℝ) :=
  (Ainv h).comp ContinuousMap.fst

/-- The cone `𝒦̂ = {y ∈ C(D̄ × Ξ) : y ≤ 0}` (p. 23). For continuous `y`, `y ≤ 0` on `D × Ξ` is
the same as `y ≤ 0` on `D̄ × Ξ`. -/
def Khat (D : Set (EuclideanSpace ℝ (Fin d))) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    [CompactSpace (closure D)] [CompactSpace Ξ] : Set C(closure D × Ξ, ℝ) :=
  {y | ∀ q, y q ≤ 0}

/-- The polar cone `𝒦̂⁻ = {y* ∈ C(D̄ × Ξ)* : ⟨y*, y⟩ ≤ 0 ∀ y ∈ 𝒦̂}` (p. 23). -/
def KhatPolar (D : Set (EuclideanSpace ℝ (Fin d))) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    [CompactSpace (closure D)] [CompactSpace Ξ] : Set (StrongDual ℝ C(closure D × Ξ, ℝ)) :=
  {ys | ∀ y ∈ Khat D Ξ, ys y ≤ 0}

/-- The feasible set of (63): `{u ∈ L²(D) : Ĝ(u) ∈ 𝒦̂}`. -/
def robustFeasible [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D) (α : ℝ) :
    Set (ChanceStateCtrl.PDE.L2 D) :=
  {u | Ghat Ainv f0 phi α u ∈ Khat D Ξ}

/-- The constraint qualification of Lemma 3.14: `0 ∈ int{Ĝ(L²(D)) − 𝒦̂}`. -/
def RobustCQ [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D) (α : ℝ) : Prop :=
  (0 : C(closure D × Ξ, ℝ)) ∈
    interior {w | ∃ u : ChanceStateCtrl.PDE.L2 D, ∃ k ∈ Khat D Ξ, w = Ghat Ainv f0 phi α u - k}

/-- `M(u)` (p. 24): the points of `D̄ × Ξ` where `Ŝ(u)` attains its maximum over `D̄ × Ξ`. -/
def argmaxSet [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D) (u : ChanceStateCtrl.PDE.L2 D) :
    Set (closure D × Ξ) :=
  {q | ∀ q' : closure D × Ξ, Shat Ainv f0 phi u q' ≤ Shat Ainv f0 phi u q}

/-- The Riesz representer `uₓ ∈ L²(D)` of the continuous linear functional `h ↦ [A⁻¹h](x)` on
`L²(D)` (`L²(D)*` identified with `L²(D)`): `⟪uₓ, h⟫ = [A⁻¹h](x)`. -/
noncomputable def evalRep [CompactSpace (closure D)] (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (x : closure D) : ChanceStateCtrl.PDE.L2 D :=
  (InnerProductSpace.toDual ℝ (ChanceStateCtrl.PDE.L2 D)).symm ((ContinuousMap.evalCLM ℝ x).comp Ainv)

end Robust

end ChanceStateCtrl.Robust


