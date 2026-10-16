-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
-- name    : OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:37:07.070328+00:00
-- url     : https://prove2.me/theorems/219c37c8-775e-4f57-ad6e-08b72fbe3825
-- title:
--   The permanent pairing on symmetric powers and the duality $\mathrm{Sym}^n(V^*)\cong(\mathrm{Sym}^n V)^*$
-- statement:
--   For a complex vector space $X$ let $X^*$ be its dual space, $S(X)$ its symmetric algebra over $\mathbb{C}$, and, for $n\in\mathbb{N}$, $\mathrm{Sym}^n X\subseteq S(X)$ the linear span of the products $[x_0,\dots,x_{n-1}]=x_0\cdots x_{n-1}$ of $n$ elements of $X$. Write $S_n$ for the symmetric group on $\{0,\dots,n-1\}$. Let $X,Y$ be complex vector spaces and $B:X\times Y\to\mathbb{C}$ a bilinear form, and for $x\in X^n$, $y\in Y^n$ put
--   $$\mathrm{per}_B(x,y)=\frac{1}{n!}\sum_{\sigma\in S_n}\ \prod_{i=0}^{n-1}B\bigl(x_i,y_{\sigma(i)}\bigr).$$
--
--   1. **Partial descent.** For $x\in X^n$ let $\lambda_x\in(\mathrm{Sym}^n Y)^*$ be the linear functional with $\lambda_x([y_0,\dots,y_{n-1}])=\mathrm{per}_B(x,y)$ for all $y\in Y^n$. The map $x\mapsto\lambda_x$ is $n$-linear and symmetric in $x_0,\dots,x_{n-1}$.
--   2. **Induced pairing.** There is a linear map $\langle\cdot,\cdot\rangle_B:\mathrm{Sym}^n X\to(\mathrm{Sym}^n Y)^*$ with
--   $$\bigl\langle[x_0,\dots,x_{n-1}],\,[y_0,\dots,y_{n-1}]\bigr\rangle_B=\mathrm{per}_B(x,y)\qquad\text{for all }x\in X^n,\ y\in Y^n.$$
--   3. **Evaluation pairing.** For a complex vector space $V$, the case $X=V^*$, $Y=V$, $B(\varphi,v)=\varphi(v)$ gives the linear map $D_n:\mathrm{Sym}^n(V^*)\to(\mathrm{Sym}^n V)^*$ with $D_n([\varphi_0,\dots,\varphi_{n-1}])([v_0,\dots,v_{n-1}])=\frac{1}{n!}\sum_{\sigma\in S_n}\prod_{i}\varphi_i(v_{\sigma(i)})$. On pure powers $x^n=[x,\dots,x]$ it is evaluation: $D_n(p)(x^n)=p(x)$ for all $p\in\mathrm{Sym}^n(V^*)$ and $x\in V$, where $p(x)$ denotes the image of $p$ under the algebra homomorphism $S(V^*)\to\mathbb{C}$ extending $\varphi\mapsto\varphi(x)$.
--   4. **Perfect duality.** If $V$ is finite-dimensional, then $D_n$ is injective and $\dim\mathrm{Sym}^n(V^*)=\dim(\mathrm{Sym}^n V)^*$, so $D_n$ is a linear isomorphism
--   $$D_n:\ \mathrm{Sym}^n(V^*)\ \xrightarrow{\ \sim\ }\ (\mathrm{Sym}^n V)^*.$$
--
--   This is the standard identification of linear functionals on a symmetric power with symmetric tensors on the dual space, normalized so that it is compatible with evaluating polynomial functions at points. Items 1 to 3 hold for spaces of any dimension; only item 4 uses finite dimension.
--
--   **Formalization Note** The objects are `leftMultilinear`, `pairing`, `dualMap` and `dualEquiv` in the namespace `PairingConstruction`; `pairing` is obtained from `leftMultilinear` by the universal property of symmetric powers, `dualMap V n` is `pairing n` applied to the identity of the dual space, and `dual_finrank` is the dimension equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/PairingConstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/PairingConstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346.PairingConstruction

universe u v
variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- Descend the right-hand family of the normalized permanent. -/
def leftMultilinear (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => X) (Module.Dual ℂ (SymPow n Y)) :=
  (symPowLiftLinear n Y ℂ).compMultilinearMap
    ((permanentPairingMultilinear n B).codRestrict
      (symmetricMultilinearSubmodule n Y ℂ) (by
        intro x σ y
        exact permanentPairingMultilinear_perm_right n B x y σ))

@[simp] theorem leftMultilinear_apply_monomial (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    leftMultilinear n B x (symMonomial n Y y) =
      permanentPairing n (fun x y => B x y) x y := by
  simp only [leftMultilinear, LinearMap.compMultilinearMap_apply,
    symPowLiftLinear_symMonomial]
  exact permanentPairingMultilinear_apply n B x y

theorem leftMultilinear_symmetric (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → X) :
    leftMultilinear n B (fun i => x (σ i)) = leftMultilinear n B x := by
  apply symPow_linearMap_ext n Y
  intro y
  simp only [leftMultilinear_apply_monomial]
  exact permanentPairing_perm_left n (fun x y => B x y) x y σ

/-- The canonical bilinear pairing induced on homogeneous symmetric powers. -/
def pairing (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    SymPow n X →ₗ[ℂ] Module.Dual ℂ (SymPow n Y) :=
  symPowLift (leftMultilinear n B) (leftMultilinear_symmetric n B)

@[simp] theorem pairing_monomials (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (x : Fin n → X) (y : Fin n → Y) :
    pairing n B (symMonomial n X x) (symMonomial n Y y) =
      permanentPairing n (fun x y => B x y) x y := by
  simp [pairing]

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- The evaluation pairing of a symmetric power and the symmetric power of its dual. -/
def dualMap (n : ℕ) :
    SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V) :=
  pairing n (LinearMap.id : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V)

@[simp] theorem dualMap_monomials (n : ℕ)
    (x : Fin n → Module.Dual ℂ V) (y : Fin n → V) :
    dualMap V n (symMonomial n (Module.Dual ℂ V) x) (symMonomial n V y) =
      permanentPairing n (fun f v => f v) x y := by
  exact pairing_monomials n LinearMap.id x y

theorem dualMap_pure (n : ℕ) (p : SymPow n (Module.Dual ℂ V)) (x : V) :
    dualMap V n p (symMonomial n V (fun _ => x)) =
      SymmetricAlgebra.lift (Module.Dual.eval ℂ V x) p.val := by
  have h : (LinearMap.applyₗ (symMonomial n V (fun _ => x))).comp (dualMap V n) =
      (SymmetricAlgebra.lift (Module.Dual.eval ℂ V x)).toLinearMap.domRestrict
        (symPowSubmodule n (Module.Dual ℂ V)) := by
    apply symPow_linearMap_ext n (Module.Dual ℂ V)
    intro f
    change dualMap V n (symMonomial n (Module.Dual ℂ V) f)
      (symMonomial n V (fun _ => x)) = _
    rw [dualMap_monomials, permanentPairing_const_right]
    simp [symMonomial, symMonomialRaw]
  exact LinearMap.congr_fun h p

theorem dualMap_injective [FiniteDimensional ℂ V] (n : ℕ) :
    Function.Injective (dualMap V n) :=
  symPowDual_injective_of_pure_evaluation V n (dualMap V n) (dualMap_pure V n)

theorem dual_finrank (n : ℕ) [FiniteDimensional ℂ V] :
    Module.finrank ℂ (SymPow n (Module.Dual ℂ V)) =
      Module.finrank ℂ (Module.Dual ℂ (SymPow n V)) := by
  rw [Subspace.dual_finrank_eq]
  let e : Module.Dual ℂ V ≃ₗ[ℂ] V :=
    LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq
  exact (symPowEquiv n e).finrank_eq

/-- Perfect duality for homogeneous symmetric powers in finite dimension. -/
def dualEquiv [FiniteDimensional ℂ V] (n : ℕ) :
    SymPow n (Module.Dual ℂ V) ≃ₗ[ℂ] Module.Dual ℂ (SymPow n V) :=
  (dualMap V n).linearEquivOfInjective (dualMap_injective V n) (dual_finrank V n)

@[simp] theorem dualEquiv_apply [FiniteDimensional ℂ V] (n : ℕ)
    (p : SymPow n (Module.Dual ℂ V)) : dualEquiv V n p = dualMap V n p := rfl

end Problem346.PairingConstruction

end

end OAI


