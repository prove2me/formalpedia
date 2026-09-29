-- Prove2me | Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization
-- name    : ModularCurve_FullLevelCuspidalSpecialization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2cf31e36-b8c7-55f3-8449-3465917e7502
-- title:
--   Cuspidal specialisation of full-level Jacobians into Drinfeld Tate modules
-- statement:
--   Throughout, $q$ and $M'$ are naturals, $\lambda$ is a prime and $k$ is a field whose Drinfeld coordinate ring [`DrinfeldCurve.CoordRing q k`](../def/DrinfeldCurve_CoordRing.html#L21) is a domain. Here $\mathrm{Jac}(q,M')$ is the product $\prod_{\zeta} J_H(q^2M')$ over the set $\mathrm{Idx}_q$ of primitive $q$-th roots of unity in $\overline{\mathbb Q}$, where $J_H$ is the degree-zero divisor class group attached to the level-$q^2M'$ curve with $H$ the kernel of $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, and $V(A) = \mathbb Q_\lambda \otimes_{\mathbb Z_\lambda} T_\lambda(A)$ denotes the rational $\lambda$-adic Tate module. First, `ratCoord` takes a $\mathbb Z_\lambda$-linear equivalence $\Psi : T_\lambda(\mathrm{Jac}(q,M')) \simeq \prod_{\zeta} T_\lambda(J_H(q^2M'))$ and a root of unity $\zeta$, and returns the base change to $\mathbb Q_\lambda$ of $\Psi$ followed by the projection to the $\zeta$-factor; on elementary tensors it sends $a \otimes x$ to $a \otimes \Psi(x)_\zeta$.
--
--   Next, `componentSpecialization` assembles, from such a $\Psi$, a subspace $V^{\mathrm{inv}} \subseteq V(J_H(q^2M'))$ with a linear map $e_{\mathrm{inv}}$ onto it, a linear map $\mathrm{red} : V^{\mathrm{inv}} \to \prod_{i<n} Y_i$ into a finite family of $\mathbb Q_\lambda$-spaces, an index map $c : T \to \mathrm{Fin}\,n$ and linear maps $\Phi_{\zeta,t} : Y_{c(t)} \to V(\mathrm{Pic}^0_k(F_{\mathrm{Dr}}))$ into the rational Tate module of the degree-zero class group of the Drinfeld function field over $k$, the $\mathbb Q_\lambda$-linear map into the product indexed by $\mathrm{Idx}_q \times T$ whose $(\zeta,t)$-component is $v \mapsto 1 \otimes \Phi_{\zeta,t}\bigl(\mathrm{red}(e_{\mathrm{inv}}(\mathrm{ratCoord}_\zeta v))_{c(t)}\bigr)$. Then `cuspidalSpecialization` is this map precomposed with a further linear endomorphism $e_C$ of $V(\mathrm{Jac}(q,M'))$. These are purely formal constructions: no idempotency, equivariance or injectivity is demanded of $e_C$, $e_{\mathrm{inv}}$, $\mathrm{red}$ or $\Phi$, such properties being the subject of separate statements. The accompanying lemmas record the componentwise formulas, the composite with a projection, invariance of the value under agreement of $e_C v$ (in particular vanishing when $e_C v = 0$), and the criterion that the specialisation of $v$ vanishes precisely when $\Phi_{\zeta,t}(\mathrm{red}(e_{\mathrm{inv}}(\mathrm{ratCoord}_\zeta v))_{c(t)}) = 0$ for all $(\zeta,t)$, using that $x \mapsto 1 \otimes x$ over $\mathbb Q_\lambda$ is injective.
--
--   **Relation to Mathlib.** Mathlib has no notion of such specialisation maps; they are the project's own, built from Mathlib's base change of linear maps, products of linear maps and the tensor-product inclusion $x \mapsto 1 \otimes x$.
--
--   **Where it is used.** The maps defined here are the $\lambda$-adic specialisation, along the components of the full-level-$q$ Jacobian and along a chosen family of reduced components, into the Tate module of the Drinfeld curve; they provide the target for the equivariance and injectivity statements used in the study of the mod-$q$ behaviour of the Galois representations attached to level $q^2M'$, as in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelCuspidalSpecialization.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve.FullLevel

section Coord

variable (q : ℕ) (M' : ℕ) (lam : ℕ) [Fact lam.Prime]

def ratCoord (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (ζ : Idx q) :
    RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (jacComp q M') :=
  ((LinearMap.proj ζ : (Idx q → TateModule lam (jacComp q M')) →ₗ[ℤ_[lam]] TateModule lam (jacComp q M')) ∘ₗ
      Ψ.toLinearMap).baseChange ℚ_[lam]

@[simp] theorem ratCoord_tmul
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (ζ : Idx q) (a : ℚ_[lam]) (x : TateModule lam (Jac q M')) :
    ratCoord q M' lam Ψ ζ (a ⊗ₜ x) = a ⊗ₜ Ψ x ζ :=
  rfl

end Coord

section Specialization

variable (q : ℕ) (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (k : Type) [Field k] [IsDomain (DrinfeldCurve.CoordRing q k)]

def componentSpecialization
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) :
    RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] DrinfeldCurve.tateProd q k lam ℚ_[lam] (Idx q × T) :=
  LinearMap.pi fun p =>
    TensorProduct.mk ℚ_[lam] ℚ_[lam]
        (RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) 1 ∘ₗ
      Φ p.1 p.2 ∘ₗ LinearMap.proj (c p.2) ∘ₗ red ∘ₗ eInv ∘ₗ ratCoord q M' lam Ψ p.1

def cuspidalSpecialization
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) :
    RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] DrinfeldCurve.tateProd q k lam ℚ_[lam] (Idx q × T) :=
  componentSpecialization q M' lam k Ψ Vinv eInv red c Φ ∘ₗ eC

variable
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))))

@[simp] theorem componentSpecialization_apply (v : RationalTateModule lam (Jac q M')) (p : Idx q × T) :
    componentSpecialization q M' lam k Ψ Vinv eInv red c Φ v p =
      (1 : ℚ_[lam]) ⊗ₜ Φ p.1 p.2 (red (eInv (ratCoord q M' lam Ψ p.1 v)) (c p.2)) :=
  rfl

theorem cuspidalSpecialization_apply' (v : RationalTateModule lam (Jac q M')) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v =
      componentSpecialization q M' lam k Ψ Vinv eInv red c Φ (eC v) :=
  rfl

@[simp] theorem cuspidalSpecialization_apply (v : RationalTateModule lam (Jac q M')) (p : Idx q × T) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v p =
      (1 : ℚ_[lam]) ⊗ₜ Φ p.1 p.2 (red (eInv (ratCoord q M' lam Ψ p.1 (eC v))) (c p.2)) :=
  rfl

theorem proj_comp_cuspidalSpecialization (p : Idx q × T) :
    LinearMap.proj p ∘ₗ cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ =
      TensorProduct.mk ℚ_[lam] ℚ_[lam]
          (RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) 1 ∘ₗ
        Φ p.1 p.2 ∘ₗ LinearMap.proj (c p.2) ∘ₗ red ∘ₗ eInv ∘ₗ ratCoord q M' lam Ψ p.1 ∘ₗ eC :=
  rfl

theorem cuspidalSpecialization_apply_eq_of_apply_eq (v w : RationalTateModule lam (Jac q M'))
    (h : eC v = eC w) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v =
      cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ w :=
  congrArg (componentSpecialization q M' lam k Ψ Vinv eInv red c Φ) h

theorem cuspidalSpecialization_apply_of_apply_eq_self (v : RationalTateModule lam (Jac q M'))
    (hv : eC v = v) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v =
      componentSpecialization q M' lam k Ψ Vinv eInv red c Φ v :=
  congrArg (componentSpecialization q M' lam k Ψ Vinv eInv red c Φ) hv

theorem cuspidalSpecialization_apply_eq_zero_of_apply_eq_zero (v : RationalTateModule lam (Jac q M'))
    (hv : eC v = 0) : cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v = 0 :=
  (congrArg (componentSpecialization q M' lam k Ψ Vinv eInv red c Φ) hv).trans
    (LinearMap.map_zero _)

theorem componentSpecialization_apply_eq_zero_iff (v : RationalTateModule lam (Jac q M')) :
    componentSpecialization q M' lam k Ψ Vinv eInv red c Φ v = 0 ↔
      ∀ (ζ : Idx q) (t : T), Φ ζ t (red (eInv (ratCoord q M' lam Ψ ζ v)) (c t)) = 0 := by
  have key : ∀ x : RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)),
      TensorProduct.mk ℚ_[lam] ℚ_[lam] _ 1 x = 0 ↔ x = 0 := fun x =>
    (TensorProduct.lid ℚ_[lam] _).symm.map_eq_zero_iff
  constructor
  · intro h ζ t
    exact (key _).mp (congrFun h (ζ, t))
  · intro h
    funext p
    exact (key _).mpr (h p.1 p.2)

theorem cuspidalSpecialization_apply_eq_zero_iff (v : RationalTateModule lam (Jac q M')) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ v = 0 ↔
      ∀ (ζ : Idx q) (t : T), Φ ζ t (red (eInv (ratCoord q M' lam Ψ ζ (eC v))) (c t)) = 0 :=
  componentSpecialization_apply_eq_zero_iff q M' lam k Ψ Vinv eInv red c Φ (eC v)

end Specialization

end ModularCurve.FullLevel

end


