-- Prove2me | Definitions.Def_GroupCohomology_CochainCup
-- name    : GroupCohomology_CochainCup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/9cb67203-ed0b-5168-96e8-fea00cf83172
-- title:
--   Cup product of inhomogeneous cochains for group cohomology
-- statement:
--   Over a commutative ring $k$ and a group $G$, for two $k$-linear representations $A$, $B$ of $G$ (objects of `Rep k G`) and natural numbers $p$, $q$, this module defines the cochain-level cup product on the carriers of Mathlib's inhomogeneous cochain complex, whose degree-$n$ term is the module of all functions $(\mathrm{Fin}\,n \to G) \to A$. Two abbreviations record the splitting of a tuple $\sigma : \mathrm{Fin}(p+q) \to G$ into its first $p$ entries, `cochainCupFst p q σ`, and its last $q$ entries, `cochainCupSnd p q σ`, via `Fin.castAdd` and `Fin.natAdd`. The main definition `cochainCup A B p q` is then a $k$-bilinear map
--   $$((\mathrm{Fin}\,p \to G) \to A) \times ((\mathrm{Fin}\,q \to G) \to B) \longrightarrow ((\mathrm{Fin}(p+q) \to G) \to (A \otimes B)),$$
--   with target the underlying module of the tensor product representation $A \otimes B$ in `Rep k G`, sending $f, g$ to the cochain
--   $$\sigma \mapsto f(\sigma_1,\dots,\sigma_p) \otimes_k \bigl(\sigma_1\cdots\sigma_p\bigr)\cdot g(\sigma_{p+1},\dots,\sigma_{p+q}),$$
--   where the group element acting on the second factor is the total partial product `Fin.partialProd (cochainCupFst p q σ) (Fin.last p)` of the first $p$ entries, acting through the representation map `B.ρ`. Bilinearity in each argument comes from additivity and homogeneity of the tensor product together with linearity of $\rho$. The accompanying lemma `cochainCup_apply` records this defining formula for the value at a tuple $\sigma$. The module contains data only: no cocycle or Leibniz property is asserted here.
--
--   **Relation to Mathlib.** Mathlib has no cup product for group cohomology; this is the project's own definition, formulated directly on Mathlib's `Rep k G` and on the carriers $(\mathrm{Fin}\,n \to G) \to A$ of Mathlib's inhomogeneous cochain complex, with values in Mathlib's monoidal tensor product of representations.
--
--   **Where it is used.** This cochain-level product is the basis for the cup product on group cohomology used in the Galois-cohomological input to the modularity argument, in particular for the cup product pairings of local Tate duality in degrees $(1,1)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_CochainCup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)

abbrev cochainCupFst (σ : Fin (p + q) → G) : Fin p → G := fun i => σ (Fin.castAdd q i)

abbrev cochainCupSnd (σ : Fin (p + q) → G) : Fin q → G := fun j => σ (Fin.natAdd p j)

noncomputable def cochainCup :
    ((Fin p → G) → A) →ₗ[k] ((Fin q → G) → B) →ₗ[k] ((Fin (p + q) → G) → (A ⊗ B : Rep k G)) :=
  LinearMap.mk₂ k
    (fun f g σ => f (cochainCupFst p q σ) ⊗ₜ[k] B.ρ (Fin.partialProd (cochainCupFst p q σ) (Fin.last p)) (g (cochainCupSnd p q σ)))
    (fun f₁ f₂ g => funext fun σ => by simp only [Pi.add_apply, TensorProduct.add_tmul])
    (fun c f g => funext fun σ => by simp only [Pi.smul_apply, TensorProduct.smul_tmul'])
    (fun f g₁ g₂ => funext fun σ => by simp only [Pi.add_apply, map_add, TensorProduct.tmul_add])
    (fun c f g => funext fun σ => by simp only [Pi.smul_apply, map_smul, TensorProduct.tmul_smul])

theorem cochainCup_apply (f : (Fin p → G) → A) (g : (Fin q → G) → B) (σ : Fin (p + q) → G) :
    cochainCup A B p q f g σ
      = f (cochainCupFst p q σ) ⊗ₜ[k] B.ρ (Fin.partialProd (cochainCupFst p q σ) (Fin.last p)) (g (cochainCupSnd p q σ)) := rfl

end groupCohomology


