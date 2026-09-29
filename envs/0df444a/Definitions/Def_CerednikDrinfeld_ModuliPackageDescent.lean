-- Prove2me | Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
-- name    : CerednikDrinfeld_ModuliPackageDescent
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/d76c9aac-bfba-5987-9bb2-d61a703b1fb5
-- title:
--   Morphisms and descent properties of moduli packages
-- statement:
--   Throughout, $p$ is a prime and $O$ a commutative ring. A `ModuliPackage` for $(p,O)$ is the project's notion of a set-valued functor $F$ on pairs $(B,\psi)$ consisting of a commutative ring $B$ with a ring homomorphism $\psi\colon O\to B$ and a witness that $p$ is nilpotent in $B$, with transition maps along ring homomorphisms $f\colon B\to B'$ satisfying $f\circ\psi=\psi'$, together with functoriality as fields. Four notions are introduced for such functors, all at universe level $0$.
--
--   `Hom G H` is a structure whose data is a family `app` of maps $G(B,\psi)\to H(B,\psi)$, one for each object, and whose single further field is the naturality identity: for every $f\colon B\to B'$ with $f\circ\psi=\psi'$, transport along $f$ commutes with `app`. Thus it carries the naturality theorem as a field rather than asserting it separately.
--
--   `IsLimitPreserving F` asks, for every $O$-algebra $B$ with $p$ nilpotent (the structure map being $\mathrm{algebraMap}$): every $x\in F(B)$ is the image of some $x_0\in F(B_0)$ under an $O$-algebra map $B_0\to B$ with $B_0$ of finite presentation over $O$ and $p$ nilpotent in $B_0$; and any two elements of $F(B_0)$, $B_0$ finitely presented, with equal images in $F(B)$ already have equal images in $F(B_1)$ for some finitely presented $O$-algebra $B_1$ with $p$ nilpotent factoring $B_0\to B$.
--
--   `IsEffective F` asks, for every Noetherian local ring $A$ complete for the maximal-ideal-adic topology, equipped with $\psi\colon O\to A$, with $p$ nilpotent in $A$ and in each $A/\mathfrak m^{n+1}$, that the map $F(A)\to\varprojlim_n F(A/\mathfrak m^{n+1})$ be injective and that every system $(y_n)$ compatible under the projections $A/\mathfrak m^{n+2}\to A/\mathfrak m^{n+1}$ be realised by some $x\in F(A)$.
--
--   `IsCompletionSheaf F` asks, for every Noetherian local $B$ with $\psi\colon O\to B$, $p$ nilpotent in $B$, in $\hat B$ and in $\hat B\otimes_B\hat B$ (these nilpotencies being hypotheses), that $F(B)\to F(\hat B)$ be injective and that every $z\in F(\hat B)$ with equal images under the two inclusions $\hat B\rightrightarrows\hat B\otimes_B\hat B$ come from $F(B)$; only this two-fold equaliser condition is imposed, with no condition on the triple tensor product.
--
--   **Relation to Mathlib.** Mathlib has no notion of a functor on nilpotent $O$-algebras of this kind; `ModuliPackage` and the four notions here are the project's own, formulated using Mathlib's `Algebra.FinitePresentation`, `IsAdicComplete`, `AdicCompletion` and tensor products.
--
--   **Where it is used.** These are the standing conditions under which a functor of special formal $O_D$-modules can be compared with a formal model by descent: limit preservation, effectivity at complete local Noetherian rings, and descent along completion of a Noetherian local ring. They are the functorial input to the representability step of the Čerednik–Drinfeld uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_ModuliPackageDescent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld

namespace SpecialFormal

namespace ModuliPackage

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

structure Hom (G H : ModuliPackage.{0, 0} p O) where

  app : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), G.obj B ψ hB → H.obj B ψ hB

  naturality : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (x : G.obj B ψ hB), app B' ψ' hB' (G.map hB hB' f hf x) = H.map hB hB' f hf (app B ψ hB x)

def IsLimitPreserving (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] (hB : IsNilpotent (p : B)),
    (∀ x : F.obj B (algebraMap O B) hB,
      ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra O B₀) (_ : Algebra.FinitePresentation O B₀)
        (hB₀ : IsNilpotent (p : B₀)) (g : B₀ →ₐ[O] B) (x₀ : F.obj B₀ (algebraMap O B₀) hB₀),
        F.map hB₀ hB (g : B₀ →+* B) (g.comp_algebraMap) x₀ = x) ∧
    (∀ (B₀ : Type) [CommRing B₀] [Algebra O B₀] [Algebra.FinitePresentation O B₀]
      (hB₀ : IsNilpotent (p : B₀)) (g : B₀ →ₐ[O] B) (x₀ x₀' : F.obj B₀ (algebraMap O B₀) hB₀),
      F.map hB₀ hB (g : B₀ →+* B) (g.comp_algebraMap) x₀ = F.map hB₀ hB (g : B₀ →+* B) (g.comp_algebraMap) x₀' →
      ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra O B₁) (_ : Algebra.FinitePresentation O B₁)
        (hB₁ : IsNilpotent (p : B₁)) (g₁ : B₀ →ₐ[O] B₁) (h : B₁ →ₐ[O] B) (_ : h.comp g₁ = g),
        F.map hB₀ hB₁ (g₁ : B₀ →+* B₁) (g₁.comp_algebraMap) x₀ =
          F.map hB₀ hB₁ (g₁ : B₀ →+* B₁) (g₁.comp_algebraMap) x₀')

def IsEffective (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (ψ : O →+* A) (hA : IsNilpotent (p : A))
    (hAn : ∀ n : ℕ, IsNilpotent ((p : A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)))),
    (∀ x x' : F.obj A ψ hA,
      (∀ n : ℕ, F.map hA (hAn n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) rfl x =
        F.map hA (hAn n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) rfl x') → x = x') ∧
    (∀ y : ∀ n : ℕ, F.obj (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))).comp ψ) (hAn n),
      (∀ n : ℕ, F.map (hAn (n + 1)) (hAn n)
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (by
            ext a; rfl) (y (n + 1)) = y n) →
      ∃ x : F.obj A ψ hA, ∀ n : ℕ,
        F.map hA (hAn n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) rfl x = y n)

open scoped TensorProduct in

def IsCompletionSheaf (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (hBc : IsNilpotent (p : AdicCompletion (IsLocalRing.maximalIdeal B) B))
    (hBcc : IsNilpotent (p : (AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B]
      (AdicCompletion (IsLocalRing.maximalIdeal B) B))),
    (∀ x x' : F.obj B ψ hB,
      F.map hB hBc (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) rfl x =
        F.map hB hBc (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) rfl x' → x = x') ∧
    (∀ z : F.obj (AdicCompletion (IsLocalRing.maximalIdeal B) B)
        ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp ψ) hBc,
      F.map (ψ' := (algebraMap B ((AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B]
          (AdicCompletion (IsLocalRing.maximalIdeal B) B))).comp ψ) hBc hBcc
          ((Algebra.TensorProduct.includeLeft :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →ₐ[B]
              (AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B] (AdicCompletion (IsLocalRing.maximalIdeal B) B)) :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →+* _)
          (by ext b; simp [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]) z =
        F.map (ψ' := (algebraMap B ((AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B]
          (AdicCompletion (IsLocalRing.maximalIdeal B) B))).comp ψ) hBc hBcc
          ((Algebra.TensorProduct.includeRight :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →ₐ[B]
              (AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B] (AdicCompletion (IsLocalRing.maximalIdeal B) B)) :
            AdicCompletion (IsLocalRing.maximalIdeal B) B →+* _)
          (by ext b; simp [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_one_eq_one_tmul]) z →
      ∃ x : F.obj B ψ hB,
        F.map hB hBc (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) rfl x = z)

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld


