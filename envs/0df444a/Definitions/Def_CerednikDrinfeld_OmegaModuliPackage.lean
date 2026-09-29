-- Prove2me | Definitions.Def_CerednikDrinfeld_OmegaModuliPackage
-- name    : CerednikDrinfeld_OmegaModuliPackage
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/37214dcb-dcc4-5530-9773-f70e528fe0a9
-- title:
--   Moduli packages from algebra-valued functors; the Omega package
-- statement:
--   Throughout, $\mathcal O$ and $O$ are commutative rings and $c\colon\mathcal O\to O$ a ring homomorphism. The first construction, `AlgFunctor.algHomOfComp`, takes rings $B,B'$ equipped with ring homomorphisms $\psi\colon O\to B$, $\psi'\colon O\to B'$ and a ring homomorphism $f\colon B\to B'$ with $f\circ\psi=\psi'$, and views $f$ as an $\mathcal O$-algebra homomorphism for the $\mathcal O$-algebra structures on $B$ and $B'$ given by $\psi\circ c$ and $\psi'\circ c$; two further lemmas record that its underlying function and underlying ring homomorphism are $f$ itself.
--
--   The main construction, `AlgFunctor.toModuliPackage`, converts a functor $F$ on commutative $\mathcal O$-algebras — an `AlgFunctor 𝒪`, i.e. a structure consisting of an assignment $B\mapsto F(B)$ on commutative rings carrying an $\mathcal O$-algebra structure, a map $F(B)\to F(B')$ for each $\mathcal O$-algebra homomorphism $B\to B'$, and the identity and composition laws as fields — into a `ModuliPackage p O` for a prime $p$: its value at a triple consisting of a commutative ring $B$, a ring homomorphism $\psi\colon O\to B$ and a proof that $p$ is nilpotent in $B$ is $F(B)$, computed for the $\mathcal O$-algebra structure $\psi\circ c$, and its transition map along a ring homomorphism $f\colon B\to B'$ with $f\circ\psi=\psi'$ is $F$ applied to $f$ regarded as an $\mathcal O$-algebra homomorphism as above; the package's identity and composition laws are inherited from those of $F$.
--
--   Finally, for a field $K$ that is an $\mathcal O$-algebra and an element $\pi\in\mathcal O$, `omegaPackage` is this construction applied to the functor `Omega K π`. Two unfolding lemmas identify its value at $(B,\psi)$ with `OmegaObj`, that is with the type of Deligne data over $B$ for $(\mathcal O,K,\pi)$ relative to the structure $\psi\circ c$ — a structure assigning to each full lattice $M\subset K^2$ a $B$-submodule `line M` of $B\otimes_{\mathcal O}M$ with invertible quotient, subject to monotonicity under inclusions of lattices, equivariance under homothety and a nondegeneracy condition at each prime of $B$ — and identify its transition maps with `DeligneDatum.map`.
--
--   **Relation to Mathlib.** Mathlib has no formal upper half plane, Deligne data or moduli of special formal modules; `AlgFunctor` and `ModuliPackage` are the project's own presentations of functors of points, the first carrying the $\mathcal O$-algebra structure as a typeclass instance and the second carrying the structure morphism $\psi\colon O\to B$ explicitly, and this module is the translation between them. `algHomOfComp` is a repackaging of a Mathlib `RingHom` as a Mathlib `AlgHom`.
--
--   **Where it is used.** These definitions belong to the formalisation of the Čerednik–Drinfeld uniformisation of Shimura curves: Drinfeld's moduli problem for special formal modules is formulated over rings with an explicit structure morphism from $O$ in which $p$ is nilpotent, whereas the formal upper half plane is presented as a functor on $\mathcal O$-algebras, and this adapter lets the two be compared along a chosen $c\colon\mathcal O\to O$, so that statements about moduli packages can be applied to the functor of Deligne data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_OmegaModuliPackage.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

namespace FormalOmega

namespace AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O]

def algHomOfComp (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B')
    (f : B →+* B') (hf : f.comp ψ = ψ') :
    letI := (ψ.comp c).toAlgebra; letI := (ψ'.comp c).toAlgebra; B →ₐ[𝒪] B' :=
  letI := (ψ.comp c).toAlgebra; letI := (ψ'.comp c).toAlgebra
  { toRingHom := f
    commutes' := fun r => by
      show f (ψ (c r)) = ψ' (c r)
      rw [← hf]
      rfl }

@[simp] theorem algHomOfComp_apply (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B)
    (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ') (b : B) :
    algHomOfComp c ψ ψ' f hf b = f b := rfl

theorem coe_algHomOfComp (c : 𝒪 →+* O) {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B)
    (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ') :
    (algHomOfComp c ψ ψ' f hf : B →+* B') = f := rfl

def toModuliPackage (p : ℕ) [Fact p.Prime] (F : AlgFunctor 𝒪) (c : 𝒪 →+* O) :
    CerednikDrinfeld.SpecialFormal.ModuliPackage.{0, 0} p O where
  obj B _ ψ _ := @AlgFunctor.obj 𝒪 _ F B _ (ψ.comp c).toAlgebra
  map {B B'} _ _ {ψ ψ'} _ _ f hf x :=
    @AlgFunctor.map 𝒪 _ F B _ (ψ.comp c).toAlgebra B' _ (ψ'.comp c).toAlgebra (algHomOfComp c ψ ψ' f hf) x
  map_id {B} _ {ψ} _ x := by
    letI := (ψ.comp c).toAlgebra
    have h : algHomOfComp c ψ ψ (RingHom.id B) (RingHom.id_comp ψ) = AlgHom.id 𝒪 B := AlgHom.ext fun _ => rfl
    show F.map (algHomOfComp c ψ ψ (RingHom.id B) (RingHom.id_comp ψ)) x = x
    rw [h]
    exact F.map_id x
  map_comp {B B' B''} _ _ _ {ψ ψ' ψ''} _ _ _ g f hf hg x := by
    letI := (ψ.comp c).toAlgebra; letI := (ψ'.comp c).toAlgebra; letI := (ψ''.comp c).toAlgebra
    have h : algHomOfComp c ψ ψ'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) =
        (algHomOfComp c ψ' ψ'' g hg).comp (algHomOfComp c ψ ψ' f hf) := AlgHom.ext fun _ => rfl
    show F.map (algHomOfComp c ψ ψ'' (g.comp f) _) x =
      F.map (algHomOfComp c ψ' ψ'' g hg) (F.map (algHomOfComp c ψ ψ' f hf) x)
    rw [h]
    exact F.map_comp _ _ x

@[simp] theorem toModuliPackage_obj (p : ℕ) [Fact p.Prime] (F : AlgFunctor 𝒪) (c : 𝒪 →+* O)
    (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    (F.toModuliPackage p c).obj B ψ hB = @AlgFunctor.obj 𝒪 _ F B _ (ψ.comp c).toAlgebra := rfl

theorem toModuliPackage_map (p : ℕ) [Fact p.Prime] (F : AlgFunctor 𝒪) (c : 𝒪 →+* O)
    {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (x : (F.toModuliPackage p c).obj B ψ hB) :
    (F.toModuliPackage p c).map hB hB' f hf x =
      @AlgFunctor.map 𝒪 _ F B _ (ψ.comp c).toAlgebra B' _ (ψ'.comp c).toAlgebra (algHomOfComp c ψ ψ' f hf) x := rfl

end AlgFunctor

def omegaPackage {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O) :
    CerednikDrinfeld.SpecialFormal.ModuliPackage.{0, 0} p O :=
  (Omega K π).toModuliPackage p c

theorem omegaPackage_obj {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O) (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    (omegaPackage (K := K) p π c).obj B ψ hB = @OmegaObj 𝒪 _ K _ _ π B _ (ψ.comp c).toAlgebra := rfl

theorem omegaPackage_map {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O)
    {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (d : (omegaPackage (K := K) p π c).obj B ψ hB) :
    (omegaPackage (K := K) p π c).map hB hB' f hf d =
      @DeligneDatum.map 𝒪 _ K _ _ π B _ (ψ.comp c).toAlgebra B' _ (ψ'.comp c).toAlgebra
        (AlgFunctor.algHomOfComp c ψ ψ' f hf) d := rfl

end FormalOmega

end CerednikDrinfeld

end


