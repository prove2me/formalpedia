-- Prove2me | Definitions.Def_Mathlib_Algebra_Algebra_Hom
-- name    : Mathlib_Algebra_Algebra_Hom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/0e22fe47-ff36-54d7-9480-e4e09bd3b71c
-- title:
--   Semialgebra homomorphisms over a ring homomorphism of base rings
-- statement:
--   Fix commutative semirings $R$, $S$, a ring homomorphism $\varphi : R \to S$, a semiring $A$ that is an $R$-algebra and a semiring $B$ that is an $S$-algebra. The structure [`SemialgHom φ A B`](../def/Mathlib_Algebra_Algebra_Hom.html#L11), written `A →ₛₐ[φ] B`, is defined as a structure extending both the $\varphi$-semilinear maps `A →ₛₗ[φ] B` and the ring homomorphisms `RingHom A B`: an element is thus a function $\psi : A \to B$ that is additive, multiplicative, unital, and satisfies $\psi(r \cdot a) = \varphi(r)\cdot\psi(a)$ for $r \in R$, $a \in A$. The `FunLike` instance makes such a $\psi$ act as a function and records that the underlying function determines $\psi$, and the companion class [`SemialgHomClass F φ A B`](../def/Mathlib_Algebra_Algebra_Hom.html#L47) is the conjunction of `SemilinearMapClass F φ A B` and `RingHomClass F A B`, with the bundled type `A →ₛₐ[φ] B` an instance and a coercion from any member of the class to the bundled type.
--
--   The lemmas record the defining semilinearity $\psi(m \cdot x) = \varphi(m)\cdot\psi(x)$, the compatibility with structure maps, $\psi(\mathrm{algebraMap}_{R,A}(r)) = \mathrm{algebraMap}_{S,B}(\varphi(r))$, and, when $A$ and $B$ are commutative, that the structure map of the $A$-algebra structure on $B$ induced by $\psi$ is $\psi$ itself. The constructions are: composition $B \to C$ after $A \to B$ along a compatible triple of base ring homomorphisms $\varphi$, $\psi$, $\xi$; the view of an $R$-algebra homomorphism as a semialgebra homomorphism over $\mathrm{id}_R$, and composition of a semialgebra homomorphism with an algebra homomorphism; the product map $A \to B \times C$ of two semialgebra homomorphisms over the same $\varphi$ and the induced map $A \times B \to C \times D$; and restriction of scalars, which turns a semialgebra homomorphism over the ring homomorphism underlying some $\psi : R' \to_{ₛₐ[\varphi]} S'$ into one over $\varphi$, in the presence of scalar towers $R \to R' \to A$ and $S \to S' \to B$.
--
--   **Relation to Mathlib.** Built on Mathlib's semilinear maps `A →ₛₗ[φ] B` and `RingHom`; it provides the "semi" analogue of Mathlib's `AlgHom`, in which the base rings of source and target are linked by a ring homomorphism rather than being equal, together with the corresponding morphism class and basic API.
--
--   **Where it is used.** This is general algebraic infrastructure for comparing algebras whose base rings are related by a ring homomorphism, so that a single bundled morphism type covers maps lying above a change of coefficient ring.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Algebra/Algebra/Hom.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri; `FLT/Mathlib/Topology/Algebra/Algebra/Hom.lean` — © 2026 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

section semialghom

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).
-/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B

/-- Reinterpret a `SemialgHom` as a `RingHom`. -/
add_decl_doc SemialgHom.toRingHom

@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => SemialgHom _

@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

variable {φ} {A} {B} in
lemma SemialgHom.map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x

@[simp]
theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : A →ₛₐ[φ] B) : A → B) = f :=
  rfl

end semialghom

section semialghomclass

class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

variable {F} {φ} {A} {B} in

def SemialgHomClass.toSemialgHom (f : F) : A →ₛₐ[φ] B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }

instance : CoeTC F (A →ₛₐ[φ] B) :=
  ⟨SemialgHomClass.toSemialgHom⟩

@[simp]
theorem SemialgHom.coe_coe (f : F) : ⇑(f : A →ₛₐ[φ] B) = f :=
  rfl

end semialghomclass

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

lemma SemialgHom.commutes (ψ : A →ₛₐ[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) := by
  have := ψ.map_smul r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]

theorem SemialgHom.toLinearMap_eq_coe (f : A →ₛₐ[φ] B) : f.toLinearMap = f :=
  rfl

theorem SemialgHom.toRingHom_eq_coe (f : A →ₛₐ[φ] B) : f.toRingHom = f :=
  rfl

theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra S B] (f : A →ₛₐ[φ] B) (a : A) :
    letI := f.toAlgebra
    algebraMap A B a = f a := rfl

def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
    (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B) :
    A →ₛₐ[ξ] C where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom

def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    A →ₛₐ[RingHom.id R] B where
  __ := f
  map_smul' _ _ := by simp

def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} [Algebra S A] (g : B →ₛₐ[ψ] C) (f : A →ₐ[S] B) :
    A →ₛₐ[ψ] C :=
  g.comp f.toSemialgHom

def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : A →ₛₐ[φ] B)
    (g : A →ₛₐ[φ] C) :
    A →ₛₐ[φ] B × C where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp

def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R B] (f : A →ₛₐ[φ] C) (g : B →ₛₐ[φ] D) :
    A × B →ₛₐ[φ] C × D :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))

@[simps!]
def SemialgHom.restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S}
    (ψ : R' →ₛₐ[φ] S') {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [Algebra R' A] [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B]
    (f : A →ₛₐ[ψ.toRingHom] B) : A →ₛₐ[φ] B where
  __ := f.toRingHom
  map_smul' r a := by
    have := f.map_smul (algebraMap R R' r) a
    simp_all [SemialgHom.toLinearMap_eq_coe, Algebra.algebraMap_eq_smul_one, ψ.map_smul]

end semialghom


