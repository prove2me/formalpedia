-- Prove2me | Definitions.Def_ModularCurve_LevelModuliPackage
-- name    : ModularCurve_LevelModuliPackage
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/3d53287b-4a27-5980-b451-269bf5593785
-- title:
--   Level moduli data, problem automorphisms, and representing packages
-- statement:
--   Fix a commutative ring $A$. A `LevelModuliDatum` over $A$ is a bundle of data in universe $u$: for each commutative $A$-algebra $T$ a type `Pt T` of "level structures over $T$"; for each $A$-algebra homomorphism $f : T \to T'$ a map `map f : Pt T → Pt T'`; fields `map_id` and `map_comp` asserting that this is functorial (identity to identity, $g \circ f$ to `map g ∘ map f`, written in Lean with `g.comp f`); a $j$-coordinate `jOf : Pt T → T`; and a field `jOf_map` asserting naturality, $jOf(\mathrm{map}\ f\ x) = f(jOf\ x)$. Functoriality is thus spelled out as structure fields rather than through a functor object.
--
--   A `ProblemAut` of a datum $D$ is a family of self-maps `act : D.Pt T → D.Pt T`, natural in $T$ and preserving `jOf`; no inverse is required, so these are natural endomorphisms of the pointed functor, composed by `ProblemAut.comp` with unit `ProblemAut.id`. For a ring automorphism $\sigma_A$ of $A$, `Twist σA T` is $T$ again as a ring, but with $A$-algebra structure $a \mapsto \mathrm{algebraMap}(\sigma_A a)$; `AlgHom.twist` carries an $A$-algebra map to the twists via the same underlying ring map. A `SemilinearProblemAut` of $D$ over $\sigma_A$ is a family `act : D.Pt T → D.Pt (Twist σA T)`, natural with respect to twisted maps, with $jOf$ preserved as an equality of elements of $T$.
--
--   Given a field $K$ with an $A$-algebra structure, an element $j \in K$ and a datum $D$, a `LevelModuliPackage` consists of an $A$-subalgebra $B \subseteq K$ with $j \in B$, a point `univ ∈ D.Pt B` whose $j$-coordinate is $j$, and the representability field: for every commutative $A$-algebra $T$ and every $x \in D.Pt\ T$ there is a unique $A$-algebra map $\varphi : B \to T$ with $\mathrm{map}\ \varphi\ (\mathrm{univ}) = x$, i.e. $\mathrm{Hom}_{A\text{-alg}}(B,T) \cong D(T)$ via the universal point.
--
--   The remaining declarations exploit this: `classify` picks the classifying map of a point, with `map_classify` and `classify_unique` its defining properties; `inducedEnd σ` is the $A$-algebra endomorphism of $B$ classifying $\sigma.\mathrm{act}(\mathrm{univ})$ for a problem automorphism $\sigma$, characterised by `map_inducedEnd_univ`, and `algHom_eq_of_map_univ_eq` says that an $A$-algebra endomorphism of $B$ is determined by its effect on the universal point; `inducedSemiEnd` is the corresponding ring endomorphism of $B$ attached to a $\sigma_A$-semilinear problem automorphism, which by `inducedSemiEnd_algebraMap` acts on scalars from $A$ through $\sigma_A$.
--
--   **Relation to Mathlib.** Mathlib has no notion of a moduli problem of elliptic curves with level structure or of its representability by a ring; this axiomatisation is the project's own, built on Mathlib's `Subalgebra`, `AlgHom` and `RingEquiv`.
--
--   **Where it is used.** The datum is deliberately generic in the level structure, so that the $\Gamma_0(p)$ situation and the full level-$q$ situation each instantiate it by supplying their own notion of level structure; a package then presents the $j$-finite chart algebra of an integral model of a modular curve as the ring representing that moduli problem, with the universal level structure over it. The induced linear and $\sigma_A$-semilinear endomorphisms are what turn automorphisms of the moduli problem, and inertia acting coefficientwise over ramified bases, into endomorphisms of the chart ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelModuliPackage.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve

structure LevelModuliDatum (A : Type u) [CommRing A] where

  Pt : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → Pt T → Pt T'

  map_id : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : Pt T), map (AlgHom.id A T) x = x

  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : Pt T), map (g.comp f) x = map g (map f x)

  jOf : {T : Type u} → [CommRing T] → [Algebra A T] → Pt T → T

  jOf_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : Pt T),
    jOf (map f x) = f (jOf x)

namespace LevelModuliDatum

variable {A : Type u} [CommRing A]

structure ProblemAut (D : LevelModuliDatum.{u} A) where

  act : {T : Type u} → [CommRing T] → [Algebra A T] → D.Pt T → D.Pt T

  act_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : D.Pt T),
    act (D.map f x) = D.map f (act x)

  jOf_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T), D.jOf (act x) = D.jOf x

def ProblemAut.id (D : LevelModuliDatum.{u} A) : ProblemAut D where
  act x := x
  act_map _ _ := rfl
  jOf_act _ := rfl

def ProblemAut.comp {D : LevelModuliDatum.{u} A} (σ τ : ProblemAut D) : ProblemAut D where
  act x := σ.act (τ.act x)
  act_map f x := by rw [τ.act_map, σ.act_map]
  jOf_act x := by rw [σ.jOf_act, τ.jOf_act]

def Twist (_σA : A ≃+* A) (T : Type u) : Type u := T

instance Twist.instCommRing (σA : A ≃+* A) (T : Type u) [CommRing T] : CommRing (Twist σA T) :=
  inferInstanceAs (CommRing T)

instance Twist.instAlgebra (σA : A ≃+* A) (T : Type u) [CommRing T] [Algebra A T] : Algebra A (Twist σA T) :=
  ((algebraMap A T).comp σA.toRingHom).toAlgebra

theorem Twist.algebraMap_apply (σA : A ≃+* A) (T : Type u) [CommRing T] [Algebra A T] (a : A) :
    (algebraMap A (Twist σA T) a : T) = algebraMap A T (σA a) := rfl

def AlgHom.twist (σA : A ≃+* A) {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') : Twist σA T →ₐ[A] Twist σA T' where
  toRingHom := (f.toRingHom : T →+* T')
  commutes' a := f.commutes (σA a)

structure SemilinearProblemAut (D : LevelModuliDatum.{u} A) (σA : A ≃+* A) where

  act : {T : Type u} → [CommRing T] → [Algebra A T] → D.Pt T → D.Pt (Twist σA T)

  act_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : D.Pt T),
    act (D.map f x) = D.map (AlgHom.twist σA f) (act x)

  jOf_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T),
    @Eq T (D.jOf (T := Twist σA T) (act x)) (D.jOf x)

end LevelModuliDatum

structure LevelModuliPackage (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K)
    (D : LevelModuliDatum.{u} A) where

  B : Subalgebra A K

  j_mem : j ∈ B

  univ : D.Pt ↥B

  jOf_univ : (D.jOf univ : ↥B) = ⟨j, j_mem⟩

  represents : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : D.Pt T), ∃! φ : ↥B →ₐ[A] T, D.map φ univ = x

namespace LevelModuliPackage

variable {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K] {j : K} {D : LevelModuliDatum.{u} A}
  (P : LevelModuliPackage A K j D)

noncomputable def classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : ↥P.B →ₐ[A] T :=
  (P.represents T x).choose

theorem map_classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : D.map (P.classify x) P.univ = x :=
  (P.represents T x).choose_spec.1

theorem classify_unique {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) (φ : ↥P.B →ₐ[A] T)
    (h : D.map φ P.univ = x) : φ = P.classify x :=
  (P.represents T x).unique h (P.map_classify x) ▸ rfl

noncomputable def inducedEnd (σ : LevelModuliDatum.ProblemAut D) : ↥P.B →ₐ[A] ↥P.B := P.classify (σ.act P.univ)

theorem map_inducedEnd_univ (σ : LevelModuliDatum.ProblemAut D) : D.map (P.inducedEnd σ) P.univ = σ.act P.univ :=
  P.map_classify _

theorem algHom_eq_of_map_univ_eq (φ ψ : ↥P.B →ₐ[A] ↥P.B) (h : D.map φ P.univ = D.map ψ P.univ) : φ = ψ :=
  (P.classify_unique (D.map ψ P.univ) φ h).trans (P.classify_unique (D.map ψ P.univ) ψ rfl).symm

noncomputable def inducedSemiEnd {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) : ↥P.B →+* ↥P.B :=
  ((P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)).toRingHom :
    ↥P.B →+* LevelModuliDatum.Twist σA ↥P.B)

theorem inducedSemiEnd_algebraMap {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) (a : A) :
    P.inducedSemiEnd σ (algebraMap A ↥P.B a) = algebraMap A ↥P.B (σA a) :=
  (P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)).commutes a

theorem map_inducedSemiEnd_univ {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) :
    D.map (P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)) P.univ = σ.act P.univ :=
  P.map_classify _

end LevelModuliPackage

end ModularCurve


