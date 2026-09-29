-- Prove2me | Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
-- name    : GoodReductionJacobian_RelativeGroupLawKernel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/d2a40321-970a-525e-8b94-0c2f5f8a15a2
-- title:
--   Iterated multiplication, torsion points and kernel schemes of relative group laws
-- statement:
--   Throughout, $R$ is a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and $G$ is a relative group law on $f$: a structure equipping every set $\mathrm{SchemeHomOver}\,t\,f = \{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of relative points, for $t \colon T \to \operatorname{Spec} R$, with a multiplication, a unit and an inverse satisfying the group axioms, together with compatibility of the multiplication with precomposition `schemeHomOverComp ψ hψ`, $x \mapsto \psi$ followed by $x$, for $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$.
--
--   `nsmul` is the iterated product: $G.\mathrm{nsmul}\,t\,0\,x$ is the unit of $\mathrm{SchemeHomOver}\,t\,f$, and $G.\mathrm{nsmul}\,t\,(n+1)\,x$ is $G.\mathrm{nsmul}\,t\,n\,x$ multiplied on the right by $x$; accompanying lemmas record the two recursion equations, $1 \cdot x = x$, that the unit is fixed by every $n$, and naturality: precomposition with $\psi$ carries $n$-fold products to $n$-fold products. The predicate `IsTorsionPoint t n x` says exactly $G.\mathrm{nsmul}\,t\,n\,x = G.\mathrm{one}\,t$, and `torsionSubset t n` is the set of relative points satisfying it; it contains the unit, equals $\{G.\mathrm{one}\,t\}$ for $n = 1$, and is preserved by precomposition with $\psi$, so the torsion loci form a subfunctor of the functor of relative points.
--
--   The remaining declarations materialise multiplication by $n$ on the scheme. `idPoint` is the identity of $A$ viewed as an element of $\mathrm{SchemeHomOver}\,f\,f$, the universal point; `schemeNsmul n` is the underlying morphism $A \to A$ of $G.\mathrm{nsmul}\,f\,n\,\mathrm{idPoint}$, and `schemeNsmul_over` states that it lies over $\operatorname{Spec} R$, i.e. $[n]$ followed by $f$ equals $f$. Finally `schemeKer G n` is the fibre product of $[n] =$ `schemeNsmul n` and the underlying morphism $\operatorname{Spec} R \to A$ of the unit $G.\mathrm{one}\,(\mathbf{1}_{\operatorname{Spec} R})$, that is the kernel scheme $A[n]$, with `schemeKerStr G n` its second projection to $\operatorname{Spec} R$ as structure morphism.
--
--   **Relation to Mathlib.** Mathlib describes group objects via monoid objects in a cartesian monoidal category; `RelativeGroupLaw` is this project's functor-of-points presentation of a group law on $f \colon A \to \operatorname{Spec} R$, and the iterated multiplication, torsion subfunctors and kernel scheme built from it are project-specific, the kernel being formed with Mathlib's fibre products of schemes.
--
--   **Where it is used.** These constructions supply the multiplication-by-$n$ morphism and the $n$-torsion subscheme $A[n]$ of a relative group scheme over a base, as needed when studying good reduction and Néron models of Jacobians, and in particular when passing from $A[n]$ to finite flat group schemes and their Hopf-algebra descriptions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawKernel.lean

import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Mathlib.AlgebraicGeometry.Pullbacks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n

@[simp]
theorem nsmul_zero (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 0 x = G.one t :=
  rfl

@[simp]
theorem nsmul_succ (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (n + 1) x = G.mul t (G.nsmul t n x) x :=
  rfl

theorem nsmul_one_apply (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 1 x = x := by
  show G.mul t (G.one t) x = x
  exact G.one_mul t x

theorem nsmul_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.nsmul t n (G.one t) = G.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, G.mul_one]

theorem nsmul_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.nsmul t n x) = G.nsmul t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero =>
      show schemeHomOverComp ψ hψ (G.one t) = G.one t'
      exact G.one_natural t t' ψ hψ
  | succ n ih =>
      calc schemeHomOverComp ψ hψ (G.nsmul t (n + 1) x)
          = schemeHomOverComp ψ hψ (G.mul t (G.nsmul t n x) x) := rfl
        _ = G.mul t' (schemeHomOverComp ψ hψ (G.nsmul t n x)) (schemeHomOverComp ψ hψ x) :=
            G.mul_natural t t' ψ hψ _ _
        _ = G.mul t' (G.nsmul t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x) := by
            rw [ih]
        _ = G.nsmul t' (n + 1) (schemeHomOverComp ψ hψ x) := rfl

def IsTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : Prop :=
  G.nsmul t n x = G.one t

theorem isTorsionPoint_def (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔ G.nsmul t n x = G.one t :=
  Iff.rfl

def torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) : Set (SchemeHomOver t f) :=
  {x | G.IsTorsionPoint t n x}

@[simp]
theorem mem_torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x ∈ G.torsionSubset t n ↔ G.IsTorsionPoint t n x :=
  Iff.rfl

theorem isTorsionPoint_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.IsTorsionPoint t n (G.one t) :=
  G.nsmul_unit t n

theorem isTorsionPoint_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t 1 x ↔ x = G.one t := by
  show G.nsmul t 1 x = G.one t ↔ x = G.one t
  rw [G.nsmul_one_apply]

theorem isTorsionPoint_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t n x) :
    G.IsTorsionPoint t' n (schemeHomOverComp ψ hψ x) := by
  show G.nsmul t' n (schemeHomOverComp ψ hψ x) = G.one t'
  rw [← G.nsmul_natural t t' ψ hψ n x, hx]
  exact G.one_natural t t' ψ hψ

theorem mapsTo_torsionSubset_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) :
    Set.MapsTo (schemeHomOverComp ψ hψ) (G.torsionSubset t n) (G.torsionSubset t' n) :=
  fun _ hx => G.isTorsionPoint_schemeHomOverComp t t' ψ hψ n hx

abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩

def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1

theorem schemeNsmul_over (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeNsmul n ≫ f = f :=
  (G.nsmul f n idPoint).2

abbrev schemeKer (G : RelativeGroupLaw R f) (n : ℕ) : Scheme.{u} :=
  pullback (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev schemeKerStr (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeKer n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

end RelativeGroupLaw

end GoodReductionJacobian


