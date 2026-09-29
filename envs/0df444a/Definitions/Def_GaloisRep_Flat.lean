-- Prove2me | Definitions.Def_GaloisRep_Flat
-- name    : GaloisRep_Flat
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/49154088-8171-5cac-b749-e4d0a38a3496
-- title:
--   The flat local condition at p for adic Galois representations
-- statement:
--   For a natural number $p$, [`GaloisRep.ratLocalizedAt p`](../def/GaloisRep_Flat.html#L8) is the subring of $\mathbb{Q}$ consisting of those rationals whose reduced denominator is coprime to $p$; for $p$ prime this is $\mathbb{Z}_{(p)}$ (for $p=0$ it is $\mathbb{Z}$, for $p=1$ all of $\mathbb{Q}$), and it is built as a bespoke `Subring ℚ` so that $\overline{\mathbb{Q}}$ is an algebra over it. For a rank-two representation $\rho$ of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ over a local ring $A$ in the project's sense ([`GaloisRepAdic A`](../def/GaloisRep_Adic.html#L16): a free $A$-module $V$ of rank $2$, a monoid homomorphism into $\mathrm{End}_A V$, adically continuous) and an ideal $I\subseteq A$, `levelAction ρ I σ` is the $A$-linear endomorphism of $V/IV$ induced by $\rho(\sigma)$, one $\sigma$ at a time rather than as a homomorphism. `IsFlatAt ρ p` asserts: the residue field of $A$ is finite, and for every ideal $I$ with $A/I$ finite there exist a commutative ring $H$ with a Hopf algebra structure over $\mathbb{Z}_{(p)}$ that is finite and flat as a module and cocommutative as a coalgebra, together with a bijection $e$ from the convolution monoid `WithConv` of $\mathbb{Z}_{(p)}$-algebra maps $H\to\overline{\mathbb{Q}}$ onto $V/IV$ sending convolution to addition and satisfying: whenever $g=\sigma\circ f$ pointwise on $H$, one has $e(g)=\rho.\mathrm{levelAction}\,I\,\sigma\,(e f)$. Thus each finite level is realised, Galois-equivariantly, by the $\overline{\mathbb{Q}}$-points of a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$; no étale-generic-fibre clause is imposed and $e$ is required only to be additive and equivariant.
--
--   `flatCondition 𝒪 p S` is the predicate on [`GaloisRepAdic A`](../def/GaloisRep_Adic.html#L16), for local $\mathcal{O}$-algebras $A$ (the ring $\mathcal{O}$ and its algebra structure enter only to fix the type, not the body), asserting `DetIsCyclotomic p` — $p$ lies in the maximal ideal of $A$ and $\det\rho(\sigma)\equiv a \pmod{p^n}$ whenever $\sigma$ raises all $p^n$-th roots of unity to the $a$-th power — together with `IsFlatAt p` and unramifiedness, $\rho(\sigma)=1$ for $\sigma$ in the inertia subgroup of any valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, at every prime $q\notin S$. `minimalFlatCondition 𝒪 p S` adds `IsUnipotentOnInertiaAt q` for each prime $q\in S$ with $q\neq p$: inertia elements there have characteristic polynomial $(X-1)^2$. Here `IsUnramifiedAt` comes from the adic-representation module and the other two from the local-conditions module.
--
--   **Relation to Mathlib.** Mathlib's `HopfAlgebra`, `Coalgebra.IsCocomm`, `Module.Flat`, `Module.Finite` and the convolution monoid `WithConv` on an algebra-hom space are used as given; the local ring $\mathbb{Z}_{(p)}$ is constructed here as an explicit `Subring ℚ` rather than via `Localization.AtPrime`, so that the algebra and scalar-tower instances over $\overline{\mathbb{Q}}$ are the standard ones for subrings. Mathlib has no notion of a flat Galois representation or of local deformation conditions; those are the project's own.
--
--   **Where it is used.** `flatCondition` and `minimalFlatCondition` have the shape required of the deformation condition parameter in the project's deformation-ring data, and provide the flat alternative to the ordinary condition used in Wiles's modularity lifting theorem at a prime $p$ of good reduction (respectively $p\nmid N$ on the Hecke side).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_Flat.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Flat.Basic
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace GaloisRep

def ratLocalizedAt (p : ℕ) : Subring ℚ where
  carrier := {q : ℚ | q.den.Coprime p}
  mul_mem' {a b} ha hb := Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (ha.mul_left hb)
  one_mem' := by simp
  add_mem' {a b} ha hb := Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (ha.mul_left hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

end GaloisRep

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

noncomputable def levelAction (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) →ₗ[A] (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :=
  Submodule.mapQ _ _ (ρ.ρ σ) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

def IsFlatAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  Finite (IsLocalRing.ResidueField A) ∧ ∀ I : Ideal A, Finite (A ⧸ I) →
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))),
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.levelAction I σ (e f)

end GaloisRepAdic

namespace GaloisRep

def flatCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ ρ.IsFlatAt p ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

def minimalFlatCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => flatCondition 𝒪 p S ρ ∧
    ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q

end GaloisRep


