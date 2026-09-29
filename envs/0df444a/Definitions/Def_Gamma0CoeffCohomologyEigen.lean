-- Prove2me | Definitions.Def_Gamma0CoeffCohomologyEigen
-- name    : Gamma0CoeffCohomologyEigen
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/ac940d15-8024-5ae9-a0b6-01d31b47d1c6
-- title:
--   First coefficient cohomology, Hecke eigensystems, binary-form substitution action
-- statement:
--   Fix a commutative ring $K$, a group $G$ and a representation $\rho$ of $G$ on a $K$-module $V$. Recall the submodules of $G \to V$ given by the inhomogeneous cocycles $Z^1 = \{z : z(gh) = z(g) + \rho(g)z(h)\}$ and the coboundaries $B^1 = \{g \mapsto \rho(g)v - v\}$. Here `coeffH1 ρ` is the quotient of the type of cocycles by the pullback of $B^1$ along the inclusion $Z^1 \hookrightarrow (G \to V)$, i.e. $Z^1/B^1$, carrying the induced additive group and $K$-module structures; `coeffH1Mk ρ` is the $K$-linear class map, which is surjective, and a cocycle class vanishes exactly when the underlying function is a coboundary. For $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$, `coeffH1parToH1 ρ` is the $K$-linear map $H^1_{\mathrm{par}} \to H^1$ induced by the inclusion of parabolic cocycles into cocycles, and it is compatible with the two class maps.
--
--   For a representation $\rho$ of $\Gamma_0(N)$, a $K$-linear $a : V \to V$ and an endomorphism $T$ of `coeffH1 ρ`, the predicate `IsCoeffHeckeOnH1 N ℓ ρ a T` says that for every cocycle $z$ the cochain `coeffHeckeFun N ℓ ρ a z` (the transfer-style sum over $\Gamma_0(N)/\{\gamma : \ell \mid \gamma_{01}\}$, twisted by conjugation by $\mathrm{diag}(1,\ell)$ and by $a$) is again a cocycle and $T[z]$ is its class; this is a property of a given $T$, not a construction of one. Then `IsEigensystemH1 N ρ a S₀ lam` asserts the existence of a nonzero class $x$ such that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ some $T$ satisfying `IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T` has $Tx = \mathrm{lam}(\ell)\,x$.
--
--   Finally `binaryFormRep K n` is the monoid homomorphism from $2\times 2$ integral matrices to $K$-linear endomorphisms of the degree-$n$ binary forms given by the substitution $X_j \mapsto \sum_i M_{ij} X_i$; restricting it along $\mathrm{SL}_2(\mathbb{Z})$ recovers `binaryFormRepSL`, and evaluating at $\mathrm{diag}(\ell,1)$ recovers `binaryFormAlphaAdj`.
--
--   **Relation to Mathlib.** Mathlib's group cohomology is developed for objects of `Rep k G`; the $H^1$ here is built by hand from a `Representation K G V` as a quotient of submodules of $G \to V$, and is not identified with the Mathlib construction. The degree-$n$ binary forms are Mathlib's `MvPolynomial.homogeneousSubmodule (Fin 2) K n`; the substitution action on them is the project's own.
--
--   **Where it is used.** These definitions provide the group-cohomological model of modular symbols for $\Gamma_0(N)$ with coefficients in a representation, together with the notion of a Hecke eigensystem occurring in it, used in the project's handling of Hecke eigenvalues and Eisenstein classes; the binary-form representation supplies the weight-$n$ coefficient module together with the auxiliary map at $\ell$ entering the Hecke operator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Gamma0CoeffCohomologyEigen.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

section H1

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def coeffH1 (ρ : Representation K G V) : Type _ :=
  ↥(coeffCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype

instance instAddCommGroupCoeffH1 (ρ : Representation K G V) : AddCommGroup (coeffH1 ρ) :=
  inferInstanceAs (AddCommGroup
    (↥(coeffCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype))

instance instModuleCoeffH1 (ρ : Representation K G V) : Module K (coeffH1 ρ) :=
  inferInstanceAs (Module K
    (↥(coeffCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype))

def coeffH1Mk (ρ : Representation K G V) : ↥(coeffCocycles ρ) →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mkQ

theorem coeffH1Mk_surjective (ρ : Representation K G V) : Function.Surjective (coeffH1Mk ρ) :=
  Submodule.mkQ_surjective _

theorem coeffH1Mk_eq_zero_iff (ρ : Representation K G V) (z : ↥(coeffCocycles ρ)) :
    coeffH1Mk ρ z = 0 ↔ (z : G → V) ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

end H1

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def coeffH1parToH1 (ρ : Representation K Γ V) : coeffH1par ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype)
    (Submodule.inclusion (coeffParabolicCocycles_le_coeffCocycles ρ))
    fun _ hz => hz

theorem coeffH1parToH1_coeffH1parMk (ρ : Representation K Γ V) (z : ↥(coeffParabolicCocycles ρ)) :
    coeffH1parToH1 ρ (coeffH1parMk ρ z) =
      coeffH1Mk ρ (Submodule.inclusion (coeffParabolicCocycles_le_coeffCocycles ρ) z) :=
  rfl

end Parabolic

section Hecke

variable (N : ℕ) (ℓ : ℕ) [NeZero ℓ]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsCoeffHeckeOnH1 (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (T : coeffH1 ρ →ₗ[K] coeffH1 ρ) : Prop :=
  ∀ z : ↥(coeffCocycles ρ), ∃ w : ↥(coeffCocycles ρ),
    (w : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z ∧ T (coeffH1Mk ρ z) = coeffH1Mk ρ w

end Hecke

section Eigensystem

variable (N : ℕ) {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsEigensystemH1 (ρ : Representation K (Gamma0 N) V) (a : ℕ → (V →ₗ[K] V)) (S₀ : Set ℕ)
    (lam : ℕ → K) : Prop :=
  ∃ x : coeffH1 ρ, x ≠ 0 ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
    ∃ T : coeffH1 ρ →ₗ[K] coeffH1 ρ,
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T) ∧ T x = lam ℓ • x

end Eigensystem

section BinaryFormRep

variable (K : Type*) [CommRing K] (n : ℕ)

noncomputable def binaryFormRep : Matrix (Fin 2) (Fin 2) ℤ →* (↥(BinaryForm K n) →ₗ[K] ↥(BinaryForm K n)) where
  toFun M := (binarySubst K M).toLinearMap.restrict fun _ hF => binarySubst_mem K M hF
  map_one' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K (1 : Matrix (Fin 2) (Fin 2) ℤ) F.1 = F.1
    rw [binarySubst_one]
    rfl
  map_mul' M M' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K (M * M') F.1 = binarySubst K M (binarySubst K M' F.1)
    rw [binarySubst_mul]
    rfl

@[simp]
theorem binaryFormRep_apply_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(BinaryForm K n)) :
    ((binaryFormRep K n M F : ↥(BinaryForm K n)) : MvPolynomial (Fin 2) K) = binarySubst K M F :=
  rfl

theorem binaryFormRepSL_apply_eq_binaryFormRep (g : SL(2, ℤ)) :
    binaryFormRepSL K n g = binaryFormRep K n (g : Matrix (Fin 2) (Fin 2) ℤ) :=
  rfl

theorem binaryFormAlphaAdj_eq_binaryFormRep (ℓ : ℕ) :
    binaryFormAlphaAdj K n ℓ = binaryFormRep K n !![(ℓ : ℤ), 0; 0, 1] :=
  rfl

end BinaryFormRep

end HeckeEis


