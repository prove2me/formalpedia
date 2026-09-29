-- Prove2me | Definitions.Def_CerednikDrinfeld_Ribbon
-- name    : CerednikDrinfeld_Ribbon
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/e7ec5b69-bfd9-5743-af87-f32dfcaf9f80
-- title:
--   Degeneracy data, ribbon kernels and width Gram cokernels
-- statement:
--   A `DegeneracyData E V` consists of two maps $a,b : E \to V$ between index types together with a width function $w : E \to \mathbb{N}^{+}$; throughout, $E$ and $V$ are finite and $V$ has decidable equality. For any $f : E \to V$, `degeneracyMatrix f` is the $V \times E$ integer matrix with entry $1$ at $(v,e)$ when $f(e) = v$ and $0$ otherwise, and `pushforward f` is the associated linear map $(E \to \mathbb{Z}) \to (V \to \mathbb{Z})$, $(f_{*}x)(v) = \sum_{f(e)=v} x(e)$. `jointDelta D` is the pair $(a_{*}, b_{*})$, indexed by `Fin 2`, and `ribbonKernel D` is the intersection of the kernels of its two components, i.e. the lattice of $x : E \to \mathbb{Z}$ with $a_{*}x = b_{*}x = 0$ (a joint kernel, not the kernel of a difference); `mem_ribbonKernel` records this membership criterion. Since a pushforward preserves total degree (`degreeOn_pushforward`), the ribbon kernel lies inside the degree-zero lattice `characterLattice E` (`ribbonKernel_le_characterLattice`). `ribbonGram D` is the restriction to the ribbon kernel of the width pairing $\langle x,y\rangle = \sum_{e} w(e)\,x(e)y(e)$, viewed as a map $Y \to \operatorname{Hom}_{\mathbb{Z}}(Y,\mathbb{Z})$ with $Y =$ `ribbonKernel D`, and `ribbonComponentGroup D` is its cokernel $Y^{*}/\operatorname{im}$, with `ribbonComponentGroupProj` the quotient map. Given endomorphisms $A,B$ of $Y$ adjoint for this pairing ($\langle Ax,y\rangle = \langle x,By\rangle$), the dual map of $B$ preserves the image of the Gram map and so descends to `ribbonComponentGroupMap`.
--
--   A `HeckeData D` is a structure carrying families of integer matrices $T_{\ell}$ on $E$ and $T_{v,\ell}$ on $V$ indexed by the primes, pairwise commuting on each side, a finite set $S$ of primes, and two assertions as fields: for $\ell \notin S$ both pushforwards intertwine $T_{\ell}$ with $T_{v,\ell}$, and for every prime $\ell$ the matrix $T_{\ell}$ carries the joint kernel into itself. Hence `ribbonKernel_stable` and the restricted operator `heckeKernelMap`. A `Matching H₁ H₂` of two such packages consists of bijections $E_{1} \simeq E_{2}$ and $V_{1} \simeq V_{2}$ compatible with $a$, $b$ and $w$, a finite set of exceptional primes, intertwining of the $T_{\ell}$ under transport by the bijection for all vectors away from that set, and intertwining only for vectors in `ribbonKernel D₁` at the exceptional primes.
--
--   **Relation to Mathlib.** Mathlib has no notion of degeneracy data, ribbon kernel or Gram cokernel of this kind; these are the project's own, built on Mathlib's `Matrix.mulVecLin`, `Module.Dual`, submodule kernels and `LinearMap.mapQ`, and on the project's width pairing and degree-zero character lattice.
--
--   **Where it is used.** These lattices and cokernels provide the combinatorial model for character groups and component groups of Jacobians of modular curves at a prime of multiplicative reduction, in the form used for the Čerednik–Drinfeld description; the Hecke and matching data express the compatibility of Hecke actions on the two sides needed in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_Ribbon.lean

import Definitions.Def_ModularCurve_ComponentGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*}

structure DegeneracyData (E V : Type*) where
  a : E → V
  b : E → V
  w : E → ℕ+

def degeneracyMatrix [DecidableEq V] (f : E → V) : Matrix V E ℤ :=
  Matrix.of fun v e => if f e = v then 1 else 0

def pushforward [Fintype E] [DecidableEq V] (f : E → V) : (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (degeneracyMatrix f).mulVecLin

def jointDelta [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Fin 2 → ((E → ℤ) →ₗ[ℤ] (V → ℤ)) :=
  ![pushforward D.a, pushforward D.b]

def ribbonKernel [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Submodule ℤ (E → ℤ) :=
  ⨅ i, LinearMap.ker (jointDelta D i)

theorem mem_ribbonKernel [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {x : E → ℤ} : x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 := by
  simp [ribbonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

theorem degreeOn_pushforward [Fintype E] [Fintype V] [DecidableEq V] (f : E → V)
    (x : E → ℤ) : degreeOn V (pushforward f x) = degreeOn E x := by
  classical
  simp only [degreeOn_apply, pushforward, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

theorem ribbonKernel_le_characterLattice [Fintype E] [Fintype V] [DecidableEq V]
    (D : DegeneracyData E V) : ribbonKernel D ≤ characterLattice E := by
  intro x hx
  rw [mem_ribbonKernel] at hx
  have h0 : pushforward D.a x = 0 := by
    simpa [jointDelta] using hx 0
  have hdeg : degreeOn E x = 0 := by
    rw [← degreeOn_pushforward D.a x, h0, map_zero]
  simpa [characterLattice, LinearMap.mem_ker] using hdeg

def ribbonGram [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D →ₗ[ℤ] Module.Dual ℤ (ribbonKernel D) :=
  (widthPairing (fun e => (D.w e : ℕ))).domRestrict₁₂ (ribbonKernel D) (ribbonKernel D)

@[simp] theorem ribbonGram_apply [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (x y : ribbonKernel D) :
    ribbonGram D x y = ∑ e : E, (D.w e : ℤ) * (x.1 e * y.1 e) :=
  rfl

abbrev ribbonComponentGroup [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :=
  Module.Dual ℤ ↥(ribbonKernel D) ⧸ LinearMap.range (ribbonGram D)

abbrev ribbonComponentGroupProj [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :
    Module.Dual ℤ ↥(ribbonKernel D) →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mkQ

theorem ribbonGram_range_map_dualMap_le [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D, ribbonGram D (A x) y = ribbonGram D x (B y)) :
    (LinearMap.range (ribbonGram D)).map B.dualMap ≤ LinearMap.range (ribbonGram D) := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hf
  refine LinearMap.mem_range.mpr ⟨A x, ?_⟩
  ext y
  rw [LinearMap.dualMap_apply]
  exact hadj x y

def ribbonComponentGroupMap [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D, ribbonGram D (A x) y = ribbonGram D x (B y)) :
    ribbonComponentGroup D →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mapQ (LinearMap.range (ribbonGram D)) B.dualMap
    (fun _ hf => ribbonGram_range_map_dualMap_le D A B hadj (Submodule.mem_map_of_mem hf))

structure HeckeData [Fintype E] [Fintype V] [DecidableEq V] (D : DegeneracyData E V) where
  T : Nat.Primes → Matrix E E ℤ
  Tv : Nat.Primes → Matrix V V ℤ
  comm : ∀ ℓ ℓ' : Nat.Primes, Commute (T ℓ) (T ℓ')
  commv : ∀ ℓ ℓ' : Nat.Primes, Commute (Tv ℓ) (Tv ℓ')
  S : Finset Nat.Primes
  good_equivariant : ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ i : Fin 2, ∀ x : E → ℤ,
    jointDelta D i ((T ℓ).mulVecLin x) = (Tv ℓ).mulVecLin (jointDelta D i x)
  kernel_stable : ∀ ℓ : Nat.Primes, ∀ x : E → ℤ, (∀ i, jointDelta D i x = 0) →
    ∀ i, jointDelta D i ((T ℓ).mulVecLin x) = 0

theorem ribbonKernel_stable [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ∀ x ∈ ribbonKernel D, (H.T ℓ).mulVecLin x ∈ ribbonKernel D := by
  intro x hx
  rw [mem_ribbonKernel] at hx ⊢
  exact H.kernel_stable ℓ x hx

def heckeKernelMap [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ribbonKernel D →ₗ[ℤ] ribbonKernel D :=
  ((H.T ℓ).mulVecLin).restrict (ribbonKernel_stable H ℓ)

variable {E₁ V₁ E₂ V₂ : Type*}

structure Matching [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}
    (H₁ : HeckeData D₁) (H₂ : HeckeData D₂) where
  eE : E₁ ≃ E₂
  eV : V₁ ≃ V₂
  map_a : ∀ e, D₂.a (eE e) = eV (D₁.a e)
  map_b : ∀ e, D₂.b (eE e) = eV (D₁.b e)
  map_w : ∀ e, D₂.w (eE e) = D₁.w e
  bad : Finset Nat.Primes
  away_intertwine : ∀ ℓ : Nat.Primes, ℓ ∉ bad → ∀ x : E₁ → ℤ,
    (H₂.T ℓ).mulVecLin (x ∘ eE.symm) = ((H₁.T ℓ).mulVecLin x) ∘ eE.symm
  bad_kernel_intertwine : ∀ ℓ : Nat.Primes, ℓ ∈ bad → ∀ x ∈ ribbonKernel D₁,
    (H₂.T ℓ).mulVecLin (x ∘ eE.symm) = ((H₁.T ℓ).mulVecLin x) ∘ eE.symm

end CerednikDrinfeld


