-- Prove2me | Definitions.Def_CuspidalType_IsCuspidalOfType
-- name    : CuspidalType_IsCuspidalOfType
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/6716e301-cf14-5b65-b2e5-83118c342c1a
-- title:
--   Cuspidal representations of GL2​(Fq​) of a given type
-- statement:
--   For a prime $q$, `GL2 q` is $\mathrm{GL}_2(\mathbf{Z}/q)$ and `ProjLine q` is the projectivization of $(\mathbf{Z}/q)^2$, on which `GL2 q` acts through the monoid homomorphism sending a matrix to the associated linear automorphism; `card_projLine` records that this set has $q+1$ elements. Distinguished elements are named: `unipotent q t` is $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, `diagElem q a` is $\mathrm{diag}(a,1)$, and `scalarElem q` is the homomorphism $(\mathbf{Z}/q)^\times\to\mathrm{GL}_2(\mathbf{Z}/q)$ given by scalar matrices. Over a field $k$, `ind q k` is the permutation representation of `GL2 q` on finitely supported $k$-valued functions on the projective line, of dimension $q+1$ (`finrank_ind`); `coeffSum` is the linear form summing all coefficients, `steinberg q k` is the subrepresentation cut out by its kernel, with associated representation `steinbergRep`, and the constant function `constFun` has coefficient sum $q+1$, hence lies in the kernel precisely when $q+1=0$ in $k$. A nonsplit torus is produced by fixing, via the equality $[\mathbf{F}_{q^2}:\mathbf{F}_q]=2$, a two-element $\mathbf{Z}/q$-basis `quadBasis` of `GaloisField q 2`, and letting `torus q` send a unit $\alpha$ to the matrix of multiplication by $\alpha$ in that basis.
--
--   The structure `IsCuspidalOfType θ ρ`, for a homomorphism $\theta\colon\mathbf{F}_{q^2}^\times\to K^\times$ and a representation $\rho$ of `GL2 q` on a finite-dimensional $K$-vector space $V$, is a proposition with four fields: $\dim_K V = q-1$; no nonzero vector of $V$ is fixed by all $\rho(\mathrm{unipotent}\ t)$; every scalar element acts as the identity; and for every $\alpha\in\mathbf{F}_{q^2}^\times$ the characteristic polynomial of $\rho(\mathrm{torus}\ \alpha)$ multiplied by $(X-\theta(\alpha))(X-\theta(\alpha)^{-1})$ equals that of $\mathrm{torus}\ \alpha$ acting on the $(q+1)$-dimensional permutation representation. Thus the predicate characterises cuspidal representations of type $\theta$ with trivial central character by dimension, absence of unipotent invariants, centrality, and a relation of torus characteristic polynomials; no such representation is constructed here.
--
--   **Relation to Mathlib.** `Subrepresentation`, `Projectivization` and `GaloisField` are Mathlib's; the induced representation `ind` is built from the project's vendored copy [`Representation.ofMulActionFinsupp`](../def/Compat_Mathlib430.html#L28) of Mathlib's permutation representation phrased on `Finsupp`. Mathlib has no notion of a cuspidal representation of $\mathrm{GL}_2(\mathbf{F}_q)$, nor of the Steinberg subrepresentation; both are introduced here.
--
--   **Where it is used.** These notions supply the representation theory of $\mathrm{GL}_2(\mathbf{F}_q)$ needed to describe local behaviour at a prime $q$: the Steinberg subrepresentation of the $(q+1)$-dimensional permutation representation on the projective line, and the cuspidal representations of type $\theta$, which enter the specification of types and local conditions in the modularity-lifting arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspidalType_IsCuspidalOfType.lean

import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]

abbrev GL2 : Type := Matrix.GeneralLinearGroup (Fin 2) (ZMod q)

abbrev ProjLine : Type := Projectivization (ZMod q) (Fin 2 → ZMod q)

scoped instance instMulActionProjLine : MulAction (GL2 q) (ProjLine q) :=
  MulAction.compHom (ProjLine q)
    (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod q)).toMonoidHom

def unipotent (t : ZMod q) : GL2 q :=
  ⟨!![1, t; 0, 1], !![1, -t; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def scalarElem : (ZMod q)ˣ →* GL2 q :=
  Units.map (Matrix.scalar (Fin 2) : ZMod q →+* Matrix (Fin 2) (Fin 2) (ZMod q)).toMonoidHom

def diagElem (a : (ZMod q)ˣ) : GL2 q :=
  ⟨!![(a : ZMod q), 0; 0, 1], !![((a⁻¹ : (ZMod q)ˣ) : ZMod q), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit]⟩

@[scoped simp] theorem diagElem_val (a : (ZMod q)ˣ) :
    (diagElem q a : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(a : ZMod q), 0; 0, 1] := rfl

@[scoped simp] theorem unipotent_val (t : ZMod q) :
    (unipotent q t : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, t; 0, 1] := rfl

theorem card_projLine : Nat.card (ProjLine q) = q + 1 := by
  rw [Projectivization.card_of_finrank_two (ZMod q) (Fin 2 → ZMod q) (by simp), Nat.card_zmod]

variable (k : Type*) [Field k]

noncomputable abbrev ind : Representation k (GL2 q) (ProjLine q →₀ k) :=
  Representation.ofMulActionFinsupp k (GL2 q) (ProjLine q)

noncomputable def coeffSum : (ProjLine q →₀ k) →ₗ[k] k :=
  Finsupp.linearCombination k fun _ => (1 : k)

noncomputable def steinberg : Subrepresentation (ind q k) where
  toSubmodule := LinearMap.ker (coeffSum q k)
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker, coeffSum] at hv ⊢
    rw [show ind q k g v = Finsupp.mapDomain (g • ·) v from rfl, Finsupp.linearCombination_mapDomain]
    exact hv

noncomputable abbrev steinbergRep : Representation k (GL2 q) (steinberg q k).toSubmodule :=
  (steinberg q k).toRepresentation

noncomputable def constFun : ProjLine q →₀ k :=
  Finsupp.equivFunOnFinite.symm fun _ => (1 : k)

theorem coeffSum_constFun : coeffSum q k (constFun q k) = (q : k) + 1 := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  have hcard : (Fintype.card (ProjLine q) : k) = (q : k) + 1 := by
    rw [← Nat.card_eq_fintype_card, card_projLine]; push_cast; rfl
  rw [coeffSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun _ => zero_smul k (1 : k))]
  simp only [constFun, Finsupp.coe_equivFunOnFinite_symm, one_smul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact hcard

theorem constFun_mem_steinberg_iff : constFun q k ∈ (steinberg q k).toSubmodule ↔ (q : k) + 1 = 0 := by
  change constFun q k ∈ LinearMap.ker (coeffSum q k) ↔ _
  rw [LinearMap.mem_ker, coeffSum_constFun]

theorem finrank_ind : Module.finrank k (ProjLine q →₀ k) = q + 1 := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, card_projLine]

noncomputable def quadBasis : Module.Basis (Fin 2) (ZMod q) (GaloisField q 2) :=
  Module.finBasisOfFinrankEq (ZMod q) (GaloisField q 2) (GaloisField.finrank q two_ne_zero)

noncomputable def torus : (GaloisField q 2)ˣ →* GL2 q :=
  Units.map
    (MonoidHomClass.toMonoidHom
      ((LinearMap.toMatrixAlgEquiv (quadBasis q)).toAlgHom.comp
        (Algebra.lmul (ZMod q) (GaloisField q 2))))

variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

structure IsCuspidalOfType (θ : (GaloisField q 2)ˣ →* Kˣ) (ρ : Representation K (GL2 q) V) : Prop where
  finrank_eq : Module.finrank K V = q - 1
  cuspidal : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0
  central : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id
  torus_charpoly : ∀ α : (GaloisField q 2)ˣ,
    LinearMap.charpoly (ρ (torus q α)) * ((X - C ((θ α : Kˣ) : K)) * (X - C (((θ α)⁻¹ : Kˣ) : K))) =
      LinearMap.charpoly (ind q K (torus q α))

end CuspidalType


