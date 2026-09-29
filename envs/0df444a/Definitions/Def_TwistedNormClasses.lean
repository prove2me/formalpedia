-- Prove2me | Definitions.Def_TwistedNormClasses
-- name    : TwistedNormClasses
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/126fb10c-c12f-5fdc-982d-836f19d80b58
-- title:
--   Twisted norms and σ-conjugacy classes for GL₂
-- statement:
--   For a group $G$ and an endomorphism $\sigma : G \to G$, `sigmaPartialNorm σ x r` is defined by the recursion $P_0(x) = 1$, $P_{r+1}(x) = x\,\sigma(P_r(x))$, so that $P_r(x) = x\,\sigma(x)\cdots\sigma^{r-1}(x)$ as an ordered product (established both as a list product over `List.range r` and, in the commutative case, as a `Finset.range` product), and `sigmaNormPow σ ℓ x` is $P_\ell(x)$. The accompanying lemmas record the twisting identities $P_\ell(h^{-1}x\,\sigma h) = h^{-1}P_\ell(x)\,\sigma^{\ell}(h)$, $\sigma(P_\ell x) = x^{-1}P_\ell(x)\,x$ when $\sigma^{\ell}(x) = x$, transport along homomorphisms intertwining two endomorphisms, and, for $\mathrm{GL}_n$ over a commutative ring with $\sigma$ acting entrywise, compatibility with the determinant and $\sigma$-invariance of the characteristic polynomial of the twisted norm.
--
--   In the $\mathrm{GL}_2$ part, `traceDetCompanion t d` is the matrix $\begin{pmatrix}0 & -d\\ 1 & t\end{pmatrix}$, used as the rational canonical form of a non-scalar $2\times 2$ matrix with trace $t$ and determinant $d$.
--
--   The class-level vocabulary is built on the imported relation [`AutomorphicForm.IsSigmaConj σ δ₁ δ₂`](../def/AutomorphicForm_SigmaConjugacy.html#L15), namely $\delta_2 = g\,\delta_1\,(\sigma g)^{-1}$ for some $g \in \mathrm{GL}_2(L)$, which is equivalent to $\delta_2 = h^{-1}\delta_1\,\sigma(h)$ for some $h$; `sigmaConjSetoid σ` equips $\mathrm{GL}_2(L)$ with this relation as an equivalence relation and `SigmaConjClasses σ` is the quotient, with `SigmaConjClasses.mk` the quotient map. For $L/F$ with $\sigma \in \mathrm{Gal}(L/F)$, `IsNormRep σ γ δ` asserts the existence of $P \in \mathrm{GL}_2(L)$ with $P^{-1}\,N_{[L:F]}(\delta)\,P$ equal to the image of $\gamma \in \mathrm{GL}_2(F)$ under entrywise $F \to L$. Under the hypothesis that $\sigma$ generates $\mathrm{Gal}(L/F)$, `normRep` chooses such a $\gamma$ for each $\delta$, `normClassMap` is the induced map from $\sigma$-conjugacy classes to `ConjClasses (GL (Fin 2) F)`, and `IsNormClass` is membership in its range.
--
--   **Relation to Mathlib.** The ordered partial norm along a group endomorphism and the twisted norm are the project's own; Mathlib's `Algebra.norm` appears only through the identification of the twisted norm on units with $N_{L/F}$. `sigmaConjSetoid`/`SigmaConjClasses` package the imported relation [`AutomorphicForm.IsSigmaConj`](../def/AutomorphicForm_SigmaConjugacy.html#L15) as a quotient in the same style as Mathlib's `ConjClasses`, into which `normClassMap` lands.
--
--   **Where it is used.** These definitions supply the norm correspondence underlying cyclic base change for $\mathrm{GL}_2$: each $\sigma$-conjugacy class of $\mathrm{GL}_2(L)$ determines, via its twisted norm, a conjugacy class in $\mathrm{GL}_2(F)$, with $\det \gamma = N_{L/F}(\det \delta)$ and matching characteristic polynomials. This is the group-theoretic input for comparing automorphic forms over $F$ with their base change to a cyclic extension $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TwistedNormClasses.lean

import Definitions.Def_AutomorphicForm_SigmaConjugacy
import Mathlib.Tactic.Group
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Trace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LT.TwistedNorm

private theorem iterate_succ_apply'' {α : Type*} (f : α → α) (r : ℕ) (x : α) :
    f^[r + 1] x = f (f^[r] x) := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
      calc f^[r + 1 + 1] x = f^[r + 1] (f x) := rfl
        _ = f (f^[r] (f x)) := ih (f x)
        _ = f (f^[r + 1] x) := rfl

section PartialNorm

variable {G : Type*} [Group G]

def sigmaPartialNorm (σ : G →* G) (x : G) : ℕ → G
  | 0 => 1
  | r + 1 => x * σ (sigmaPartialNorm σ x r)

@[simp] theorem sigmaPartialNorm_zero (σ : G →* G) (x : G) :
    sigmaPartialNorm σ x 0 = 1 := rfl

theorem sigmaPartialNorm_succ' (σ : G →* G) (x : G) (r : ℕ) :
    sigmaPartialNorm σ x (r + 1) = x * σ (sigmaPartialNorm σ x r) := rfl

theorem sigmaPartialNorm_one (σ : G →* G) (x : G) :
    sigmaPartialNorm σ x 1 = x := by
  rw [sigmaPartialNorm_succ', sigmaPartialNorm_zero, map_one, mul_one]

attribute [local simp] sigmaPartialNorm_one

theorem sigmaPartialNorm_succ (σ : G →* G) (x : G) (r : ℕ) :
    sigmaPartialNorm σ x (r + 1) = sigmaPartialNorm σ x r * (⇑σ)^[r] x := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc sigmaPartialNorm σ x (r + 1 + 1)
          = x * σ (sigmaPartialNorm σ x (r + 1)) := rfl
        _ = x * σ (sigmaPartialNorm σ x r * (⇑σ)^[r] x) := by rw [ih]
        _ = x * σ (sigmaPartialNorm σ x r) * σ ((⇑σ)^[r] x) := by rw [map_mul, mul_assoc]
        _ = sigmaPartialNorm σ x (r + 1) * (⇑σ)^[r + 1] x := by
              rw [← sigmaPartialNorm_succ', iterate_succ_apply'']

def sigmaNormPow (σ : G →* G) (ℓ : ℕ) (x : G) : G :=
  sigmaPartialNorm σ x ℓ

theorem sigmaNormPow_def (σ : G →* G) (ℓ : ℕ) (x : G) :
    sigmaNormPow σ ℓ x = sigmaPartialNorm σ x ℓ := rfl

theorem sigmaPartialNorm_sigmaConjElt (σ : G →* G) (h x : G) (r : ℕ) :
    sigmaPartialNorm σ (h⁻¹ * x * σ h) r
      = h⁻¹ * sigmaPartialNorm σ x r * (⇑σ)^[r] h := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc sigmaPartialNorm σ (h⁻¹ * x * σ h) (r + 1)
          = (h⁻¹ * x * σ h) * σ (sigmaPartialNorm σ (h⁻¹ * x * σ h) r) := rfl
        _ = (h⁻¹ * x * σ h) * σ (h⁻¹ * sigmaPartialNorm σ x r * (⇑σ)^[r] h) := by rw [ih]
        _ = h⁻¹ * (x * σ (sigmaPartialNorm σ x r)) * (⇑σ)^[r + 1] h := by
              simp only [map_mul, map_inv, iterate_succ_apply'']
              group
        _ = h⁻¹ * sigmaPartialNorm σ x (r + 1) * (⇑σ)^[r + 1] h := by
              rw [← sigmaPartialNorm_succ']

theorem sigmaNormPow_sigmaConjElt (σ : G →* G) (ℓ : ℕ) {h : G}
    (hσh : (⇑σ)^[ℓ] h = h) (x : G) :
    sigmaNormPow σ ℓ (h⁻¹ * x * σ h) = h⁻¹ * sigmaNormPow σ ℓ x * h := by
  rw [sigmaNormPow_def, sigmaNormPow_def, sigmaPartialNorm_sigmaConjElt, hσh]

theorem map_sigmaNormPow (σ : G →* G) (ℓ : ℕ) {x : G} (hσx : (⇑σ)^[ℓ] x = x) :
    σ (sigmaNormPow σ ℓ x) = x⁻¹ * sigmaNormPow σ ℓ x * x := by
  have hkey : x * σ (sigmaPartialNorm σ x ℓ) = sigmaPartialNorm σ x ℓ * x := by
    have h2 := sigmaPartialNorm_succ σ x ℓ
    rw [hσx] at h2
    rw [← sigmaPartialNorm_succ' σ x ℓ, h2]
  rw [sigmaNormPow_def]
  calc σ (sigmaPartialNorm σ x ℓ)
      = x⁻¹ * (x * σ (sigmaPartialNorm σ x ℓ)) := by group
    _ = x⁻¹ * (sigmaPartialNorm σ x ℓ * x) := by rw [hkey]
    _ = x⁻¹ * sigmaPartialNorm σ x ℓ * x := by group

theorem iterate_map_sigmaNormPow (σ : G →* G) (ℓ : ℕ) {x : G}
    (hσx : (⇑σ)^[ℓ] x = x) (r : ℕ) :
    (⇑σ)^[r] (sigmaNormPow σ ℓ x)
      = (sigmaPartialNorm σ x r)⁻¹ * sigmaNormPow σ ℓ x * sigmaPartialNorm σ x r := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc (⇑σ)^[r + 1] (sigmaNormPow σ ℓ x)
          = σ ((⇑σ)^[r] (sigmaNormPow σ ℓ x)) := iterate_succ_apply'' _ _ _
        _ = σ ((sigmaPartialNorm σ x r)⁻¹ * sigmaNormPow σ ℓ x * sigmaPartialNorm σ x r) := by
              rw [ih]
        _ = (σ (sigmaPartialNorm σ x r))⁻¹ * σ (sigmaNormPow σ ℓ x)
              * σ (sigmaPartialNorm σ x r) := by
              simp only [map_mul, map_inv]
        _ = (σ (sigmaPartialNorm σ x r))⁻¹ * (x⁻¹ * sigmaNormPow σ ℓ x * x)
              * σ (sigmaPartialNorm σ x r) := by rw [map_sigmaNormPow σ ℓ hσx]
        _ = (x * σ (sigmaPartialNorm σ x r))⁻¹ * sigmaNormPow σ ℓ x
              * (x * σ (sigmaPartialNorm σ x r)) := by group
        _ = (sigmaPartialNorm σ x (r + 1))⁻¹ * sigmaNormPow σ ℓ x
              * sigmaPartialNorm σ x (r + 1) := by rw [← sigmaPartialNorm_succ']

end PartialNorm

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem hom_sigmaPartialNorm (σ : G →* G) (τ : H →* H) (f : G →* H)
    (hf : ∀ x, f (σ x) = τ (f x)) (x : G) (r : ℕ) :
    f (sigmaPartialNorm σ x r) = sigmaPartialNorm τ (f x) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', map_mul, hf, ih]

theorem hom_sigmaNormPow (σ : G →* G) (τ : H →* H) (f : G →* H)
    (hf : ∀ x, f (σ x) = τ (f x)) (ℓ : ℕ) (x : G) :
    f (sigmaNormPow σ ℓ x) = sigmaNormPow τ ℓ (f x) :=
  hom_sigmaPartialNorm σ τ f hf x ℓ

theorem sigmaPartialNorm_id (x : G) (r : ℕ) :
    sigmaPartialNorm (MonoidHom.id G) x r = x ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [sigmaPartialNorm_succ', MonoidHom.id_apply, ih, pow_succ']

theorem sigmaPartialNorm_eq_prod_map_range (σ : G →* G) (x : G) (r : ℕ) :
    sigmaPartialNorm σ x r = ((List.range r).map fun i => (⇑σ)^[i] x).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ, ih, List.range_succ, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton]

theorem sigmaPartialNorm_of_map_eq (σ : G →* G) {x : G} (hx : σ x = x) (r : ℕ) :
    sigmaPartialNorm σ x r = x ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hiter : (⇑σ)^[r] x = x := Function.iterate_fixed hx r
      rw [sigmaPartialNorm_succ, ih, hiter, pow_succ]

end Transport

section CommTransport

variable {G : Type*} [CommGroup G]

theorem sigmaPartialNorm_eq_prod_range (σ : G →* G) (x : G) (r : ℕ) :
    sigmaPartialNorm σ x r = ∏ i ∈ Finset.range r, (⇑σ)^[i] x := by
  induction r with
  | zero => simp
  | succ r ih => rw [sigmaPartialNorm_succ, ih, Finset.prod_range_succ]

end CommTransport

section GLn

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {L : Type*} [CommRing L]

open Matrix

theorem iterate_generalLinearGroup_map_apply (σ : L →+* L) (r : ℕ) (δ : GL n L) (i j : n) :
    ((Matrix.GeneralLinearGroup.map (n := n) σ)^[r] δ) i j = (⇑σ)^[r] (δ i j) := by
  induction r generalizing δ with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        Matrix.GeneralLinearGroup.map_apply]

theorem iterate_generalLinearGroup_map_eq_self {σ : L →+* L} {ℓ : ℕ}
    (hσ : ∀ a : L, (⇑σ)^[ℓ] a = a) (δ : GL n L) :
    (Matrix.GeneralLinearGroup.map (n := n) σ)^[ℓ] δ = δ := by
  ext i j
  rw [iterate_generalLinearGroup_map_apply, hσ]

theorem det_sigmaNormPow (σ : L →+* L) (ℓ : ℕ) (δ : GL n L) :
    Matrix.GeneralLinearGroup.det (sigmaNormPow (Matrix.GeneralLinearGroup.map σ) ℓ δ)
      = sigmaNormPow (Units.map (σ : L →* L)) ℓ (Matrix.GeneralLinearGroup.det δ) :=
  hom_sigmaNormPow _ _ Matrix.GeneralLinearGroup.det
    (fun x => Matrix.GeneralLinearGroup.map_det σ x) ℓ δ

theorem sigmaNormPow_sigmaConj_generalLinearGroup {σ : L →+* L} {ℓ : ℕ}
    (hσ : ∀ a : L, (⇑σ)^[ℓ] a = a) (h δ : GL n L) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map σ) ℓ
        (h⁻¹ * δ * Matrix.GeneralLinearGroup.map σ h)
      = h⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map σ) ℓ δ * h :=
  sigmaNormPow_sigmaConjElt _ ℓ (iterate_generalLinearGroup_map_eq_self hσ h) δ

theorem map_sigmaNormPow_generalLinearGroup {σ : L →+* L} {ℓ : ℕ}
    (hσ : ∀ a : L, (⇑σ)^[ℓ] a = a) (δ : GL n L) :
    Matrix.GeneralLinearGroup.map σ (sigmaNormPow (Matrix.GeneralLinearGroup.map σ) ℓ δ)
      = δ⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map σ) ℓ δ * δ :=
  map_sigmaNormPow _ ℓ (iterate_generalLinearGroup_map_eq_self hσ δ)

theorem coe_generalLinearGroup_map (σ : L →+* L) (δ : GL n L) :
    ((Matrix.GeneralLinearGroup.map σ δ : GL n L) : Matrix n n L)
      = (δ : Matrix n n L).map σ := by
  ext i j
  rfl

theorem charpoly_sigmaNormPow_map {σ : L →+* L} {ℓ : ℕ}
    (hσ : ∀ a : L, (⇑σ)^[ℓ] a = a) (δ : GL n L) :
    (Matrix.charpoly
        ((sigmaNormPow (Matrix.GeneralLinearGroup.map σ) ℓ δ : GL n L) : Matrix n n L)).map σ
      = Matrix.charpoly
        ((sigmaNormPow (Matrix.GeneralLinearGroup.map σ) ℓ δ : GL n L) : Matrix n n L) := by
  rw [← Matrix.charpoly_map, ← coe_generalLinearGroup_map,
    map_sigmaNormPow_generalLinearGroup hσ δ, Units.val_mul, Units.val_mul,
    Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' δ _

end GLn

section Galois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [FiniteDimensional F L] [IsGalois F L] in

theorem forall_algEquiv_apply_eq_of_generator {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {a : L} (ha : σ a = a)
    (τ : L ≃ₐ[F] L) : τ a = a := by
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[F] L) a :=
    (Subgroup.zpowers_le).mpr (MulAction.mem_stabilizer_iff.mpr ha)
  exact MulAction.mem_stabilizer_iff.mp (hle (hgen τ))

theorem mem_range_algebraMap_of_generator_apply_eq {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {a : L} (ha : σ a = a) :
    a ∈ Set.range (algebraMap F L) :=
  (IsGalois.mem_range_algebraMap_iff_fixed a).mpr
    (forall_algEquiv_apply_eq_of_generator hgen ha)

theorem iterate_finrank_apply_of_generator {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (a : L) :
    (⇑σ)^[Module.finrank F L] a = a := by
  have horder : orderOf σ = Module.finrank F L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  rw [← AlgEquiv.coe_pow, ← horder, pow_orderOf_eq_one, AlgEquiv.one_apply]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem charpoly_sigmaNormPow_mem_lifts {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ : GL n L) :
    Matrix.charpoly
        ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ :
            GL n L) : Matrix n n L)
      ∈ Polynomial.lifts (algebraMap F L) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro k
  apply mem_range_algebraMap_of_generator_apply_eq hgen
  have h := charpoly_sigmaNormPow_map (n := n) (σ := (σ : L →+* L))
    (ℓ := Module.finrank F L) (fun a => iterate_finrank_apply_of_generator hgen a) δ
  have hk := congrArg (fun p => Polynomial.coeff p k) h
  simp only [Polynomial.coeff_map] at hk
  exact hk

theorem prod_algEquiv_eq_prod_range_of_generator {M : Type*} [CommMonoid M] {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (f : (L ≃ₐ[F] L) → M) :
    ∏ τ : L ≃ₐ[F] L, f τ = ∏ i ∈ Finset.range (Module.finrank F L), f (σ ^ i) := by
  classical
  have horder : orderOf σ = Module.finrank F L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  have hbij : Function.Bijective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [Fintype.card_fin, horder, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]⟩
  rw [← Fintype.prod_bijective _ hbij (fun i => f (σ ^ (i : ℕ))) f (fun _ => rfl),
    ← horder, ← Fin.prod_univ_eq_prod_range]

theorem coe_sigmaNormPow_units_eq_algebraMap_norm {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (z : Lˣ) :
    ((sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) z : Lˣ) : L)
      = algebraMap F L (Algebra.norm F (z : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, prod_algEquiv_eq_prod_range_of_generator hgen,
    sigmaNormPow_def, sigmaPartialNorm_eq_prod_range, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hiter : ∀ (r : ℕ) (w : Lˣ),
      (((Units.map ((σ : L →+* L) : L →* L))^[r] w : Lˣ) : L) = (⇑σ)^[r] (w : L) := by
    intro r
    induction r with
    | zero => intro w; rfl
    | succ r ih =>
        intro w
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map,
          MonoidHom.coe_coe, ih]
        rfl
  rw [hiter, AlgEquiv.coe_pow]

end Galois

end LT.TwistedNorm

namespace LT.TwistedNorm.GL2

open Matrix

section Companion

variable {K : Type*} [Field K]

def traceDetCompanion (t d : K) : Matrix (Fin 2) (Fin 2) K := !![0, -d; 1, t]

@[simp] theorem traceDetCompanion_apply_00 (t d : K) : traceDetCompanion t d 0 0 = 0 := rfl
@[simp] theorem traceDetCompanion_apply_01 (t d : K) : traceDetCompanion t d 0 1 = -d := rfl
@[simp] theorem traceDetCompanion_apply_10 (t d : K) : traceDetCompanion t d 1 0 = 1 := rfl
@[simp] theorem traceDetCompanion_apply_11 (t d : K) : traceDetCompanion t d 1 1 = t := rfl

theorem det_traceDetCompanion (t d : K) : (traceDetCompanion t d).det = d := by
  simp [Matrix.det_fin_two]

theorem trace_traceDetCompanion (t d : K) : (traceDetCompanion t d).trace = t := by
  simp [Matrix.trace_fin_two]

theorem traceDetCompanion_map {K' : Type*} [Field K'] (f : K →+* K') (t d : K) :
    (traceDetCompanion t d).map f = traceDetCompanion (f t) (f d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceDetCompanion]

theorem eq_smul_one_of_entries (A : Matrix (Fin 2) (Fin 2) K)
    (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) (hdiag : A 0 0 = A 1 1) :
    A = A 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, hdiag]

theorem entries_of_ne_smul_one (A : Matrix (Fin 2) (Fin 2) K)
    (hA : ∀ c : K, A ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    A 1 0 ≠ 0 ∨ A 0 1 ≠ 0 ∨ A 0 0 ≠ A 1 1 := by
  by_contra h
  push Not at h
  exact hA (A 0 0) (eq_smul_one_of_entries A h.1 h.2.1 h.2.2)

theorem mul_basis10_eq (A : Matrix (Fin 2) (Fin 2) K) :
    A * !![1, A 0 0; 0, A 1 0] = !![1, A 0 0; 0, A 1 0] * traceDetCompanion A.trace A.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, traceDetCompanion, Matrix.det_fin_two,
      Matrix.trace_fin_two] <;> ring

theorem mul_basis01_eq (A : Matrix (Fin 2) (Fin 2) K) :
    A * !![0, A 0 1; 1, A 1 1] = !![0, A 0 1; 1, A 1 1] * traceDetCompanion A.trace A.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, traceDetCompanion, Matrix.det_fin_two,
      Matrix.trace_fin_two] <;> ring

theorem mul_basis11_eq (A : Matrix (Fin 2) (Fin 2) K) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    A * !![1, A 0 0; 1, A 1 1] = !![1, A 0 0; 1, A 1 1] * traceDetCompanion A.trace A.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, traceDetCompanion, Matrix.det_fin_two,
      Matrix.trace_fin_two, h10, h01] <;> ring

theorem inv_mul_mul_eq_of_mul_eq {A P C : Matrix (Fin 2) (Fin 2) K} (hP : P.det ≠ 0)
    (h : A * P = P * C) : P⁻¹ * A * P = C := by
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]

theorem exists_conj_eq_traceDetCompanion (A : Matrix (Fin 2) (Fin 2) K)
    (hA : ∀ c : K, A ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ P : GL (Fin 2) K,
      (P : Matrix (Fin 2) (Fin 2) K)⁻¹ * A * P = traceDetCompanion A.trace A.det := by
  rcases entries_of_ne_smul_one A hA with h10 | h01 | hdiag
  · have hdet : Matrix.det !![1, A 0 0; 0, A 1 0] ≠ 0 := by
      simpa [Matrix.det_fin_two] using h10
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet,
      inv_mul_mul_eq_of_mul_eq hdet (mul_basis10_eq A)⟩
  · have hdet : Matrix.det !![0, A 0 1; 1, A 1 1] ≠ 0 := by
      simpa [Matrix.det_fin_two] using h01
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet,
      inv_mul_mul_eq_of_mul_eq hdet (mul_basis01_eq A)⟩
  · by_cases h10 : A 1 0 = 0
    · by_cases h01 : A 0 1 = 0
      · have hdet : Matrix.det !![1, A 0 0; 1, A 1 1] ≠ 0 := by
          simpa [Matrix.det_fin_two, sub_eq_zero] using (Ne.symm hdiag)
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet,
          inv_mul_mul_eq_of_mul_eq hdet (mul_basis11_eq A h10 h01)⟩
      · have hdet : Matrix.det !![0, A 0 1; 1, A 1 1] ≠ 0 := by
          simpa [Matrix.det_fin_two] using h01
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet,
          inv_mul_mul_eq_of_mul_eq hdet (mul_basis01_eq A)⟩
    · have hdet : Matrix.det !![1, A 0 0; 0, A 1 0] ≠ 0 := by
        simpa [Matrix.det_fin_two] using h10
      exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet,
        inv_mul_mul_eq_of_mul_eq hdet (mul_basis10_eq A)⟩

theorem exists_conj_eq_traceDetCompanion_units (A : GL (Fin 2) K)
    (hA : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ P : GL (Fin 2) K, ((P⁻¹ * A * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = traceDetCompanion (A : Matrix (Fin 2) (Fin 2) K).trace
          (A : Matrix (Fin 2) (Fin 2) K).det := by
  obtain ⟨P, hP⟩ := exists_conj_eq_traceDetCompanion (A : Matrix (Fin 2) (Fin 2) K) hA
  refine ⟨P, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact hP

theorem exists_conj_of_trace_eq_det_eq (A A' : GL (Fin 2) K)
    (hA : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hA' : ∀ c : K, (A' : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    (htr : (A : Matrix (Fin 2) (Fin 2) K).trace = (A' : Matrix (Fin 2) (Fin 2) K).trace)
    (hdet : (A : Matrix (Fin 2) (Fin 2) K).det = (A' : Matrix (Fin 2) (Fin 2) K).det) :
    ∃ Q : GL (Fin 2) K, A' = Q⁻¹ * A * Q := by
  obtain ⟨P, hP⟩ := exists_conj_eq_traceDetCompanion_units A hA
  obtain ⟨P', hP'⟩ := exists_conj_eq_traceDetCompanion_units A' hA'
  have hPP : P⁻¹ * A * P = P'⁻¹ * A' * P' := by
    apply Units.ext
    rw [hP, hP', htr, hdet]
  refine ⟨P * P'⁻¹, ?_⟩
  calc A' = P' * (P'⁻¹ * A' * P') * P'⁻¹ := by group
    _ = P' * (P⁻¹ * A * P) * P'⁻¹ := by rw [hPP]
    _ = (P * P'⁻¹)⁻¹ * A * (P * P'⁻¹) := by group

end Companion

section Descent

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem generalLinearGroup_map_smul_one_coe (c : F) (γ : GL (Fin 2) F)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ((Matrix.GeneralLinearGroup.map (algebraMap F L) γ : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L)
      = algebraMap F L c • (1 : Matrix (Fin 2) (Fin 2) L) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, hγ]
  fin_cases i <;> fin_cases j <;> simp

theorem conj_eq_self_of_coe_eq_smul_one {K : Type*} [Field K] (A P : GL (Fin 2) K) (c : K)
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    P⁻¹ * A * P = A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.coe_units_inv, Matrix.nonsing_inv_mul _ (Matrix.isUnits_det_units P)]

theorem exists_map_eq_conj_of_trace_det_mem (A : GL (Fin 2) L)
    (htr : (A : Matrix (Fin 2) (Fin 2) L).trace ∈ Set.range (algebraMap F L))
    (hdet : (A : Matrix (Fin 2) (Fin 2) L).det ∈ Set.range (algebraMap F L))
    (hsc : ∀ c : L, (A : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L) →
      c ∈ Set.range (algebraMap F L)) :
    ∃ γ : GL (Fin 2) F, ∃ P : GL (Fin 2) L,
      P⁻¹ * A * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ := by
  by_cases hscalar : ∃ c : L, (A : Matrix (Fin 2) (Fin 2) L) = c • (1 : Matrix (Fin 2) (Fin 2) L)
  ·
    obtain ⟨c, hc⟩ := hscalar
    obtain ⟨t, rfl⟩ := hsc c hc
    have ht0 : t ≠ 0 := by
      rintro rfl
      have hA := Matrix.isUnits_det_units A
      rw [hc, map_zero, zero_smul] at hA
      simp [Matrix.det_fin_two] at hA
    have ht : (t • (1 : Matrix (Fin 2) (Fin 2) F)).det ≠ 0 := by
      simp [ht0]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ ht, 1, ?_⟩
    apply Units.ext
    rw [inv_one, one_mul, mul_one, generalLinearGroup_map_smul_one_coe t _ rfl, hc]
  · push Not at hscalar
    obtain ⟨t, htt⟩ := htr
    obtain ⟨d, hdd⟩ := hdet
    obtain ⟨P, hP⟩ := exists_conj_eq_traceDetCompanion_units A hscalar
    have hd : (traceDetCompanion t d).det ≠ 0 := by
      rw [det_traceDetCompanion]
      intro h0
      have hA := Matrix.isUnits_det_units A
      rw [← hdd, h0, map_zero] at hA
      exact not_isUnit_zero hA
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, P, ?_⟩
    apply Units.ext
    rw [hP, ← htt, ← hdd, ← traceDetCompanion_map]
    rfl

theorem exists_conj_of_map_conj_map (γ γ' : GL (Fin 2) F) (P : GL (Fin 2) L)
    (h : Matrix.GeneralLinearGroup.map (algebraMap F L) γ'
      = P⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap F L) γ * P) :
    ∃ Q : GL (Fin 2) F, γ' = Q⁻¹ * γ * Q := by
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap F L)) := by
    intro x y hxy
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hij := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) i j) hxy
    simpa only [Matrix.GeneralLinearGroup.map_apply] using
      (algebraMap F L).injective hij
  by_cases hscalar : ∃ c : F, (γ : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F)
  ·
    obtain ⟨c, hc⟩ := hscalar
    refine ⟨1, ?_⟩
    rw [inv_one, one_mul, mul_one]
    apply hinj
    rw [h, conj_eq_self_of_coe_eq_smul_one _ P (algebraMap F L c)
      (generalLinearGroup_map_smul_one_coe c γ hc)]
  · push Not at hscalar

    have hscalar' : ∀ c : F,
        (γ' : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      intro c hc
      have hcen := conj_eq_self_of_coe_eq_smul_one _ P⁻¹ (algebraMap F L c)
        (generalLinearGroup_map_smul_one_coe c γ' hc)
      have hγ : Matrix.GeneralLinearGroup.map (algebraMap F L) γ
          = Matrix.GeneralLinearGroup.map (algebraMap F L) γ' := by
        rw [← hcen, h]; group
      exact hscalar c (by rw [hinj hγ, hc])

    have hmat : ((Matrix.GeneralLinearGroup.map (algebraMap F L) γ' : GL (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L)
        = ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * ((Matrix.GeneralLinearGroup.map (algebraMap F L) γ : GL (Fin 2) L) :
              Matrix (Fin 2) (Fin 2) L) * P := by
      rw [h, Units.val_mul, Units.val_mul]
    have hmapγ : ((Matrix.GeneralLinearGroup.map (algebraMap F L) γ : GL (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) = (γ : Matrix (Fin 2) (Fin 2) F).map (algebraMap F L) := by
      ext i j; rfl
    have hmapγ' : ((Matrix.GeneralLinearGroup.map (algebraMap F L) γ' : GL (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) = (γ' : Matrix (Fin 2) (Fin 2) F).map (algebraMap F L) := by
      ext i j; rfl
    have htr : (γ : Matrix (Fin 2) (Fin 2) F).trace = (γ' : Matrix (Fin 2) (Fin 2) F).trace := by
      apply (algebraMap F L).injective
      have := congrArg Matrix.trace hmat
      rw [Matrix.trace_units_conj', hmapγ, hmapγ'] at this
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add, map_add]
      simpa [Matrix.trace_fin_two] using this.symm
    have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det = (γ' : Matrix (Fin 2) (Fin 2) F).det := by
      apply (algebraMap F L).injective
      have := congrArg Matrix.det hmat
      rw [Matrix.det_units_conj', hmapγ, hmapγ', ← RingHom.mapMatrix_apply,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at this
      exact this.symm
    exact exists_conj_of_trace_eq_det_eq γ γ' hscalar hscalar' htr hdet

variable [FiniteDimensional F L] [IsGalois F L]

theorem exists_map_eq_conj_of_map_eq_conj {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (A B : GL (Fin 2) L)
    (hA : Matrix.GeneralLinearGroup.map (σ : L →+* L) A = B⁻¹ * A * B) :
    ∃ γ : GL (Fin 2) F, ∃ P : GL (Fin 2) L,
      P⁻¹ * A * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ := by

  have hfix : ∀ a : L, σ a = a → a ∈ Set.range (algebraMap F L) := by
    intro a ha
    refine (IsGalois.mem_range_algebraMap_iff_fixed a).mpr fun τ => ?_
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[F] L) a :=
      (Subgroup.zpowers_le).mpr (MulAction.mem_stabilizer_iff.mpr ha)
    exact MulAction.mem_stabilizer_iff.mp (hle (hgen τ))
  have hmat : ((A : Matrix (Fin 2) (Fin 2) L).map σ)
      = ((B⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * A * B := by
    have := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) hA
    simp only [Units.val_mul] at this
    rw [← this]
    ext i j; rfl
  apply exists_map_eq_conj_of_trace_det_mem
  · apply hfix
    have := congrArg Matrix.trace hmat
    rw [Matrix.trace_units_conj'] at this
    calc σ (A : Matrix (Fin 2) (Fin 2) L).trace
        = ((A : Matrix (Fin 2) (Fin 2) L).map σ).trace := by simp [Matrix.trace_fin_two]
      _ = (A : Matrix (Fin 2) (Fin 2) L).trace := this
  · apply hfix
    have := congrArg Matrix.det hmat
    rw [Matrix.det_units_conj'] at this
    calc σ (A : Matrix (Fin 2) (Fin 2) L).det
        = ((A : Matrix (Fin 2) (Fin 2) L).map σ).det := by simp [Matrix.det_fin_two]
      _ = (A : Matrix (Fin 2) (Fin 2) L).det := this
  · intro c hc
    apply hfix

    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) L => M 0 0) hmat
    have hcen : ((B⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * A * B = A := by
      rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.coe_units_inv,
        Matrix.nonsing_inv_mul _ (Matrix.isUnits_det_units B)]
    rw [hcen, hc] at h00
    simpa using h00

end Descent

end LT.TwistedNorm.GL2

namespace LT.TwistedNorm

open Matrix

section NormCorrespondence

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

theorem exists_map_eq_conj_sigmaNormPow {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ : GL (Fin 2) L) :
    ∃ γ : GL (Fin 2) F, ∃ P : GL (Fin 2) L,
      P⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ * P
        = Matrix.GeneralLinearGroup.map (algebraMap F L) γ :=
  GL2.exists_map_eq_conj_of_map_eq_conj hgen _ δ
    (map_sigmaNormPow_generalLinearGroup (n := Fin 2) (σ := (σ : L →+* L))
      (fun a => iterate_finrank_apply_of_generator hgen a) δ)

omit [FiniteDimensional F L] [IsGalois F L] in

theorem exists_conj_of_conj_eq_map_of_conj_eq_map {N : GL (Fin 2) L} {γ γ' : GL (Fin 2) F}
    {P P' : GL (Fin 2) L}
    (hγ : P⁻¹ * N * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ)
    (hγ' : P'⁻¹ * N * P' = Matrix.GeneralLinearGroup.map (algebraMap F L) γ') :
    ∃ Q : GL (Fin 2) F, γ' = Q⁻¹ * γ * Q := by
  refine GL2.exists_conj_of_map_conj_map γ γ' (P⁻¹ * P') ?_
  rw [← hγ, ← hγ']
  group

omit [FiniteDimensional F L] [IsGalois F L] in

theorem exists_conj_of_conj_sigmaNormPow_of_conj_sigmaNormPow {σ : L ≃ₐ[F] L} {ℓ : ℕ}
    {δ : GL (Fin 2) L} {γ γ' : GL (Fin 2) F} {P P' : GL (Fin 2) L}
    (hγ : P⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) ℓ δ * P
      = Matrix.GeneralLinearGroup.map (algebraMap F L) γ)
    (hγ' : P'⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) ℓ δ * P'
      = Matrix.GeneralLinearGroup.map (algebraMap F L) γ') :
    ∃ Q : GL (Fin 2) F, γ' = Q⁻¹ * γ * Q :=
  exists_conj_of_conj_eq_map_of_conj_eq_map hγ hγ'

theorem conj_sigmaNormPow_sigmaConj {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    {P : GL (Fin 2) L}
    (hγ : P⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ
      * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ)
    (h : GL (Fin 2) L) :
    (h⁻¹ * P)⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L)
        (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) * (h⁻¹ * P)
      = Matrix.GeneralLinearGroup.map (algebraMap F L) γ := by
  rw [sigmaNormPow_sigmaConj_generalLinearGroup (n := Fin 2) (σ := (σ : L →+* L))
    (fun a => iterate_finrank_apply_of_generator hgen a) h δ, ← hγ]
  group

omit [FiniteDimensional F L] [IsGalois F L] in

theorem algebraMap_det_eq_det_of_conj_eq_map {N : GL (Fin 2) L} {γ : GL (Fin 2) F}
    {P : GL (Fin 2) L} (hγ : P⁻¹ * N * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ) :
    algebraMap F L (γ : Matrix (Fin 2) (Fin 2) F).det = (N : Matrix (Fin 2) (Fin 2) L).det := by
  have h := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L).det) hγ
  simp only [Units.val_mul, Matrix.det_units_conj'] at h
  rw [h, RingHom.map_det, RingHom.mapMatrix_apply]
  rfl

theorem det_eq_norm_det_of_conj_sigmaNormPow {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    {P : GL (Fin 2) L}
    (hγ : P⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ
      * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ) :
    (γ : Matrix (Fin 2) (Fin 2) F).det = Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L).det) := by
  apply (algebraMap F L).injective
  rw [algebraMap_det_eq_det_of_conj_eq_map hγ]
  have hdet := congrArg (fun u : Lˣ => (u : L))
    (det_sigmaNormPow (n := Fin 2) (σ : L →+* L) (Module.finrank F L) δ)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hdet
  rw [hdet, coe_sigmaNormPow_units_eq_algebraMap_norm hgen]
  rfl

omit [FiniteDimensional F L] [IsGalois F L] in

theorem charpoly_map_eq_charpoly_of_conj_eq_map {N : GL (Fin 2) L} {γ : GL (Fin 2) F}
    {P : GL (Fin 2) L} (hγ : P⁻¹ * N * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ) :
    (γ : Matrix (Fin 2) (Fin 2) F).charpoly.map (algebraMap F L)
      = (N : Matrix (Fin 2) (Fin 2) L).charpoly := by
  have h := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L).charpoly) hγ
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj'] at h
  rw [h, ← Matrix.charpoly_map]
  rfl

end NormCorrespondence

end LT.TwistedNorm

namespace LT.TwistedNorm

section NormEquivVocab

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem isSigmaConj_iff_exists_eq_inv_mul_mul_map (σ : L →+* L) (δ₁ δ₂ : GL (Fin 2) L) :
    AutomorphicForm.IsSigmaConj σ δ₁ δ₂
      ↔ ∃ h : GL (Fin 2) L, δ₂ = h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map σ h := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [AutomorphicForm.sigmaConj, map_inv, inv_inv]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h⁻¹, by simp only [AutomorphicForm.sigmaConj, map_inv, inv_inv]⟩

def sigmaConjSetoid (σ : L ≃ₐ[F] L) : Setoid (GL (Fin 2) L) where
  r := AutomorphicForm.IsSigmaConj (σ : L →+* L)
  iseqv :=
    { refl := AutomorphicForm.IsSigmaConj.refl (σ : L →+* L)
      symm := by
        intro δ₁ δ₂ h
        obtain ⟨k, rfl⟩ := (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h
        exact (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mpr ⟨k⁻¹, by rw [map_inv]; group⟩
      trans := by
        intro δ₁ δ₂ δ₃ h h'
        obtain ⟨k, rfl⟩ := (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h
        obtain ⟨k', rfl⟩ := (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h'
        exact (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mpr ⟨k * k', by rw [map_mul]; group⟩ }

def SigmaConjClasses (σ : L ≃ₐ[F] L) : Type _ := Quotient (sigmaConjSetoid σ)

def SigmaConjClasses.mk (σ : L ≃ₐ[F] L) (δ : GL (Fin 2) L) : SigmaConjClasses σ :=
  Quotient.mk (sigmaConjSetoid σ) δ

theorem SigmaConjClasses.mk_surjective (σ : L ≃ₐ[F] L) :
    Function.Surjective (SigmaConjClasses.mk σ) :=
  Quotient.mk_surjective

theorem SigmaConjClasses.mk_eq_mk_iff {σ : L ≃ₐ[F] L} {δ₁ δ₂ : GL (Fin 2) L} :
    SigmaConjClasses.mk σ δ₁ = SigmaConjClasses.mk σ δ₂
      ↔ AutomorphicForm.IsSigmaConj (σ : L →+* L) δ₁ δ₂ :=
  Quotient.eq (r := sigmaConjSetoid σ)

theorem SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map {σ : L ≃ₐ[F] L} {δ₁ δ₂ : GL (Fin 2) L} :
    SigmaConjClasses.mk σ δ₁ = SigmaConjClasses.mk σ δ₂
      ↔ ∃ h : GL (Fin 2) L, δ₂ = h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h :=
  SigmaConjClasses.mk_eq_mk_iff.trans (isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _)

def IsNormRep (σ : L ≃ₐ[F] L) (γ : GL (Fin 2) F) (δ : GL (Fin 2) L) : Prop :=
  ∃ P : GL (Fin 2) L,
    P⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ * P
      = Matrix.GeneralLinearGroup.map (algebraMap F L) γ

end NormEquivVocab

section NormEquiv

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

noncomputable def normRep {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) : GL (Fin 2) F :=
  Classical.choose (exists_map_eq_conj_sigmaNormPow hgen δ)

theorem isNormRep_normRep {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) : IsNormRep σ (normRep hgen δ) δ :=
  Classical.choose_spec (exists_map_eq_conj_sigmaNormPow hgen δ)

theorem isConj_of_isNormRep_of_sigmaConj {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ₁ δ₂ : GL (Fin 2) L}
    {γ₁ γ₂ : GL (Fin 2) F} (h₁ : IsNormRep σ γ₁ δ₁) (h₂ : IsNormRep σ γ₂ δ₂)
    (h : ∃ k : GL (Fin 2) L, δ₂ = k⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) k) :
    IsConj γ₁ γ₂ := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  obtain ⟨k, rfl⟩ := h
  have h₁' := conj_sigmaNormPow_sigmaConj hgen hP₁ k
  obtain ⟨Q, hQ⟩ := exists_conj_of_conj_sigmaNormPow_of_conj_sigmaNormPow h₁' hP₂
  exact isConj_iff.mpr ⟨Q⁻¹, by rw [hQ]; group⟩

noncomputable def normClassMap {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) :
    SigmaConjClasses σ → ConjClasses (GL (Fin 2) F) :=
  Quotient.lift (fun δ => ConjClasses.mk (normRep hgen δ)) fun δ₁ δ₂ h =>
    ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_of_isNormRep_of_sigmaConj hgen (isNormRep_normRep hgen δ₁)
        (isNormRep_normRep hgen δ₂) ((isSigmaConj_iff_exists_eq_inv_mul_mul_map _ _ _).mp h))

theorem normClassMap_mk {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) :
    normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (normRep hgen δ) := rfl

theorem normClassMap_mk_eq_of_isNormRep {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : IsNormRep σ γ δ) :
    normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr
    (isConj_of_isNormRep_of_sigmaConj hgen (isNormRep_normRep hgen δ) h ⟨1, by simp⟩)

def IsNormClass {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (c : ConjClasses (GL (Fin 2) F)) : Prop :=
  c ∈ Set.range (normClassMap hgen)

theorem isNormClass_mk_iff {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) F) :
    IsNormClass hgen (ConjClasses.mk γ) ↔ ∃ δ : GL (Fin 2) L, IsNormRep σ γ δ := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨δ, rfl⟩ := SigmaConjClasses.mk_surjective σ c
    rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hc
    obtain ⟨Q, hQ⟩ := hc
    obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
    refine ⟨δ, P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, ?_⟩
    rw [← hQ, map_mul, map_mul, map_inv, ← hP]
    group
  · rintro ⟨δ, h⟩
    exact ⟨SigmaConjClasses.mk σ δ, normClassMap_mk_eq_of_isNormRep hgen h⟩

end NormEquiv

end LT.TwistedNorm

namespace LT.TwistedNorm

section Inhabitants

theorem sigmaPartialNorm_one_left {G : Type*} [Group G] (σ : G →* G) (r : ℕ) :
    sigmaPartialNorm σ 1 r = 1 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [sigmaPartialNorm_succ', ih, map_one, mul_one]

theorem sigmaNormPow_one_left {G : Type*} [Group G] (σ : G →* G) (ℓ : ℕ) :
    sigmaNormPow σ ℓ 1 = 1 :=
  sigmaPartialNorm_one_left σ ℓ

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem isNormRep_one (σ : L ≃ₐ[F] L) : IsNormRep σ (1 : GL (Fin 2) F) (1 : GL (Fin 2) L) :=
  ⟨1, by rw [sigmaNormPow_one_left, map_one]; group⟩

theorem nonempty_sigmaConjClasses (σ : L ≃ₐ[F] L) : Nonempty (SigmaConjClasses σ) :=
  ⟨SigmaConjClasses.mk σ 1⟩

variable [FiniteDimensional F L] [IsGalois F L]

theorem isNormClass_mk_one {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) :
    IsNormClass hgen (ConjClasses.mk (1 : GL (Fin 2) F)) :=
  (isNormClass_mk_iff hgen 1).mpr ⟨1, isNormRep_one σ⟩

theorem nonempty_isNormClass {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) :
    Nonempty {c : ConjClasses (GL (Fin 2) F) // IsNormClass hgen c} :=
  ⟨⟨_, isNormClass_mk_one hgen⟩⟩

end Inhabitants

end LT.TwistedNorm


