-- Prove2me | Definitions.Def_GaloisRep_CompletionBridge
-- name    : GaloisRep_CompletionBridge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/94c47fca-5f30-5f42-a9c6-cd22320940e8
-- title:
--   A q-adic place of Q​ and local-to-global Galois map
-- statement:
--   Fix a rational prime $q$. [`padicEmbedding q`](../def/GaloisRep_CompletionBridge.html#L17) is a $\mathbb{Q}$-algebra embedding $\iota_q : \overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_q$, where $\overline{\mathbb{Q}}$ is Mathlib's `AlgebraicClosure ℚ` and $\overline{\mathbb{Q}}_q$ is `PadicAlgCl q`, obtained by lifting along the algebraic extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ into an algebraically closed field; the accompanying local instances record that $\overline{\mathbb{Q}}$ is an algebraic closure of $\mathbb{Q}$ and normal over it. [`padicIntegers q`](../def/GaloisRep_CompletionBridge.html#L20) is the valuation subring attached to the $\mathbb{R}_{\ge 0}$-valued valuation of $\overline{\mathbb{Q}}_q$, i.e. the closed unit ball $\{x : \lVert x\rVert \le 1\}$, and [`padicPlace q`](../def/GaloisRep_CompletionBridge.html#L25) is its preimage under $\iota_q$: a valuation subring of $\overline{\mathbb{Q}}$, consisting of those $x$ with $\lVert \iota_q x\rVert \le 1$, which is the place of $\overline{\mathbb{Q}}$ above $q$ cut out by the chosen embedding. Transporting the $\overline{\mathbb{Q}}$-algebra structure on $\overline{\mathbb{Q}}_q$ along $\iota_q$, together with the scalar towers over $\mathbb{Q}$, [`localGaloisToGlobal q`](../def/GaloisRep_CompletionBridge.html#L41) is the monoid homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ given by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}}$. Three theorems accompany this: the compatibility $\iota_q(\text{localGaloisToGlobal}\,q\,\tau\,(x)) = \tau(\iota_q x)$ for $x \in \overline{\mathbb{Q}}$; the isometry statement $\lVert \tau y\rVert = \lVert y\rVert$ for every $\mathbb{Q}_q$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}_q$ and $y \in \overline{\mathbb{Q}}_q$, via invariance of the spectral norm; and, as a consequence, that the image of [`localGaloisToGlobal q`](../def/GaloisRep_CompletionBridge.html#L41) lies in the decomposition subgroup of [`padicPlace q`](../def/GaloisRep_CompletionBridge.html#L25) over $\mathbb{Q}$, that is, in the stabiliser of this valuation subring under the Galois action.
--
--   **Relation to Mathlib.** The completed algebraic closure `PadicAlgCl`, valuation subrings and their decomposition subgroups, spectral-norm invariance and `AlgEquiv.restrictNormalHom` are Mathlib's; what is added here is the bridge between them — a fixed embedding $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_q$, the induced place of $\overline{\mathbb{Q}}$ above $q$, and the resulting map from the local to the global Galois group.
--
--   **Where it is used.** These objects provide the finite places of $\overline{\mathbb{Q}}$ and the local-at-$q$ Galois structure used throughout the argument: valuation subrings above $q$ are what the project's ramification predicates quantify over ([`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16), `inertiaSubgroupIn`, and the unramifiedness conditions on torsion of the Frey curve), and [`localGaloisToGlobal`](../def/GaloisRep_CompletionBridge.html#L41) lets local Galois data at $q$ be compared with the global representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_CompletionBridge.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal Pointwise

local instance isAlgebraicQbar_cb : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_cb : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar_cb : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]

noncomputable def padicEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl q :=
  IsAlgClosed.lift

noncomputable abbrev padicIntegers : ValuationSubring (PadicAlgCl q) :=
  (Valued.v : Valuation (PadicAlgCl q) ℝ≥0).valuationSubring

lemma mem_padicIntegers_iff {x : PadicAlgCl q} : x ∈ padicIntegers q ↔ ‖x‖₊ ≤ 1 := Iff.rfl

noncomputable def padicPlace : ValuationSubring (AlgebraicClosure ℚ) :=
  (padicIntegers q).comap (padicEmbedding q).toRingHom

theorem mem_padicPlace_iff {x : AlgebraicClosure ℚ} :
    x ∈ padicPlace q ↔ ‖padicEmbedding q x‖₊ ≤ 1 := Iff.rfl

section Galois

noncomputable local instance instAlgebraQbarPadic : Algebra (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  (padicEmbedding q).toRingHom.toAlgebra
local instance instTowerQbarPadic :
    IsScalarTower ℚ (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
local instance instTowerQqPadic : IsScalarTower ℚ ℚ_[q] (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

noncomputable def localGaloisToGlobal :
    (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := PadicAlgCl q) (AlgebraicClosure ℚ)).comp
    (MonoidHom.mk' (fun τ => τ.restrictScalars ℚ) (fun _ _ => rfl))

theorem padicEmbedding_localGaloisToGlobal (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (x : AlgebraicClosure ℚ) :
    padicEmbedding q (localGaloisToGlobal q τ x) = τ (padicEmbedding q x) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem nnnorm_padicAlgCl_algEquiv (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)
    (y : PadicAlgCl q) : ‖τ y‖₊ = ‖y‖₊ := by
  ext
  exact (spectralNorm_eq_of_equiv τ y).symm

theorem localGaloisToGlobal_mem_decompositionSubgroup
    (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    localGaloisToGlobal q τ ∈ (padicPlace q).decompositionSubgroup ℚ := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (localGaloisToGlobal q τ)⁻¹ = localGaloisToGlobal q τ⁻¹ := (map_inv _ τ).symm
  rw [AlgEquiv.smul_def, hinv]
  rw [mem_padicPlace_iff, mem_padicPlace_iff, padicEmbedding_localGaloisToGlobal,
    nnnorm_padicAlgCl_algEquiv]

end Galois


