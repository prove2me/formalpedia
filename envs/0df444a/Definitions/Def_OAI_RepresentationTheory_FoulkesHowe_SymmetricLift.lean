-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
-- name    : OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:18:37.575898+00:00
-- url     : https://prove2.me/theorems/d39a5a9f-2bab-41eb-9735-5b8950bf8f84
-- title:
--   Symmetric multilinear maps descend to linear maps on $\mathrm{Sym}^n V$
-- statement:
--   Let $V,W$ be complex vector spaces of arbitrary (possibly infinite) dimension, $S(V)$ the symmetric algebra of $V$ over $\mathbb{C}$, $n\in\mathbb{N}$, and $\mathrm{Sym}^n V\subseteq S(V)$ the linear span of the products $[v_0,\dots,v_{n-1}]=v_0v_1\cdots v_{n-1}$ with $v_i\in V$. A multilinear map $T:V^n\to W$ is *symmetric* if $T(v_{\sigma(0)},\dots,v_{\sigma(n-1)})=T(v_0,\dots,v_{n-1})$ for every permutation $\sigma$ of $\{0,\dots,n-1\}$ and all $v\in V^n$. The file establishes the universal property of $\mathrm{Sym}^n V$.
--
--   1. **Descent.** For every symmetric multilinear map $T:V^n\to W$ there is a linear map $L:\mathrm{Sym}^n V\to W$ with
--   $$L\bigl([v_0,\dots,v_{n-1}]\bigr)=T(v_0,\dots,v_{n-1})\qquad\text{for all }v_0,\dots,v_{n-1}\in V;$$
--   a chosen such map is denoted $\widehat T$.
--   2. **Uniqueness.** Two linear maps $\mathrm{Sym}^n V\to W$ that agree on all products $[v_0,\dots,v_{n-1}]$ are equal. In particular $\widehat T$ is the only map with the property in item 1.
--   3. **Linearity of descent.** The symmetric multilinear maps $V^n\to W$ form a linear subspace $\mathcal{S}_n(V,W)$ of the space of all multilinear maps $V^n\to W$, and $T\mapsto\widehat T$ is a $\mathbb{C}$-linear map $\mathcal{S}_n(V,W)\to\mathrm{Hom}_{\mathbb{C}}(\mathrm{Sym}^n V,W)$.
--   4. **Auxiliary construction.** Fix a basis $(e_k)_{k\in K}$ of $V$. The *exponent* of a tuple $f:\{0,\dots,n-1\}\to K$ is the finitely supported function $d_f:K\to\mathbb{N}$, $d_f(k)=\#\{i: f(i)=k\}$, and two tuples with the same exponent differ by a permutation of $\{0,\dots,n-1\}$. Identifying $S(V)$ with the polynomial ring $\mathbb{C}[X_k:k\in K]$ via the basis, define the linear map $S(V)\to W$ sending each monomial $X^{d}$ to $T(e_{f(0)},\dots,e_{f(n-1)})$ if $d=d_f$ for some tuple $f$ (one such $f$ being chosen), and to $0$ otherwise. When $T$ is symmetric this map sends $[v_0,\dots,v_{n-1}]$ to $T(v_0,\dots,v_{n-1})$ for all $v_i\in V$, and its restriction to $\mathrm{Sym}^n V$ provides the map of item 1.
--
--   This universal property is the standard tool for defining linear maps out of symmetric powers by prescribing their values on products, for instance the pairing between $\mathrm{Sym}^n X$ and $\mathrm{Sym}^n Y$ induced by a bilinear form. No finiteness assumption on $V$ is needed.
--
--   **Formalization Note** `exists_symPow_lift` is the existence statement and `symPowLift T hT` the chosen map, with defining property `symPowLift_symMonomial`; `SymmetricLift.linearMap_ext` is the uniqueness statement; `symmetricMultilinearSubmodule` and `symPowLiftLinear` give item 3. The auxiliary objects `tupleExponent`, `liftValues` and `liftOnAlgebra` use `Module.Free.chooseBasis` and Mathlib's `SymmetricAlgebra.equivMvPolynomial`; `dite_eq_left` is a private helper.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SymmetricLift.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SymmetricLift.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Module

namespace Problem346
namespace SymmetricLift

variable {κ : Type*} {n : ℕ}

 def tupleExponent (f : Fin n → κ) : κ →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

 lemma tupleExponent_apply (f : Fin n → κ) (k : κ) :
    tupleExponent f k = Fintype.card {i // f i = k} := by
  classical
  rw [Fintype.card_subtype]
  simp only [tupleExponent, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_boole, Nat.cast_id]

 lemma exists_perm_of_exponent_eq (f g : Fin n → κ)
    (h : tupleExponent f = tupleExponent g) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, g (σ i) = f i := by
  classical
  have hc (k : κ) : Fintype.card {i // f i = k} = Fintype.card {i // g i = k} := by
    simpa only [tupleExponent_apply] using congrArg (fun d : κ →₀ ℕ => d k) h
  let e (k : κ) : {i // f i = k} ≃ {i // g i = k} :=
    Fintype.equivOfCardEq (hc k)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

 def liftValues (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W) (d : κ →₀ ℕ) : W :=
  if h : ∃ f : Fin n → κ, tupleExponent f = d then
    T (fun i => b (Classical.choose h i)) else 0

 lemma liftValues_tuple (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (f : Fin n → κ) : liftValues b T (tupleExponent f) = T (fun i => b (f i)) := by
  let h : ∃ g : Fin n → κ, tupleExponent g = tupleExponent f := ⟨f, rfl⟩
  rw [liftValues, dite_eq_left h]
  obtain ⟨σ, hσ⟩ := exists_perm_of_exponent_eq (Classical.choose h) f (Classical.choose_spec h)
  convert hT σ (fun i => b (f i)) using 1
  congr 1
  funext i
  rw [hσ]

 def liftOnAlgebra (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W) :
    SymmetricAlgebra ℂ V →ₗ[ℂ] W :=
  ((MvPolynomial.basisMonomials κ ℂ).constr ℂ (liftValues b T)).comp
    (SymmetricAlgebra.equivMvPolynomial b).toLinearMap

 lemma liftOnAlgebra_basis (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (f : Fin n → κ) :
    liftOnAlgebra b T (symMonomialRaw n V (fun i => b (f i))) = T (fun i => b (f i)) := by
  have hp : (∏ i, MvPolynomial.X (f i) : MvPolynomial κ ℂ) =
      MvPolynomial.monomial (tupleExponent f) 1 := by
    simp only [tupleExponent, MvPolynomial.monomial_sum_one, MvPolynomial.X]
  change ((MvPolynomial.basisMonomials κ ℂ).constr ℂ (liftValues b T))
    ((SymmetricAlgebra.equivMvPolynomial b) (∏ i, SymmetricAlgebra.ι ℂ V (b (f i)))) = _
  rw [map_prod]
  simp only [SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [hp]
  change ((MvPolynomial.basisMonomials κ ℂ).constr ℂ (liftValues b T))
    ((MvPolynomial.basisMonomials κ ℂ) (tupleExponent f)) = _
  rw [Basis.constr_basis, liftValues_tuple b T hT]

 lemma liftOnAlgebra_monomial (b : Basis κ ℂ V)
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (v : Fin n → V) :
    liftOnAlgebra b T (symMonomialRaw n V v) = T v := by
  let M : MultilinearMap ℂ (fun _ : Fin n => V) (SymmetricAlgebra ℂ V) :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
      (fun _ => SymmetricAlgebra.ι ℂ V)
  have h : (liftOnAlgebra b T).compMultilinearMap M = T := by
    apply Basis.ext_multilinear (fun _ => b)
    intro f
    exact liftOnAlgebra_basis b T hT f
  exact congrArg (fun S : MultilinearMap ℂ (fun _ : Fin n => V) W => S v) h

end SymmetricLift

/-- A symmetric multilinear map descends to the homogeneous symmetric-power submodule. -/
theorem exists_symPow_lift {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v) :
    ∃ L : SymPow n V →ₗ[ℂ] W, ∀ v, L (symMonomial n V v) = T v := by
  let b := Module.Free.chooseBasis ℂ V
  refine ⟨(SymmetricLift.liftOnAlgebra b T).domRestrict (symPowSubmodule n V), ?_⟩
  intro v
  exact SymmetricLift.liftOnAlgebra_monomial b T hT v

/-- A chosen linear descent of a symmetric multilinear map. -/
def symPowLift {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v) :
    SymPow n V →ₗ[ℂ] W :=
  Classical.choose (exists_symPow_lift T hT)

@[simp] theorem symPowLift_symMonomial {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hT : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), T (fun i => v (σ i)) = T v)
    (v : Fin n → V) : symPowLift T hT (symMonomial n V v) = T v :=
  Classical.choose_spec (exists_symPow_lift T hT) v

namespace SymmetricLift

/-- Linear maps out of a symmetric power are determined by products. -/
theorem linearMap_ext {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {f g : SymPow n V →ₗ[ℂ] W}
    (h : ∀ v, f (symMonomial n V v) = g (symMonomial n V v)) : f = g := by
  apply (Submodule.linearMap_eq_iff_of_eq_span f g rfl).2
  rintro ⟨x, ⟨v, rfl⟩⟩
  exact h v

end SymmetricLift

/-- The submodule of multilinear maps invariant under permutations of their arguments. -/
def symmetricMultilinearSubmodule (n : ℕ) (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    Submodule ℂ (MultilinearMap ℂ (fun _ : Fin n => V) W) where
  carrier := {T | ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V),
    T (fun i => v (σ i)) = T v}
  zero_mem' := by simp
  add_mem' := by
    intro T U hT hU σ v
    simp only [add_apply, hT σ v, hU σ v]
  smul_mem' := by
    intro c T hT σ v
    simp only [smul_apply, hT σ v]

/-- Descent from symmetric multilinear maps is linear in the map being descended. -/
def symPowLiftLinear (n : ℕ) (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    symmetricMultilinearSubmodule n V W →ₗ[ℂ] (SymPow n V →ₗ[ℂ] W) where
  toFun T := symPowLift T.val T.property
  map_add' T U := by
    apply SymmetricLift.linearMap_ext
    intro v
    exact (symPowLift_symMonomial (T + U).val (T + U).property v).trans
      (congrArg₂ (fun left right : W => left + right)
        (symPowLift_symMonomial T.val T.property v).symm
        (symPowLift_symMonomial U.val U.property v).symm)
  map_smul' c T := by
    apply SymmetricLift.linearMap_ext
    intro v
    exact (symPowLift_symMonomial (c • T).val (c • T).property v).trans
      (congrArg (c • ·) (symPowLift_symMonomial T.val T.property v).symm)

@[simp] theorem symPowLiftLinear_symMonomial {n : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : symmetricMultilinearSubmodule n V W) (v : Fin n → V) :
    symPowLiftLinear n V W T (symMonomial n V v) = T.val v :=
  symPowLift_symMonomial T.val T.property v

end Problem346

end

end OAI


