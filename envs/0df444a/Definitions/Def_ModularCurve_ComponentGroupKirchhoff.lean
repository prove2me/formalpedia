-- Prove2me | Definitions.Def_ModularCurve_ComponentGroupKirchhoff
-- name    : ModularCurve_ComponentGroupKirchhoff
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f5753837-9a1f-5248-82e1-b3a8312556bd
-- title:
--   Difference basis of the character lattice; Kirchhoff count
-- statement:
--   Throughout, $\iota$ is a finite type and $e : \iota \to \mathbb{N}$ a width function; the character lattice `characterLattice ι` is the kernel of $D \mapsto \sum_{x} D(x)$ inside $\mathbb{Z}^{\iota}$, and `gramMap e` sends $D$ to the functional $D' \mapsto \sum_{x} e_x\, D(x) D'(x)$ on that lattice. The first part fixes a presentation of $\iota$ as a marked point together with a complementary index type, in the form of an equivalence $\sigma : \mathrm{Option}\,\kappa \simeq \iota$ with $\kappa$ finite, and writes $\sigma(\mathrm{none})$ for the marked point. For $k : \kappa$, `diffChar σ k` is the degree-zero element $\mathbf{1}_{\sigma(\mathrm{some}\,k)} - \mathbf{1}_{\sigma(\mathrm{none})}$ of the character lattice; its values are computed at the marked point ($-1$) and at the other points ($\delta_{mk}$). The linear map `coordOf σ` reads off the coordinates of an element of the character lattice at the unmarked points, $D \mapsto (D(\sigma(\mathrm{some}\,k)))_{k}$; it is injective and surjective, because the degree-zero condition forces $D(\sigma(\mathrm{none})) = -\sum_k D(\sigma(\mathrm{some}\,k))$ (recorded as `coe_apply_base_eq_neg_sum`). The resulting isomorphism `coordOfEquiv σ` onto $\mathbb{Z}^{\kappa}$ transports the standard basis to `diffBasisOf σ`, a $\mathbb{Z}$-basis of the character lattice indexed by $\kappa$ whose $k$-th vector is `diffChar σ k`. In this basis the Gram form is diagonal-plus-constant: `gramMap_diffChar_diffChar` states that the pairing of `diffChar σ k` with `diffChar σ l` equals $\delta_{kl}\, e_{\sigma(\mathrm{some}\,k)} + e_{\sigma(\mathrm{none})}$.
--
--   The second part defines the natural number $\mathrm{kirchhoffCount}(e) = \sum_{x \in \iota} \prod_{y \neq x} e_y$, and records that it is positive when $\iota$ is nonempty and every $e_x$ is positive, and that it equals the cardinality of $\iota$ when $e$ is constant equal to $1$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here (`Basis`, `Pi.basisFun`, `Module.Dual`, linear equivalences from bijective maps); the degree-zero character lattice, its difference basis and the weighted count $\sum_x \prod_{y \ne x} e_y$ are the project's own definitions.
--
--   **Where it is used.** These are the combinatorial ingredients for the order formula of the component group attached to a width function, namely the cokernel of `gramMap e` in the dual of the character lattice: in the difference basis the Gram matrix is diagonal-plus-constant, and its determinant is the Kirchhoff count. Such component groups of Jacobians at primes of multiplicative reduction enter the level-lowering step of the proof of Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ComponentGroupKirchhoff.lean

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroupOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset Module

section DifferenceBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

def diffChar (σ : Option κ ≃ ι) (k : κ) : characterLattice ι :=
  ⟨fun x => (if x = σ (some k) then 1 else 0) - (if x = σ none then 1 else 0), by
    rw [mem_characterLattice, Finset.sum_sub_distrib,
      Fintype.sum_ite_eq' (σ (some k)) (fun _ => (1 : ℤ)),
      Fintype.sum_ite_eq' (σ none) (fun _ => (1 : ℤ))]
    norm_num⟩

@[simp] theorem diffChar_coe_apply (σ : Option κ ≃ ι) (k : κ) (x : ι) :
    (diffChar σ k).1 x =
      (if x = σ (some k) then 1 else 0) - (if x = σ none then 1 else 0) :=
  rfl

theorem diffChar_apply_base (σ : Option κ ≃ ι) (k : κ) :
    (diffChar σ k).1 (σ none) = -1 := by
  rw [diffChar_coe_apply, if_pos rfl,
    if_neg (fun h => Option.some_ne_none k (σ.injective h).symm), zero_sub]

theorem diffChar_apply_some (σ : Option κ ≃ ι) (k m : κ) :
    (diffChar σ k).1 (σ (some m)) = if m = k then 1 else 0 := by
  rw [diffChar_coe_apply, if_neg (fun h => Option.some_ne_none m (σ.injective h)), sub_zero]
  by_cases h : m = k
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg fun hc => h (Option.some_injective κ (σ.injective hc))]

def coordOf (σ : Option κ ≃ ι) : characterLattice ι →ₗ[ℤ] (κ → ℤ) :=
  LinearMap.pi fun k =>
    (LinearMap.proj (σ (some k))).comp (characterLattice ι).subtype

@[simp] theorem coordOf_apply (σ : Option κ ≃ ι) (D : characterLattice ι) (k : κ) :
    coordOf σ D k = D.1 (σ (some k)) :=
  rfl

theorem coe_apply_base_eq_neg_sum (σ : Option κ ≃ ι) (D : characterLattice ι) :
    D.1 (σ none) = - ∑ k : κ, D.1 (σ (some k)) := by
  have hdeg : ∑ o : Option κ, D.1 (σ o) = 0 := by
    rw [Equiv.sum_comp σ (D.1 : ι → ℤ)]
    exact mem_characterLattice.mp D.2
  rw [Fintype.sum_option] at hdeg
  linarith

theorem coordOf_injective (σ : Option κ ≃ ι) : Function.Injective (coordOf σ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  have hsome : ∀ k : κ, D.1 (σ (some k)) = 0 := fun k => congrFun hD k
  have hnone : D.1 (σ none) = 0 := by
    rw [coe_apply_base_eq_neg_sum σ D]
    simp [hsome]
  apply Subtype.ext
  funext x
  obtain ⟨o, rfl⟩ := σ.surjective x
  cases o with
  | none => exact hnone
  | some k => exact hsome k

theorem coordOf_diffChar (σ : Option κ ≃ ι) (k l : κ) :
    coordOf σ (diffChar σ k) l = if l = k then 1 else 0 := by
  rw [coordOf_apply, diffChar_apply_some]

theorem coordOf_surjective (σ : Option κ ≃ ι) : Function.Surjective (coordOf σ) := by
  intro v
  refine ⟨∑ k : κ, v k • diffChar σ k, ?_⟩
  funext l
  rw [map_sum]
  rw [Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, coordOf_diffChar, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ l v]
  simp

def coordOfEquiv (σ : Option κ ≃ ι) : characterLattice ι ≃ₗ[ℤ] (κ → ℤ) :=
  LinearEquiv.ofBijective (coordOf σ) ⟨coordOf_injective σ, coordOf_surjective σ⟩

@[simp] theorem coordOfEquiv_apply (σ : Option κ ≃ ι) (D : characterLattice ι) :
    coordOfEquiv σ D = coordOf σ D :=
  rfl

def diffBasisOf (σ : Option κ ≃ ι) : Basis κ ℤ (characterLattice ι) :=
  (Pi.basisFun ℤ κ).map (coordOfEquiv σ).symm

theorem diffBasisOf_apply (σ : Option κ ≃ ι) (k : κ) :
    diffBasisOf σ k = diffChar σ k := by
  apply (coordOfEquiv σ).injective
  have h : (coordOfEquiv σ) (diffBasisOf σ k) = Pi.single k 1 := by
    show (coordOfEquiv σ) (((Pi.basisFun ℤ κ).map (coordOfEquiv σ).symm) k) = Pi.single k 1
    rw [Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  rw [h]
  funext l
  rw [coordOfEquiv_apply, coordOf_diffChar, Pi.single_apply]

theorem gramMap_diffChar_diffChar (e : ι → ℕ) (σ : Option κ ≃ ι) (k l : κ) :
    gramMap e (diffChar σ k) (diffChar σ l) =
      (if k = l then (e (σ (some k)) : ℤ) else 0) + (e (σ none) : ℤ) := by
  rw [gramMap_apply]
  have key : ∑ x : ι, (e x : ℤ) * ((diffChar σ k).1 x * (diffChar σ l).1 x) =
      ∑ o : Option κ, (e (σ o) : ℤ) * ((diffChar σ k).1 (σ o) * (diffChar σ l).1 (σ o)) :=
    (Fintype.sum_equiv σ _ _ fun _ => rfl).symm
  rw [key, Fintype.sum_option, diffChar_apply_base, diffChar_apply_base]
  simp_rw [diffChar_apply_some]
  have hsum : ∑ m : κ, (e (σ (some m)) : ℤ) *
      ((if m = k then (1 : ℤ) else 0) * (if m = l then (1 : ℤ) else 0)) =
      if k = l then (e (σ (some k)) : ℤ) else 0 := by
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      have hterm : ∀ m : κ, (e (σ (some m)) : ℤ) *
          ((if m = k then (1 : ℤ) else 0) * (if m = k then (1 : ℤ) else 0)) =
          if m = k then (e (σ (some m)) : ℤ) else 0 := fun m => by
        by_cases hmk : m = k <;> simp [hmk]
      rw [Finset.sum_congr rfl fun m _ => hterm m]
      exact Fintype.sum_ite_eq' k fun m => (e (σ (some m)) : ℤ)
    · rw [if_neg hkl]
      have hterm : ∀ m : κ, (e (σ (some m)) : ℤ) *
          ((if m = k then (1 : ℤ) else 0) * (if m = l then (1 : ℤ) else 0)) = 0 := fun m => by
        by_cases hmk : m = k
        · subst hmk
          simp [hkl]
        · simp [hmk]
      rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_const_zero]
  rw [hsum]
  ring

end DifferenceBasis

section KirchhoffCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def kirchhoffCount (e : ι → ℕ) : ℕ :=
  ∑ x : ι, ∏ y ∈ Finset.univ.erase x, e y

theorem kirchhoffCount_def (e : ι → ℕ) :
    kirchhoffCount e = ∑ x : ι, ∏ y ∈ Finset.univ.erase x, e y :=
  rfl

theorem kirchhoffCount_pos [Nonempty ι] {e : ι → ℕ} (he : ∀ x, 0 < e x) :
    0 < kirchhoffCount e := by
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  rw [kirchhoffCount_def]
  refine Finset.sum_pos' (fun x _ => Nat.zero_le _) ⟨x₀, Finset.mem_univ x₀, ?_⟩
  exact Finset.prod_pos fun y _ => he y

theorem kirchhoffCount_const_one : kirchhoffCount (fun _ : ι => 1) = Fintype.card ι := by
  rw [kirchhoffCount_def]
  trans ∑ _x : ι, 1
  · exact Finset.sum_congr rfl fun x _ => Finset.prod_const_one
  · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

end KirchhoffCount

end ModularCurve


