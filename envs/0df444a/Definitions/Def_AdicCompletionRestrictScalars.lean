-- Prove2me | Definitions.Def_AdicCompletionRestrictScalars
-- name    : AdicCompletionRestrictScalars
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/970818a6-9177-5b65-800d-de7642fe328c
-- title:
--   Adic completion of an algebra along an extended ideal
-- statement:
--   Throughout, $A$ is a commutative ring, $B$ a commutative $A$-algebra, and $\mathfrak p$ an ideal of $A$; write $\mathfrak p B$ for the image ideal $\mathfrak p \cdot B$ obtained as `𝔭.map (algebraMap A B)`. The first result, `restrictScalars_map_pow_smul_top`, records that the two natural filtrations of $B$ coincide as $A$-submodules: for each $n$, the $B$-submodule $(\mathfrak p B)^n \cdot B$ of $B$, viewed as an $A$-submodule by restriction of scalars, is equal to the $A$-submodule $\mathfrak p^n \cdot B$ of $B$. From this, `levelRestrictScalarsEquiv` is, for each $n$, the $A$-linear equivalence
--   $$B/\bigl((\mathfrak p B)^n\cdot B\bigr) \;\simeq\; B/\bigl(\mathfrak p^n\cdot B\bigr),$$
--   and `levelRestrictScalarsEquiv_mk` states that it carries the class of $b \in B$ to the class of $b$; `transitionMap_levelRestrictScalarsEquiv` states that for $m \le n$ these level equivalences commute with the transition maps of the two inverse systems, i.e. the square formed by the transition map for $\mathfrak p B$ over $B$ and the transition map for $\mathfrak p$ over $B$ commutes.
--
--   The main definition, `restrictScalarsEquiv`, assembles these into an $A$-linear equivalence
--   $$\widehat{B}_{\mathfrak p B} \;\simeq\; \widehat{B}_{\mathfrak p},$$
--   between the $\mathfrak p B$-adic completion of $B$ as a module over itself and the $\mathfrak p$-adic completion of $B$ as an $A$-module: a compatible family $(x_n)_n$ of classes modulo $(\mathfrak p B)^n \cdot B$ is sent to the family of the same classes read modulo $\mathfrak p^n \cdot B$, compatibility being exactly the commutation with transition maps, and the inverse is given levelwise by the inverse equivalences. Finally `restrictScalarsEquiv_of` and `restrictScalarsEquiv_symm_of` state that this equivalence and its inverse are compatible with the canonical maps from $B$ into the two completions: the image of $b \in B$ in $\widehat{B}_{\mathfrak p B}$ corresponds to the image of $b$ in $\widehat{B}_{\mathfrak p}$.
--
--   **Relation to Mathlib.** Mathlib provides `AdicCompletion I M` for an ideal $I$ of a ring and a module $M$ over that ring, together with the level quotients, transition maps and the canonical map `of`. The identification of the $\mathfrak p B$-adic completion of $B$ over itself with the $\mathfrak p$-adic completion of $B$ as an $A$-module is added here, in Mathlib's `AdicCompletion` namespace.
--
--   **Where it is used.** The equivalence lets statements about the $\mathfrak p$-adic completion of an $A$-algebra $B$ be transferred to the completion of $B$ at the extended ideal $\mathfrak p B$, so that results available for the adic completion of a ring at one of its own ideals can be applied in the relative setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AdicCompletionRestrictScalars.lean

import Mathlib.RingTheory.AdicCompletion.Algebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u₁ u₂

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

theorem restrictScalars_map_pow_smul_top (n : ℕ) :
    (((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A) =
      (𝔭 ^ n • ⊤ : Submodule A B) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

noncomputable def levelRestrictScalarsEquiv (n : ℕ) :
    (B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) ≃ₗ[A]
      B ⧸ (𝔭 ^ n • ⊤ : Submodule A B) :=
  (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    (Submodule.quotEquivOfEq _ _ (restrictScalars_map_pow_smul_top B 𝔭 n))

theorem levelRestrictScalarsEquiv_mk (n : ℕ) (b : B) :
    levelRestrictScalarsEquiv B 𝔭 n (Submodule.Quotient.mk b) = Submodule.Quotient.mk b :=
  rfl

theorem transitionMap_levelRestrictScalarsEquiv {m n : ℕ} (hmn : m ≤ n)
    (y : B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :
    transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n y) =
      levelRestrictScalarsEquiv B 𝔭 m
        (transitionMap (𝔭.map (algebraMap A B)) B hmn y) :=
  Quotient.inductionOn' y fun _ => rfl

noncomputable def restrictScalarsEquiv :
    AdicCompletion (𝔭.map (algebraMap A B)) B ≃ₗ[A] AdicCompletion 𝔭 B where
  toFun x := ⟨fun n => levelRestrictScalarsEquiv B 𝔭 n (x.val n), fun {m n} hmn => by
    show transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n (x.val n)) =
      levelRestrictScalarsEquiv B 𝔭 m (x.val m)
    rw [← x.prop hmn]
    exact transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn (x.val n)⟩
  invFun y := ⟨fun n => (levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n), fun {m n} hmn => by
    show transitionMap (𝔭.map (algebraMap A B)) B hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)) =
      (levelRestrictScalarsEquiv B 𝔭 m).symm (y.val m)
    rw [← y.prop hmn, LinearEquiv.eq_symm_apply,
      ← transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)),
      LinearEquiv.apply_symm_apply]⟩
  map_add' x y := by
    ext n
    exact map_add (levelRestrictScalarsEquiv B 𝔭 n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (levelRestrictScalarsEquiv B 𝔭 n) a _
  left_inv x := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).symm_apply_apply _
  right_inv y := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).apply_symm_apply _

theorem restrictScalarsEquiv_of (b : B) :
    restrictScalarsEquiv B 𝔭 (of (𝔭.map (algebraMap A B)) B b) = of 𝔭 B b := by
  ext n
  rfl

theorem restrictScalarsEquiv_symm_of (b : B) :
    (restrictScalarsEquiv B 𝔭).symm (of 𝔭 B b) = of (𝔭.map (algebraMap A B)) B b := by
  ext n
  rfl

end AdicCompletion

set_option pp.universes true in
#check @AdicCompletion.restrictScalarsEquiv
#print axioms AdicCompletion.restrictScalars_map_pow_smul_top
#print axioms AdicCompletion.levelRestrictScalarsEquiv
#print axioms AdicCompletion.restrictScalarsEquiv
#print axioms AdicCompletion.restrictScalarsEquiv_of
#print axioms AdicCompletion.restrictScalarsEquiv_symm_of


