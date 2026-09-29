-- Prove2me | Definitions.Def_M4aHerbrand_IdeleClassVocab
-- name    : M4aHerbrand_IdeleClassVocab
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/4c79a1d5-66db-57f2-a07a-ba9ed873c3b0
-- title:
--   Idele class group, Galois descent data, norm and σ−1
-- statement:
--   Throughout, $R$ is a Dedekind domain with field of fractions $F$, and $E$ is a field with $F$ an $E$-algebra; the ambient ring is Mathlib's full adele ring $\mathbb{A}_{R,F}$ of $F$ (the product of the infinite-place factor with the finite adeles, not the finite part alone). `principalIdeles` is the subgroup of $(\mathbb{A}_{R,F})^\times$ obtained as the range of the map on unit groups induced by the structure map $F \to \mathbb{A}_{R,F}$, i.e. the diagonal image of $F^\times$; `IdeleClassGroup` is the quotient group $(\mathbb{A}_{R,F})^\times / \mathrm{principalIdeles}$.
--
--   `IdeleGaloisDescent` is a structure packaging a descent datum: a field `act`, a monoid homomorphism from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of $\mathbb{A}_{R,F}$; a field `compat` asserting that for every $g$ and every $x \in F$ the automorphism `act g` carries the diagonal image of $x$ to the diagonal image of $g x$; and a field `continuous_act` asserting that each `act g` is continuous. Given such a datum $D$, `unitsAct` is the induced homomorphism into the multiplicative automorphisms of $(\mathbb{A}_{R,F})^\times$, and `map_principalIdeles` is the statement that the image of `principalIdeles` under `unitsAct g` is again `principalIdeles`, which is what lets `classAct` define, for each $g$, an endomorphism of the idele class group (obtained from the isomorphism of quotients induced by `unitsAct g`).
--
--   Two derived endomorphisms of the idele class group are defined: `ideleClassNorm`, under the hypothesis that $F \simeq_{\mathrm{alg}[E]} F$ is finite, sends $c$ to $\prod_{\tau} \mathrm{classAct}\,\tau\,(c)$; and `ideleClassDerive`, for a fixed $\sigma$, sends $c$ to $(\mathrm{classAct}\,\sigma\,(c))\, c^{-1}$. Finally `identityDescent` exhibits a descent datum when the group $F \simeq_{\mathrm{alg}[E]} F$ is a subsingleton, namely the trivial action.
--
--   **Relation to Mathlib.** Built on Mathlib's `AdeleRing R F`. The idele class group, the Galois descent datum on the adele ring, and the associated norm and $\sigma - 1$ endomorphisms are the project's own definitions.
--
--   **Where it is used.** The module supplies the idele-theoretic vocabulary in which statements of global class field theory type are phrased within the development, and is imported broadly across its statement and proof modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_IdeleClassVocab.lean

import Mathlib.NumberTheory.NumberField.AdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

namespace M4aHerbrand

noncomputable section

section Carrier

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

def principalIdeles : Subgroup (AdeleRing R F)ˣ :=
  (Units.map (algebraMap F (AdeleRing R F) : F →* AdeleRing R F)).range

abbrev IdeleClassGroup := (AdeleRing R F)ˣ ⧸ principalIdeles R F

end Carrier

section Descent

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

structure IdeleGaloisDescent where

  act : (F ≃ₐ[E] F) →* RingAut (AdeleRing R F)

  compat : ∀ (g : F ≃ₐ[E] F) (x : F),
    act g (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) (g x)

  continuous_act : ∀ g : F ≃ₐ[E] F, Continuous (act g)

namespace IdeleGaloisDescent

variable {R E F}

def unitsAct (D : IdeleGaloisDescent R E F) : (F ≃ₐ[E] F) →* MulAut (AdeleRing R F)ˣ where
  toFun g := Units.mapEquiv (D.act g).toMulEquiv
  map_one' := by refine MulEquiv.ext fun u => Units.ext ?_; simp only [map_one]; rfl
  map_mul' g₁ g₂ := by refine MulEquiv.ext fun u => Units.ext ?_; simp only [map_mul]; rfl

theorem map_principalIdeles (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) :
    (principalIdeles R F).map (D.unitsAct g).toMonoidHom = principalIdeles R F := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨Units.map (g : F →* F) u, Units.ext (D.compat g u).symm⟩
  · intro x hx
    have hmem : D.unitsAct g⁻¹ x ∈ principalIdeles R F := by
      rcases hx with ⟨u, rfl⟩
      exact ⟨Units.map ((g⁻¹ : F ≃ₐ[E] F) : F →* F) u, Units.ext (D.compat g⁻¹ u).symm⟩
    refine ⟨D.unitsAct g⁻¹ x, hmem, ?_⟩
    show D.unitsAct g (D.unitsAct g⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

def classAct (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) :
    IdeleClassGroup R F →* IdeleClassGroup R F :=
  (QuotientGroup.congr (principalIdeles R F) (principalIdeles R F)
    (D.unitsAct g) (D.map_principalIdeles g)).toMonoidHom

end IdeleGaloisDescent

end Descent

section NormDerive

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

def ideleClassNorm [Finite (F ≃ₐ[E] F)] (D : IdeleGaloisDescent R E F) :
    IdeleClassGroup R F →* IdeleClassGroup R F where
  toFun c :=
    letI := Fintype.ofFinite (F ≃ₐ[E] F)
    ∏ τ : F ≃ₐ[E] F, D.classAct τ c
  map_one' := by simp
  map_mul' x y := by
    letI := Fintype.ofFinite (F ≃ₐ[E] F)
    simp only [map_mul]; exact Finset.prod_mul_distrib

set_option maxSynthPendingDepth 3 in

def ideleClassDerive (D : IdeleGaloisDescent R E F) (σ : F ≃ₐ[E] F) :
    IdeleClassGroup R F →* IdeleClassGroup R F where
  toFun c := D.classAct σ c * c⁻¹
  map_one' := by simp
  map_mul' x y := by
    show D.classAct σ (x * y) * (x * y)⁻¹ = D.classAct σ x * x⁻¹ * (D.classAct σ y * y⁻¹)
    rw [map_mul, mul_inv_rev, mul_comm y⁻¹ x⁻¹]
    exact mul_mul_mul_comm _ _ _ _

end NormDerive

section Inhabitant

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

def identityDescent [Subsingleton (F ≃ₐ[E] F)] : IdeleGaloisDescent R E F where
  act := 1
  compat g x := by
    have hg : g = 1 := Subsingleton.elim g 1
    subst hg; rfl
  continuous_act g := by
    have hg : g = 1 := Subsingleton.elim g 1
    subst hg; simp only [map_one]; exact continuous_id

end Inhabitant

end

end M4aHerbrand


