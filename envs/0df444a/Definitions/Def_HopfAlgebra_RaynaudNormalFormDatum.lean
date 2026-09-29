-- Prove2me | Definitions.Def_HopfAlgebra_RaynaudNormalFormDatum
-- name    : HopfAlgebra_RaynaudNormalFormDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/84d20c4a-ca9f-566f-829b-be7a2564d555
-- title:
--   Raynaud normal-form data and descent data for F-vector space schemes
-- statement:
--   Two groups of notions are set up. First, cotangent carriers: for a commutative ring $R$ and an $R$-Hopf algebra $B$, `Cot R B` is the cotangent module $I/I^2$ of the augmentation ideal $I=\ker(\varepsilon)$ (`augIdeal`), and for $R$ local, `CotSpecial` is $k_R\otimes_B (I/I^2)$, where the residue field $k_R$ of $R$ is made into a $B$-algebra through the counit followed by the residue map. Second, normal forms. Fix natural numbers $p,r$ with $r\neq 0$, a finite field $F$, an $R'$-Hopf algebra $B$ with an $F$-vector space structure $\mathit{fv}$ in the sense of `FVectStructure` (an additive character $a\mapsto \mathit{fv}.\mathrm{act}\,a$ of $F$ into bialgebra endomorphisms of $B$ under convolution), and a character $\chi\colon F^\times\to R'^\times$. A `NormalFormDatum` consists of elements $X_i\in B$ and $\delta_i\in R'$ indexed by $i\in\mathrm{Fin}\,r$ such that $\mathit{fv}.\mathrm{act}\,l\,(X_i)=\chi^{p^i}(l)\cdot X_i$ for all $l\in F^\times$, $X_i^{\,p}=\delta_i\cdot X_{i+1}$ with the index taken cyclically, $\delta_i\mid p$ in $R'$, $\varepsilon(X_i)=0$, and $R'[X_0,\dots,X_{r-1}]=B$; it is thus a predicate on a chosen presentation of $B$, not an invariant of $B$. When $R'$ is a discrete valuation domain, `digit i` is the additive valuation of $\delta_i$, `ramification R' p` is that of $p$, and the datum is `IsEtale` if all digits vanish, `IsMultiplicative` if all equal $v(p)$, `IsLocalLocal` if some digit is positive and some is $<v(p)$; `tameExponent` is $\sum_i \mathrm{digit}(i)\,p^i$. Finally, for $R\to R'$ and a group $\Gamma$ acting on $R'$ by ring automorphisms, a `DescentDatum` is a homomorphism $g\colon\Gamma\to\mathrm{Aut}_{\mathrm{ring}}(B)$ with $g_\sigma(c\cdot b)=\sigma(c)\cdot g_\sigma(b)$, with $\Gamma$ fixing the image of $R$, with $\varepsilon(g_\sigma b)=\sigma(\varepsilon b)$, and commuting with the whole $F$-action. `gTensor` is the additive endomorphism $b_1\otimes b_2\mapsto g_\sigma b_1\otimes g_\sigma b_2$ of $B\otimes_{R'}B$, well defined by semilinearity, and `gTensor_tmul` records its values on pure tensors; `IsComulCompatible` is the separate predicate $\Delta(g_\sigma b)=(g_\sigma\otimes g_\sigma)\Delta(b)$, kept as a hypothesis rather than as a field. A `CotAction` over a descent datum is a homomorphism $\Gamma\to\mathrm{AddAut}(I/I^2)$ together with the requirement that it send the class of $x$ to the class of $g_\sigma x$; the structure therefore carries the assertion that the action is the one induced by $g$.
--
--   **Relation to Mathlib.** Mathlib provides the ambient notions used here (`HopfAlgebra`, `Ideal.Cotangent`, `IsDiscreteValuationRing.addVal`, `AddAut`, semiring actions); the augmentation ideal `augIdeal` and the $F$-vector space structure `FVectStructure` are the project's own, as are the normal-form datum, its digits and types, and the semilinear descent and cotangent-action data.
--
--   **Where it is used.** These data encode Raynaud's classification of $\mathbb{F}$-vector space schemes over a discrete valuation ring, in the normal form $X_i^p=\delta_i X_{i+1}$ with digits bounded by the absolute ramification, together with the Galois descent along a ramified base extension. They serve the local analysis at $p$ of the finite flat group schemes attached to the Galois representations occurring in the modularity and level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_RaynaudNormalFormDatum.lean

import Mathlib
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HopfTower
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

section Cotangent

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [HopfAlgebra R B]

abbrev Cot : Type _ := (augIdeal R B).Cotangent

def CotSpecial [IsLocalRing R] : Type _ :=
  letI : Algebra B (IsLocalRing.ResidueField R) :=
    ((IsLocalRing.residue R).comp (Bialgebra.counitAlgHom R B).toRingHom).toAlgebra
  (IsLocalRing.ResidueField R) ⊗[B] (augIdeal R B).Cotangent

end Cotangent

namespace FVect

variable (R' : Type*) [CommRing R'] (p r : ℕ) [NeZero r] (F : Type*) [Field F] [Fintype F]
  (B : Type*) [CommRing B] [HopfAlgebra R' B] (fv : FVectStructure F R' B) (χ : Fˣ →* R'ˣ)

structure NormalFormDatum where
  X : Fin r → B
  δ : Fin r → R'
  act_X : ∀ (i : Fin r) (l : Fˣ), fv.act l (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i
  pow_X : ∀ i : Fin r, X i ^ p = δ i • X (i + 1)
  δ_dvd : ∀ i : Fin r, δ i ∣ (p : R')
  counit_X : ∀ i : Fin r, Coalgebra.counit (R := R') (X i) = 0
  adjoin_X : Algebra.adjoin R' (Set.range X) = ⊤

namespace NormalFormDatum

variable {R' p r F B fv χ}
variable (D : NormalFormDatum R' p r F B fv χ)

def digit [IsDomain R'] [IsDiscreteValuationRing R'] (i : Fin r) : ℕ :=
  (IsDiscreteValuationRing.addVal R' (D.δ i)).toNat

def _root_.HopfAlgebra.FVect.ramification (R' : Type*) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] (p : ℕ) : ℕ :=
  (IsDiscreteValuationRing.addVal R' (p : R')).toNat

def IsEtale [IsDomain R'] [IsDiscreteValuationRing R'] : Prop := ∀ i : Fin r, D.digit i = 0

def IsMultiplicative [IsDomain R'] [IsDiscreteValuationRing R'] : Prop := ∀ i : Fin r, D.digit i = ramification R' p

def IsLocalLocal [IsDomain R'] [IsDiscreteValuationRing R'] : Prop :=
  (∃ i : Fin r, 0 < D.digit i) ∧ (∃ i : Fin r, D.digit i < ramification R' p)

def tameExponent [IsDomain R'] [IsDiscreteValuationRing R'] : ℕ := ∑ i : Fin r, D.digit i * p ^ (i : ℕ)

end NormalFormDatum

variable (R : Type*) [CommRing R] [Algebra R R'] (Γ : Type*) [Group Γ] [MulSemiringAction Γ R']

structure DescentDatum where
  g : Γ →* (B ≃+* B)
  semilinear : ∀ (σ : Γ) (c : R') (b : B), g σ (c • b) = (σ • c) • g σ b
  fixes_base : ∀ (σ : Γ) (c : R), σ • (algebraMap R R' c) = algebraMap R R' c
  counit_g : ∀ (σ : Γ) (b : B), Coalgebra.counit (R := R') (g σ b) = σ • Coalgebra.counit (R := R') b
  act_g : ∀ (σ : Γ) (l : F) (b : B), fv.act l (g σ b) = g σ (fv.act l b)

namespace DescentDatum

variable {R' p r F B fv χ R Γ}

def gTensor (Dd : DescentDatum R' F B fv R Γ) (σ : Γ) : B ⊗[R'] B →+ B ⊗[R'] B :=
  TensorProduct.liftAddHom
    { toFun := fun b₁ =>
        { toFun := fun b₂ => Dd.g σ b₁ ⊗ₜ[R'] Dd.g σ b₂
          map_zero' := by simp only [map_zero, TensorProduct.tmul_zero]
          map_add' := fun x y => by simp only [map_add, TensorProduct.tmul_add] }
      map_zero' := by
        ext b₂
        simp only [map_zero, TensorProduct.zero_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
      map_add' := fun x y => by
        ext b₂
        simp only [map_add, TensorProduct.add_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply] }
    (fun c b₁ b₂ => by
      show Dd.g σ (c • b₁) ⊗ₜ[R'] Dd.g σ b₂ = Dd.g σ b₁ ⊗ₜ[R'] Dd.g σ (c • b₂)
      rw [Dd.semilinear, Dd.semilinear, TensorProduct.smul_tmul])

theorem gTensor_tmul (Dd : DescentDatum R' F B fv R Γ) (σ : Γ) (b₁ b₂ : B) :
    Dd.gTensor σ (b₁ ⊗ₜ[R'] b₂) = Dd.g σ b₁ ⊗ₜ[R'] Dd.g σ b₂ := rfl

def IsComulCompatible (Dd : DescentDatum R' F B fv R Γ) : Prop :=
  ∀ (σ : Γ) (b : B), Coalgebra.comul (R := R') (Dd.g σ b) = Dd.gTensor σ (Coalgebra.comul (R := R') b)

structure CotAction (Dd : DescentDatum R' F B fv R Γ) where

  cotAct : Γ →* AddAut (Cot R' B)
  cotAct_spec : ∀ (σ : Γ) (x : augIdeal R' B),
    cotAct σ ((augIdeal R' B).toCotangent x) =
      (augIdeal R' B).toCotangent ⟨Dd.g σ x, by
        have hx := x.2
        rw [HopfAlgebra.mem_augIdeal] at hx ⊢
        rw [Dd.counit_g, hx, smul_zero]⟩

end DescentDatum

end FVect

end HopfAlgebra

end


