-- Prove2me | Definitions.Def_CohCarrier_CharInvolution
-- name    : CohCarrier_CharInvolution
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/8710a0be-2262-5106-847b-862d88a349b2
-- title:
--   The character involution on ΓH​(M)-cohomology
-- statement:
--   Fix $M \in \mathbb{N}$ and a subgroup $H \le (\mathbb{Z}/M)^\times$. Here $\Gamma_H(M)$ is the subgroup [`CohCarrier.GammaH M H`](../def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $A \in \Gamma_0(M)$ whose lower-right entry, viewed through the homomorphism [`CohCarrier.gamma0Units`](../def/CohCarrier_Level.html#L121) sending $A$ to the unit $d \bmod M$ (with inverse $a \bmod M$), lies in $H$; and [`CohCarrier.H1 M H A`](../def/CohCarrier_Level.html#L162) is the group $\operatorname{Hom}(\Gamma_H(M), A) = (\mathrm{Additive}\,\Gamma_H(M) \to_+ A)$ of additive characters, with its module structure over any semiring $R$ acting on $A$.
--
--   The first result states that the involutive automorphism [`ModularCurve.Period.jConjSL`](../def/ModularCurve_PeriodHomPair.html#L47) of $\mathrm{SL}_2(\mathbb{Z})$, namely conjugation by $\operatorname{diag}(1,-1)$, which sends $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ to $\begin{pmatrix} a & -b \\ -c & d\end{pmatrix}$, maps $\Gamma_H(M)$ into itself: it preserves $\Gamma_0(M)$ (the lower-left entry only changes sign) and leaves the associated unit $d \bmod M$ unchanged. Restricting it yields the monoid homomorphism [`CohCarrier.jConjGammaH`](../def/CohCarrier_CharInvolution.html#L23) of $\Gamma_H(M)$ to itself, which is shown to be an involution, together with the compatibility of its underlying matrices.
--
--   For an additive commutative group $A$ and a semiring $R$ making $A$ an $R$-module, [`CohCarrier.charInvolution M H A R`](../def/CohCarrier_CharInvolution.html#L43) is the $R$-linear endomorphism of $\operatorname{Hom}(\Gamma_H(M), A)$ given by precomposition with `jConjGammaH`, so $\varphi \mapsto (\gamma \mapsto \varphi(J\gamma J^{-1}))$. The remaining statements record the pointwise formula, that applying it twice returns $\varphi$, and the composite form of the same fact, that `charInvolution` composed with itself is the identity linear map. No parabolicity or cuspidality condition enters: the involution is defined on all characters of $\Gamma_H(M)$.
--
--   **Relation to Mathlib.** Mathlib's congruence subgroup file supplies $\Gamma(N)$, $\Gamma_0(N)$ and $\Gamma_1(N)$; the intermediate groups $\Gamma_H(M)$, the group $\operatorname{Hom}(\Gamma_H(M),A)$ used as cohomology carrier, and this involution on it are the project's own. The construction is the $\Gamma_H(M)$-analogue of [`ModularCurve.Period.charInvolution`](../def/ModularCurve_PeriodHomPair.html#L95), which is defined for characters of $\Gamma_0(N)$.
--
--   **Where it is used.** The module [`CohCarrier.H1`](../def/CohCarrier_Level.html#L162) serves as the project's carrier for weight-two group cohomology of $\Gamma_H(M)$, on which Hecke operators, diamond operators and degeneracy maps between levels are defined; the character involution is the extra operator whose $\pm 1$-eigenspaces correspond, via Eichler–Shimura, to the two copies of the space of weight-two cusp forms occurring in [`ModularCurve.periodHomPair`](../def/ModularCurve_PeriodHomPair.html#L135).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CohCarrier_CharInvolution.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CohCarrier

section Level

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem jConjSL_mem_GammaH {A : SL(2, ℤ)} (hA : A ∈ GammaH M H) :
    ModularCurve.Period.jConjSL A ∈ GammaH M H := by
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  rw [mem_GammaH_iff]
  refine ⟨ModularCurve.Period.jConjSL_mem_Gamma0 hA0, ?_⟩
  exact hAH

def jConjGammaH : ↥(GammaH M H) →* ↥(GammaH M H) where
  toFun γ := ⟨ModularCurve.Period.jConjSL (γ : SL(2, ℤ)), jConjSL_mem_GammaH M H γ.2⟩
  map_one' := Subtype.ext (by
    show ModularCurve.Period.jConjSL ((1 : ↥(GammaH M H)) : SL(2, ℤ)) = 1
    rw [OneMemClass.coe_one, map_one])
  map_mul' γ δ := Subtype.ext (by
    show ModularCurve.Period.jConjSL ((γ * δ : ↥(GammaH M H)) : SL(2, ℤ)) =
      ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) * ModularCurve.Period.jConjSL (δ : SL(2, ℤ))
    rw [Subgroup.coe_mul, map_mul])

@[simp] theorem coe_jConjGammaH (γ : ↥(GammaH M H)) :
    ((jConjGammaH M H γ : ↥(GammaH M H)) : SL(2, ℤ)) = ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) :=
  rfl

@[simp] theorem jConjGammaH_jConjGammaH (γ : ↥(GammaH M H)) :
    jConjGammaH M H (jConjGammaH M H γ) = γ :=
  Subtype.ext (ModularCurve.Period.jConjSL_jConjSL _)

variable (A : Type*) [AddCommGroup A]

def charInvolution (R : Type*) [Semiring R] [Module R A] : H1 M H A →ₗ[R] H1 M H A where
  toFun φ := φ.comp (MonoidHom.toAdditive (jConjGammaH M H))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

@[simp] theorem charInvolution_apply (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A)
    (γ : Additive ↥(GammaH M H)) :
    charInvolution M H A R φ γ = φ (Additive.ofMul (jConjGammaH M H (Additive.toMul γ))) := rfl

theorem charInvolution_charInvolution (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A) :
    charInvolution M H A R (charInvolution M H A R φ) = φ := by
  ext γ
  show φ (Additive.ofMul (jConjGammaH M H (Additive.toMul
    (Additive.ofMul (jConjGammaH M H (Additive.toMul γ)))))) = φ γ
  rw [toMul_ofMul, jConjGammaH_jConjGammaH, ofMul_toMul]

theorem charInvolution_comp_charInvolution (R : Type*) [Semiring R] [Module R A] :
    charInvolution M H A R ∘ₗ charInvolution M H A R = LinearMap.id :=
  LinearMap.ext (charInvolution_charInvolution M H A R)

end Level

end CohCarrier


