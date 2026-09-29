-- Prove2me | Definitions.Def_CuspForm_CornerPairingFamily
-- name    : CuspForm_CornerPairingFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/e9386973-8507-5a27-891a-81478ca6be4f
-- title:
--   Chosen pairings on parabolic classes at all levels
-- statement:
--   Fix a commutative ring $\mathcal O$. For a level $M$, a subgroup $H\le(\mathbb Z/M)^\times$ and a datum $h_1:\mathrm{LevelLE}\,M\,M\,\top\,H\,1$, write $W(M,H)$ for the submodule of $H^1(M,H,\mathcal O)=\mathrm{Hom}(\mathrm{Additive}\,\Gamma_H(M,H),\mathcal O)$ obtained as the image under `iDegL M M ⊤ H 1` (restriction along the inclusion $\Gamma_H(M,H)\to\Gamma_H(M,\top)=\Gamma_0(M)$) of [`ModularCurve.Period.parabolicHoms`](../def/ModularCurve_PeriodMap.html#L62), i.e. of those additive characters of $\Gamma_0(M)$ that vanish on every element whose matrix trace has square $4$. Two predicates are defined on families $B=(B_{M,H,h_1})$ of $\mathcal O$-bilinear forms $W(M,H)\times W(M,H)\to\mathcal O$. `LevelBlock` asks, for every $M\ne 0$ and every $H$ whose index $[(\mathbb Z/M)^\times:H]$ is a unit in $\mathcal O$: that $B_{M,H,h_1}$ be bijective as a map $W(M,H)\to\mathrm{Hom}_{\mathcal O}(W(M,H),\mathcal O)$; that for each $\ell\ne 0$ which is prime or divides $M$ and for elements $x,y,Tx,Ty$ of $W(M,H)$ whose underlying characters satisfy $Tx=\mathrm{heckeT}_\ell x$ and $Ty=\mathrm{heckeT}_\ell y$ one has $B(Tx,y)=B(x,Ty)$; and that `diamondL` at every $d\in(\mathbb Z/M)^\times$ fix each element of $W(M,H)$. `DegeneracyBlock` asks, for $h:\mathrm{LevelLE}\,M\,M'\,H\,H'\,d$ and $h':\mathrm{LevelLE}\,M\,M'\,H\,H'\,d'$ with $dd'=M'/M$, with $H'$ the full preimage of $H$ under `ZMod.unitsMap` and both indices units, that $B_{M,H,h_1}(jy,x)=B_{M',H',h_1'}(y,ix)$ whenever $ix$ and $jy$ have underlying characters $\mathrm{iDegL}\,x$ and $\mathrm{jDegL}\,y$. [`CuspForm.Bfam 𝒪`](../def/CuspForm_CornerPairingFamily.html#L57) is then a family chosen by `Classical.epsilon` to satisfy both blocks when such a family exists.
--
--   In the corner section, for corner data `cd : H1CornerData M H 𝒪 𝕋` (an idempotent splitting of $\mathbb T$, an index, and a level pairing on the corresponding corner submodule of $H^1$) and a hypothesis $hW$ placing that corner submodule inside $W(M,H)$, `cornerInclusion` is the resulting $\mathcal O$-linear inclusion, `cornerRestrict` is `Bfam 𝒪 M H h₁` restricted along it in both arguments, and `pairing_eq_cornerRestrict_iff` states that the corner datum's own pairing equals this restriction exactly when the two agree on all pairs of elements. The `Bfam₀` section repeats the construction for $H=\top$ on `parabolicHoms` itself: `Bfam₀.Block` requires bijectivity, self-adjointness of `heckeT` for every $\ell\ne 0$ and of `diamondL` for every $d$ (rather than triviality of the diamonds), together with the same degeneracy compatibility at $H=H'=\top$, and `Bfam₀ 𝒪` is a family chosen to satisfy it.
--
--   **Relation to Mathlib.** Mathlib has no pairing on parabolic cohomology of congruence subgroups; the carriers ([`CohCarrier.H1`](../def/CohCarrier_Level.html#L162), `parabolicHoms`, the Hecke, diamond and degeneracy operators) and both pairing families are the project's own, built on Mathlib's congruence subgroups, transfer and `LinearMap.compl₁₂`, with the choice made by Mathlib's `Classical.epsilon`.
--
--   **Where it is used.** These named pairings let statements about Hecke modules at the various levels of the tower used in modularity lifting ($\Gamma_0(N)\cap\Gamma_1(r)$, its $p$-level and its auxiliary Taylor–Wiles levels) refer to one and the same pairing at each level, instead of carrying a family together with its perfectness, Hecke-adjointness and degeneracy-adjointness hypotheses. The corner constructions transport such a pairing to the summand cut out by an idempotent of a Hecke algebra, which is the shape required by the Ihara-style rung data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_CornerPairingFamily.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_LevelPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

set_option linter.unusedVariables false

noncomputable section

namespace CuspForm

open CohCarrier IharaLemma IharaTower

namespace Bfam

variable (𝒪 : Type) [CommRing 𝒪]

def LevelBlock
    (B : (M : ℕ) → (H : Subgroup (ZMod M)ˣ) → (h₁ : LevelLE M M ⊤ H 1) →
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪]
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪] 𝒪) :
    Prop :=
  ∀ (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1),
    IsUnit ((H.index : ℕ) : 𝒪) →
    Function.Bijective (B M H h₁) ∧
    (∀ (ℓ : ℕ) [NeZero ℓ], (ℓ.Prime ∨ ℓ ∣ M) →
      ∀ (x y Tx Ty : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
          (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
        (Tx : H1 M H 𝒪) = heckeT M H ℓ 𝒪 x → (Ty : H1 M H 𝒪) = heckeT M H ℓ 𝒪 y →
        B M H h₁ Tx y = B M H h₁ x Ty) ∧
    (∀ (d : (ZMod M)ˣ) (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
          (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
        diamondL M H 𝒪 d (x : H1 M H 𝒪) = x)

def DegeneracyBlock
    (B : (M : ℕ) → (H : Subgroup (ZMod M)ˣ) → (h₁ : LevelLE M M ⊤ H 1) →
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪]
        ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪] 𝒪) :
    Prop :=
  ∀ (M M' : ℕ) [NeZero M] [NeZero M'] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ)
      (h₁ : LevelLE M M ⊤ H 1) (h₁' : LevelLE M' M' ⊤ H' 1)
      (d d' : ℕ) [NeZero d] [NeZero d'] (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
      (hdd' : d * d' = M' / M)
      (hH' : ∀ u : (ZMod M')ˣ, u ∈ H' ↔ ZMod.unitsMap h.dvd u ∈ H),
      IsUnit ((H.index : ℕ) : 𝒪) → IsUnit ((H'.index : ℕ) : 𝒪) →
      ∀ (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)))
        (y : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
        (ix : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
        (jy : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
      (ix : H1 M' H' 𝒪) = iDegL M M' H H' d 𝒪 𝒪 h x →
      (jy : H1 M H 𝒪) = jDegL M M' H H' d' 𝒪 𝒪 h' y →
      B M H h₁ jy x = B M' H' h₁' y ix

end Bfam

def Bfam (𝒪 : Type) [CommRing 𝒪] :
    (M : ℕ) → (H : Subgroup (ZMod M)ˣ) → (h₁ : LevelLE M M ⊤ H 1) →
      ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪]
      ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) →ₗ[𝒪] 𝒪 :=
  Classical.epsilon fun B => Bfam.LevelBlock 𝒪 B ∧ Bfam.DegeneracyBlock 𝒪 B

namespace Bfam

section Corner

variable (𝒪 : Type) [CommRing 𝒪] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1)
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M H 𝒪)]

def cornerInclusion (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) :
    cd.cornerModule →ₗ[𝒪]
      ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) where
  toFun x := ⟨x, hW _ x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cornerInclusion_apply (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))
    (x : cd.cornerModule) :
    cornerInclusion 𝒪 M H h₁ cd hW x = ⟨x, hW _ x.2⟩ := rfl

def cornerRestrict (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) :
    cd.cornerModule →ₗ[𝒪] cd.cornerModule →ₗ[𝒪] 𝒪 :=
  (Bfam 𝒪 M H h₁).compl₁₂ (cornerInclusion 𝒪 M H h₁ cd hW) (cornerInclusion 𝒪 M H h₁ cd hW)

@[simp] theorem cornerRestrict_apply (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))
    (x y : cd.cornerModule) :
    cornerRestrict 𝒪 M H h₁ cd hW x y = Bfam 𝒪 M H h₁ ⟨x, hW _ x.2⟩ ⟨y, hW _ y.2⟩ := rfl

theorem pairing_eq_cornerRestrict_iff (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) :
    cd.pairing.B = cornerRestrict 𝒪 M H h₁ cd hW ↔
      ∀ x y : cd.cornerModule, cd.pairing.B x y = Bfam 𝒪 M H h₁ ⟨x, hW _ x.2⟩ ⟨y, hW _ y.2⟩ := by
  constructor
  · intro h x y
    rw [h]
    rfl
  · intro h
    exact LinearMap.ext₂ fun x y => h x y

end Corner

end Bfam

namespace Bfam₀

variable (𝒪 : Type) [CommRing 𝒪]

def Block
    (B : (M : ℕ) → ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪]
        ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪] 𝒪) : Prop :=
  (∀ (M : ℕ) [NeZero M],
    Function.Bijective (B M) ∧
    (∀ (ℓ : ℕ) [NeZero ℓ] (x y Tx Ty : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
        (Tx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 x →
        (Ty : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 y → B M Tx y = B M x Ty) ∧
    (∀ (d : (ZMod M)ˣ) (x y Dx Dy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
        (Dx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d x →
        (Dy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d y → B M Dx y = B M x Dy)) ∧
  (∀ (M M' : ℕ) [NeZero M'] (d d' : ℕ) [NeZero d] [NeZero d']
      (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (h' : CohCarrier.LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
      (x : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪))
      (y : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
      (ix : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
      (jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
      (ix : CohCarrier.H1 M' ⊤ 𝒪) = CohCarrier.iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h x →
      (jy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h' y →
      B M jy x = B M' y ix)

end Bfam₀

def Bfam₀ (𝒪 : Type) [CommRing 𝒪] :
    (M : ℕ) → ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪]
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪] 𝒪 :=
  Classical.epsilon (Bfam₀.Block 𝒪)

end CuspForm

end


