-- Prove2me | Definitions.Def_ModularCurve_WeierstrassH1Pow
-- name    : ModularCurve_WeierstrassH1Pow
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/936c8a14-da90-58bc-a756-6f3b1cc38097
-- title:
--   Level component with Γ₁(ℓ)-generator link, and its rigid data
-- statement:
--   Over a commutative ring $T$ and a Weierstrass curve $W/T$, [`ModularCurve.inLineMulPoly W ℓ n x₀`](../def/ModularCurve_WeierstrassH1Pow.html#L18) is the polynomial $\prod_{a=1}^{(\ell-1)/2}\bigl(\Phi_n\cdot\Psi_a^2(x_0)-\Phi_a(x_0)\cdot\Psi_n^2\bigr)\in T[X]$, formed from Mathlib's division polynomials `W.Φ` and `W.ΨSq` (whose quotient gives the abscissa of a multiple); the factor indexed by $a$ vanishes at an abscissa $x$ exactly when $x([n]G)=x([a]P_0)$ in the division-free sense, for $G$ with abscissa $x$ and $P_0$ with abscissa $x_0$. The lemma `inLineMulPoly_map` records compatibility with a ring homomorphism $f$: the polynomial formed for $W$ mapped by $f$ at $f(x_0)$ is the coefficientwise image of the one formed for $W$ at $x_0$.
--
--   [`ModularCurve.IsGamma1Link W ℓ M' h D`](../def/ModularCurve_WeierstrassH1Pow.html#L26) asserts, for each proof that $\ell$ is a prime factor of $M'$, that the $\ell$-th member $h(\ell)$ of the family $h$ indexed by the prime factors of $M'$ divides `inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP`, where `D.xP` is the abscissa recorded by the level-$p$ datum $D$; the condition is vacuous when $\ell\nmid M'$. `IsGamma1Link.map` transports it along a ring homomorphism.
--
--   [`ModularCurve.LevelComponent.restrict L P hmap hact`](../def/ModularCurve_WeierstrassH1Pow.html#L40) produces, from a level component $L$ and a predicate $P$ on pairs (curve, level datum) that is preserved by base change along $A$-algebra maps and by Weierstrass variable changes on pairs already satisfying `L.IsLevel`, the level component with the same carrier, base-change and variable-change operations and with `IsLevel W x` replaced by the conjunction of `L.IsLevel W x` and `P W x`.
--
--   Finally, `rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯` is the rigid Weierstrass datum obtained from the product of `gamma0PowComponent A M' hM` (families of monic kernel polynomials at the prime powers dividing $M'$), `gamma1Component A ℓ hℓ` (a point $P$ with $(W.\mathrm{preΨ}\,\ell)(x_P)=0$ and $Q=P$) and `levelComponent A 𝒢 q 𝒯` (Drinfeld $q$-bases for the group laws $𝒢$ with transport $𝒯$), restricted by the link condition relating the $\Gamma_0$-tuple's $\ell$-component to $x_P$; the hypothesis `hL` supplies the required variable-change stability, for $h\mapsto$ `kernelVariableChangeDeg C d h` against the substitution $x\mapsto u^{-2}(x-r)$ on abscissae. The datum is then passed through `toRigid`, whose raw points are quadruples (Weierstrass curve, invertibility of $\Delta$, level datum, level condition) with variable changes as the identification relation.
--
--   **Relation to Mathlib.** The division polynomials `Φ`, `ΨSq`, `preΨ` and variable changes of Weierstrass curves are Mathlib's; the notions `LevelComponent`, `RigidWeierstrassData`, `IsGamma1Point`, `IsGamma0PowAt`, `IsGamma1Link` and the Drinfeld-basis components are the project's own, Mathlib having no moduli-of-elliptic-curves-with-level-structure API.
--
--   **Where it is used.** This assembles the rigid moduli datum for structures of type $\Gamma_0(M')\cap\Gamma_1(\ell)$ together with a Drinfeld $q$-basis, the level structure underlying the modular curves used on the modularity side of the argument; the link condition is what forces the $\Gamma_1(\ell)$-point to generate the $\ell$-torsion of the cyclic subgroup recorded by the $\Gamma_0$-part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeierstrassH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace ModularCurve

section Link

variable {T : Type u} [CommRing T]

def inLineMulPoly (W : WeierstrassCurve T) (ℓ n : ℕ) (x₀ : T) : T[X] :=
  ∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), (W.Φ n * C ((W.ΨSq a).eval x₀) - C ((W.Φ a).eval x₀) * W.ΨSq n)

theorem inLineMulPoly_map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (ℓ n : ℕ) (x₀ : T) :
    inLineMulPoly (W.map f) ℓ n (f x₀) = (inLineMulPoly W ℓ n x₀).map f := by
  simp only [inLineMulPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq, Polynomial.eval_map, Polynomial.eval₂_at_apply]

def IsGamma1Link (W : WeierstrassCurve T) (ℓ M' : ℕ) (h : ↥M'.primeFactors → T[X]) (D : LevelPData T) : Prop :=
  ∀ hmem : ℓ ∈ M'.primeFactors, h ⟨ℓ, hmem⟩ ∣ inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP

theorem IsGamma1Link.map {T' : Type u} [CommRing T'] (f : T →+* T') {W : WeierstrassCurve T} {ℓ M' : ℕ}
    {h : ↥M'.primeFactors → T[X]} {D : LevelPData T} (hD : IsGamma1Link W ℓ M' h D) :
    IsGamma1Link (W.map f) ℓ M' (fun p => (h p).map f) (D.map f) :=
  fun hmem => by rw [LevelPData.map_xP, inLineMulPoly_map]; exact Polynomial.map_dvd f (hD hmem)

end Link

namespace LevelComponent

variable {A : Type u} [CommRing A]

def restrict (L : LevelComponent A)
    (P : ∀ {T : Type u} [CommRing T] [Algebra A T], WeierstrassCurve T → L.obj T → Prop)
    (hmap : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve T) (x : L.obj T), L.IsLevel W x → P W x → P (W.map f.toRingHom) (L.map f x))
    (hact : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
      (W : WeierstrassCurve T) (x : L.obj T), L.IsLevel W x → P W x → P (C • W) (L.act C x)) :
    LevelComponent A where
  obj := L.obj
  IsLevel W x := L.IsLevel W x ∧ P W x
  map := L.map
  act := L.act
  map_id := L.map_id
  map_comp := L.map_comp
  act_one := L.act_one
  act_mul := L.act_mul
  map_act := L.map_act
  isLevel_map f W x h := ⟨L.isLevel_map f W x h.1, hmap f W x h.1 h.2⟩
  isLevel_act C W x h := ⟨L.isLevel_act C W x h.1, hact C W x h.1 h.2⟩

end LevelComponent

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

def rigidDataH1Pow (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  (((ModularCurve.gamma0PowComponent A M' hM).prod
      ((ModularCurve.gamma1Component A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).restrict
    (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
    (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
    (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid

end WeierstrassCurve.DrinfeldGlobal

end


