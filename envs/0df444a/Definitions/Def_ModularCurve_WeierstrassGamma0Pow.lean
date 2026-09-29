-- Prove2me | Definitions.Def_ModularCurve_WeierstrassGamma0Pow
-- name    : ModularCurve_WeierstrassGamma0Pow
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/f967e359-5adc-56f7-8b74-84cfd4456d18
-- title:
--   Prime-power Γ₀ level data via generator kernel polynomials
-- statement:
--   For a Weierstrass curve $W$ over a commutative ring $T$, natural numbers $p,k$ and a polynomial $h \in T[X]$, the structure [`WeierstrassCurve.IsCyclicGenKernel W p k h`](../def/ModularCurve_WeierstrassGamma0Pow.html#L23) bundles four conditions: $\deg h \le \varphi(p^k)/2$ and the coefficient of $X^{\varphi(p^k)/2}$ equals $1$ (so $h$ is monic of that degree, recorded as `IsCyclicGenKernel.monic`); the divisibility $h \cdot \mathrm{pre}\Psi_{p^{k-1}} \mid \mathrm{pre}\Psi_{p^k}$ of Mathlib's univariate division polynomials; and, for every $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$, the divisibility $h \mid W.\mathrm{smulNumerator}\,a\,(\varphi(p^k)/2)\,h$, where $\mathrm{smulNumerator}\,a\,d\,h = \sum_{i \le d} h_i \Phi_a^{\,i}\,(\Psi^2_a)^{\,d-i}$ is the degree-$d$ homogenisation of $h$ evaluated at the $x$-coordinate $\Phi_a/\Psi_a^2$ of $[a]P$. Thus $h$ is required to cut out, in the $x$-line, a set of $\varphi(p^k)/2$ points of exact order $p^k$ stable under multiplication by units mod $p^k$. The predicate transports along a ring homomorphism: `IsCyclicGenKernel.map` gives the same property for $W.map\,f$ and $h.map\,f$.
--
--   The local datum at a prime power is [`ModularCurve.IsGamma0PowAt W p k h`](../def/ModularCurve_WeierstrassGamma0Pow.html#L55), defined as the project's `IsTwoKernel` condition when $p^k = 2$ and as `IsCyclicGenKernel W p k h` otherwise, with matching transport degree `gamma0PowDeg p k` ($=1$ when $p^k=2$, else $\varphi(p^k)/2$); two lemmas record the two branches, and `IsGamma0PowAt.map` its base change. From this, `gamma0PowComponent A M' hM` is a `LevelComponent` over $A$ whose objects are families $h : M'.\mathrm{primeFactors} \to T[X]$, whose level predicate asks `IsGamma0PowAt W p (M'.factorization p) (h p)` for each prime factor $p$ of $M'$, with base change by `Polynomial.map` and variable change by `kernelVariableChangeDeg C (gamma0PowDeg p (M'.factorization p))`, i.e. $h \mapsto u^{-2d} h(u^2X + r)$; the hypothesis `hM` supplies compatibility of `IsGamma0PowAt` with changes of variables, which is the component's `isLevel_act` field. Finally [`WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯`](../def/ModularCurve_WeierstrassGamma0Pow.html#L93) is the rigid Weierstrass datum obtained from the triple product of this Γ₀-component, the level-$ℓ$ point component `levelPComponent A ℓ hℓ` and the Drinfeld level-$q$ component `levelComponent A 𝒢 q 𝒯`.
--
--   **Relation to Mathlib.** The division polynomials `preΨ`, `Φ` and `ΨSq`, and the variable-change action on Weierstrass curves, are Mathlib's; Mathlib has no notion of a Γ₀-type level structure, and the kernel-polynomial predicates and level components here are the project's own.
--
--   **Where it is used.** These level components provide the moduli data for modular curves with Γ₀(M')-type level together with a point structure of level $ℓ$ and full Drinfeld level $q$, in the form of a rigid Weierstrass datum; the prime-power version refines the squarefree one by allowing each prime factor of $M'$ to occur with its exponent $v_p(M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeierstrassGamma0Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

structure IsCyclicGenKernel (p k : ℕ) (h : T[X]) : Prop where

  natDegree_le : h.natDegree ≤ Nat.totient (p ^ k) / 2

  coeff_eq_one : h.coeff (Nat.totient (p ^ k) / 2) = 1

  mul_preΨ_dvd : h * W.preΨ (p ^ (k - 1)) ∣ W.preΨ (p ^ k)

  dvd_smulNumerator : ∀ a : ℕ, 2 ≤ a → a ≤ (p ^ k - 1) / 2 → ¬ p ∣ a →
    h ∣ W.smulNumerator a (Nat.totient (p ^ k) / 2) h

theorem IsCyclicGenKernel.monic {p k : ℕ} {h : T[X]} (hh : W.IsCyclicGenKernel p k h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one

theorem IsCyclicGenKernel.map {T' : Type u} [CommRing T'] (f : T →+* T') {p k : ℕ} {h : T[X]}
    (hh : W.IsCyclicGenKernel p k h) : (W.map f).IsCyclicGenKernel p k (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  mul_preΨ_dvd := by
    rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, ← Polynomial.map_mul]
    exact Polynomial.map_dvd f hh.mul_preΨ_dvd
  dvd_smulNumerator := fun a ha ha' hpa => by
    rw [W.smulNumerator_map f]; exact Polynomial.map_dvd f (hh.dvd_smulNumerator a ha ha' hpa)

end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]

def gamma0PowDeg (p k : ℕ) : ℕ := if p ^ k = 2 then 1 else Nat.totient (p ^ k) / 2

def IsGamma0PowAt (W : WeierstrassCurve T) (p k : ℕ) (h : T[X]) : Prop :=
  if p ^ k = 2 then W.IsTwoKernel h else W.IsCyclicGenKernel p k h

theorem isGamma0PowAt_of_pow_eq_two (W : WeierstrassCurve T) {p k : ℕ} (hpk : p ^ k = 2) (h : T[X]) :
    IsGamma0PowAt W p k h ↔ W.IsTwoKernel h := by
  simp [IsGamma0PowAt, hpk]

theorem isGamma0PowAt_of_pow_ne_two (W : WeierstrassCurve T) {p k : ℕ} (hpk : p ^ k ≠ 2) (h : T[X]) :
    IsGamma0PowAt W p k h ↔ W.IsCyclicGenKernel p k h := by
  simp [IsGamma0PowAt, hpk]

theorem IsGamma0PowAt.map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (p k : ℕ) {h : T[X]}
    (hh : IsGamma0PowAt W p k h) : IsGamma0PowAt (W.map f) p k (h.map f) := by
  by_cases hpk : p ^ k = 2
  · exact (isGamma0PowAt_of_pow_eq_two _ hpk _).2 (((isGamma0PowAt_of_pow_eq_two _ hpk _).1 hh).map W f)
  · exact (isGamma0PowAt_of_pow_ne_two _ hpk _).2 (((isGamma0PowAt_of_pow_ne_two _ hpk _).1 hh).map W f)

def gamma0PowComponent (A : Type u) [CommRing A] (M' : ℕ)
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : T[X]), IsGamma0PowAt W p k h →
        IsGamma0PowAt (C • W) p k (kernelVariableChangeDeg C (gamma0PowDeg p k) h)) :
    LevelComponent A where
  obj T _ _ := ↥M'.primeFactors → T[X]
  IsLevel W h := ∀ p : ↥M'.primeFactors, IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p)
  map f h := fun p => (h p).map f.toRingHom
  act C h := fun p => kernelVariableChangeDeg C (gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (h p)
  map_id h := funext fun _ => Polynomial.map_id
  map_comp f g h := funext fun p => (Polynomial.map_map f.toRingHom g.toRingHom (h p)).symm
  act_one h := funext fun p => kernelVariableChangeDeg_one _ (h p)
  act_mul C C' h := funext fun p => kernelVariableChangeDeg_mul C C' _ (h p)
  map_act f C h := funext fun p => kernelVariableChangeDeg_map f.toRingHom C _ (h p)
  isLevel_map f W h hh := fun p => IsGamma0PowAt.map f.toRingHom W (p : ℕ) _ (hh p)
  isLevel_act C W h hh := fun p => hM _ W C (p : ℕ) _ (h p) (hh p)

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

def rigidDataPow (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ((ModularCurve.gamma0PowComponent A M' hM).prod
    ((ModularCurve.levelPComponent A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).toRigid

end WeierstrassCurve.DrinfeldGlobal

end


