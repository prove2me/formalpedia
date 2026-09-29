-- Prove2me | Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
-- name    : ModularCurve_WeierstrassGamma0Sqf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/e5aa2bae-6dd9-5698-ab78-8d4194e8b9b2
-- title:
--   Γ₀(M′)-level structures for squarefree M′ as prime-by-prime kernels
-- statement:
--   For a Weierstrass curve $W$ over a commutative ring $T$, [`WeierstrassCurve.IsTwoKernel W h`](../def/ModularCurve_WeierstrassGamma0Sqf.html#L22) is the predicate on a polynomial $h \in T[X]$ asserting three things: $\deg h \le 1$, the coefficient of $X$ in $h$ equals $1$, and $h$ divides $W.\Psi_2^2$ (Mathlib's squared second division polynomial). Such an $h$ is monic, and the predicate is preserved by base change along a ring homomorphism $f \colon T \to T'$, with $W$ replaced by `W.map f` and $h$ by `h.map f`. The numerical function [`ModularCurve.gamma0Deg p`](../def/ModularCurve_WeierstrassGamma0Sqf.html#L42) is $1$ for $p = 2$ and $(p-1)/2$ otherwise, and [`ModularCurve.IsGamma0At W p h`](../def/ModularCurve_WeierstrassGamma0Sqf.html#L44) is defined by case split: it is `IsTwoKernel W h` when $p = 2$ and the project's cyclic-kernel predicate `W.IsCyclicKernel p h` otherwise (degree at most $(p-1)/2$, leading coefficient $1$ in that degree, $h \mid W.\mathrm{pre}\Psi_p$, and $h \mid W.\mathrm{smulNumerator}\,a\,((p-1)/2)\,h$ for $2 \le a \le (p-1)/2$). Two unfolding lemmas record the two branches, and `IsGamma0At.map` gives compatibility with base change.
--
--   Given a base ring $A$, a natural number $M'$, and a hypothesis `hM` asserting that `IsGamma0At` is preserved, for every $A$-algebra $T$, under the action of a variable change $C$ on $W$ together with the substitution `kernelVariableChangeDeg C (gamma0Deg p)` on the polynomial, [`ModularCurve.gamma0SqfComponent`](../def/ModularCurve_WeierstrassGamma0Sqf.html#L61) builds a `LevelComponent A` whose objects over $T$ are families $p \mapsto h_p \in T[X]$ indexed by the prime factors of $M'$, the level condition being `IsGamma0At W p (h p)` for every such $p$; base change acts coefficientwise and variable changes act through `kernelVariableChangeDeg` with degree `gamma0Deg p` in each coordinate. Finally [`WeierstrassCurve.DrinfeldGlobal.rigidDataSqf`](../def/ModularCurve_WeierstrassGamma0Sqf.html#L81) assembles, from transport hypotheses `hℓ` for level-$p$ data and `hM` as above, a family of group laws $\mathcal{G}$ and a level transport $\mathcal{T}$, the rigid Weierstrass datum obtained as the product of this $\Gamma_0(M')$ component with the level-$\ell$ component and the Drinfeld level-$q$ component, passed through `toRigid`.
--
--   **Relation to Mathlib.** Mathlib supplies the Weierstrass-curve division polynomials used here ($\Psi_2^2$, $\mathrm{pre}\Psi_N$, $\Phi_a$, $\Psi_a^2$) and the group of variable changes; the level predicates, level components and rigid Weierstrass data are the project's own notions.
--
--   **Where it is used.** The cyclic-kernel predicate of the project encodes a $\Gamma_0(N)$-structure for an odd prime $N$; for squarefree $M'$ a $\Gamma_0(M')$-structure is recorded instead as the tuple of prime-level kernels, one for each prime factor of $M'$, together with the $p=2$ case handled by `IsTwoKernel`. The resulting level component feeds the rigid Weierstrass data used to present the modular curves with auxiliary level structure occurring in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeierstrassGamma0Sqf.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
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

structure IsTwoKernel (h : T[X]) : Prop where
  natDegree_le : h.natDegree ≤ 1
  coeff_eq_one : h.coeff 1 = 1
  dvd_Ψ₂Sq : h ∣ W.Ψ₂Sq

theorem IsTwoKernel.monic {h : T[X]} (hh : W.IsTwoKernel h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one

theorem IsTwoKernel.map {T' : Type u} [CommRing T'] (f : T →+* T') {h : T[X]} (hh : W.IsTwoKernel h) :
    (W.map f).IsTwoKernel (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  dvd_Ψ₂Sq := by rw [WeierstrassCurve.map_Ψ₂Sq]; exact Polynomial.map_dvd f hh.dvd_Ψ₂Sq

end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]

def gamma0Deg (p : ℕ) : ℕ := if p = 2 then 1 else (p - 1) / 2

def IsGamma0At (W : WeierstrassCurve T) (p : ℕ) (h : T[X]) : Prop :=
  if p = 2 then W.IsTwoKernel h else W.IsCyclicKernel p h

theorem isGamma0At_two (W : WeierstrassCurve T) (h : T[X]) : IsGamma0At W 2 h ↔ W.IsTwoKernel h := by
  simp [IsGamma0At]

theorem isGamma0At_of_ne_two (W : WeierstrassCurve T) {p : ℕ} (hp : p ≠ 2) (h : T[X]) :
    IsGamma0At W p h ↔ W.IsCyclicKernel p h := by
  simp [IsGamma0At, hp]

theorem IsGamma0At.map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (p : ℕ) {h : T[X]}
    (hh : IsGamma0At W p h) : IsGamma0At (W.map f) p (h.map f) := by
  by_cases hp : p = 2
  · subst hp
    exact (isGamma0At_two _ _).2 (((isGamma0At_two _ _).1 hh).map W f)
  · exact (isGamma0At_of_ne_two _ hp _).2 (((isGamma0At_of_ne_two _ hp _).1 hh).map W f)

def gamma0SqfComponent (A : Type u) [CommRing A] (M' : ℕ)
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p : ℕ) (h : T[X]), IsGamma0At W p h → IsGamma0At (C • W) p (kernelVariableChangeDeg C (gamma0Deg p) h)) :
    LevelComponent A where
  obj T _ _ := ↥M'.primeFactors → T[X]
  IsLevel W h := ∀ p : ↥M'.primeFactors, IsGamma0At W (p : ℕ) (h p)
  map f h := fun p => (h p).map f.toRingHom
  act C h := fun p => kernelVariableChangeDeg C (gamma0Deg (p : ℕ)) (h p)
  map_id h := funext fun _ => Polynomial.map_id
  map_comp f g h := funext fun p => (Polynomial.map_map f.toRingHom g.toRingHom (h p)).symm
  act_one h := funext fun p => kernelVariableChangeDeg_one _ (h p)
  act_mul C C' h := funext fun p => kernelVariableChangeDeg_mul C C' _ (h p)
  map_act f C h := funext fun p => kernelVariableChangeDeg_map f.toRingHom C _ (h p)
  isLevel_map f W h hh := fun p => IsGamma0At.map f.toRingHom W (p : ℕ) (hh p)
  isLevel_act C W h hh := fun p => hM _ W C (p : ℕ) (h p) (hh p)

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

def rigidDataSqf (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p : ℕ) (h : Polynomial T), ModularCurve.IsGamma0At W p h →
        ModularCurve.IsGamma0At (C • W) p (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0Deg p) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ((ModularCurve.gamma0SqfComponent A M' hM).prod
    ((ModularCurve.levelPComponent A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).toRigid

end WeierstrassCurve.DrinfeldGlobal

end


