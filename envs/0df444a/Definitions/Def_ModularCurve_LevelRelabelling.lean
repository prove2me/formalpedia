-- Prove2me | Definitions.Def_ModularCurve_LevelRelabelling
-- name    : ModularCurve_LevelRelabelling
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/0924fc0f-159d-5058-9a7b-96de3932bf44
-- title:
--   Relabelling level structures by integral 2 × 2 matrices
-- statement:
--   This module defines the operation of changing the basis of a level structure by a $2\times 2$ integer matrix, in two incarnations, and a predicate pinning down automorphisms of a full-level moduli problem as such relabellings.
--
--   For a Weierstrass curve $W$ over a field $T$, `toPoint` sends a coordinate pair $(x,y)$ to the affine point `Point.some x y` when $(x,y)$ is a nonsingular point of the affine model, and to the point at infinity otherwise, while `ofPoint` returns the coordinates of an affine point and $(0,0)$ at infinity. With these, `LevelPData.relabel W g D` takes the quadruple $D=(x_P,y_P,x_Q,y_Q)$ of [`ModularCurve.LevelPData T`](../def/ModularCurve_KatzLevelP.html#L43), converts it to a pair $P,Q$ of points of `W.toAffine.Point`, and records the coordinates of $g_{00}\cdot P+g_{10}\cdot Q$ and $g_{01}\cdot P+g_{11}\cdot Q$; that is, the row vector $(P,Q)$ is multiplied on the right by $g$, the integers acting by the Mathlib group law.
--
--   In the Drinfeld setting, for a projective Weierstrass curve $W$ over a commutative ring $T$ with a relative group law $G$ on its projective model, `zsmulSection` defines the action of $\mathbb{Z}$ on sections by `G.nsmul` for non-negative integers and by `G.inv` of `G.nsmul` for negative ones, and `zlinComb G P Q a b` is $aP+bQ$ formed with `G.mul`. Then `RawDrinfeldPair.relabel 𝒢 g x hΔ` keeps the curve of $x$ and replaces $(P,Q)$ by $(P,Q)\cdot g$, using the group law $𝒢\,T\,x.\mathrm{curve}\,h_\Delta$ supplied by the family $𝒢$ at the unit discriminant witness $h_\Delta$.
--
--   Finally, `IsModuliRelabelling A ℓ M' q hℓ hN 𝒢 𝒯 ρ` is a predicate on a family $\rho$ indexed by $\Gamma_0(M')$ of automorphisms of the moduli datum attached to `rigidData A ℓ M' q hℓ hN 𝒢 𝒯`: it asserts that for every $\gamma$, every field $T$ which is an $A$-algebra, and raw data $x,x'$ over $T$ with $x.\mathrm{level}.2.2.\mathrm{curve}$ of unit discriminant, if $x'$ has the same curve as $x$, the same first level component (the kernel polynomial at level $M'$), its `LevelPData` component equal to `LevelPData.relabel` of that of $x$ by the integral matrix underlying $\gamma$, and its raw Drinfeld pair equal to `RawDrinfeldPair.relabel` of that of $x$ by the same matrix, then $(\rho\,\gamma).\mathrm{act}$ carries the class of $x$ to the class of $x'$ in the quotient by variable changes. The condition is imposed only on field-valued points and is stated without constructing the relabelled raw datum.
--
--   **Relation to Mathlib.** Mathlib supplies the group law on affine points of a Weierstrass curve used by `toPoint`/`ofPoint`, and the congruence subgroups `CongruenceSubgroup.Gamma0`; the level structures, the relative group laws on projective models and the moduli data relabelled here are the project's own notions.
--
--   **Where it is used.** These relabellings express the right action of $\Gamma_0(M')$ on the level data of the fine moduli problem for elliptic curves with a cyclic subgroup, a Katz level-$\ell$ basis and a Drinfeld $\Gamma(q)$-basis; the predicate `IsModuliRelabelling` is what ties a given family of automorphisms of the moduli problem to the matrix action, and so to the action on $q$-expansions used on the modular-curve side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelRelabelling.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open scoped Classical

namespace ModularCurve.LevelRelabelling

section LevelP

variable {T : Type u} [Field T] (W : WeierstrassCurve T)

def toPoint (x y : T) : W.toAffine.Point :=
  if h : W.toAffine.Nonsingular x y then WeierstrassCurve.Affine.Point.some x y h else 0

def ofPoint : W.toAffine.Point → T × T
  | WeierstrassCurve.Affine.Point.zero => (0, 0)
  | WeierstrassCurve.Affine.Point.some x y _ => (x, y)

def LevelPData.relabel (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T) : ModularCurve.LevelPData T :=
  let P := toPoint W D.xP D.yP
  let Q := toPoint W D.xQ D.yQ
  let P' := ofPoint W (g 0 0 • P + g 1 0 • Q)
  let Q' := ofPoint W (g 0 1 • P + g 1 1 • Q)
  ⟨P'.1, P'.2, Q'.1, Q'.2⟩

end LevelP

section Drinfeld

open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T}

def zsmulSection (G : RelativeGroupLaw T (projModelStrCR W)) : ℤ → Section W → Section W
  | Int.ofNat k, P => G.nsmul _ k P
  | Int.negSucc k, P => G.inv _ (G.nsmul _ (k + 1) P)

def zlinComb (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) (a b : ℤ) : Section W :=
  G.mul _ (zsmulSection G a P) (zsmulSection G b Q)

variable {A : Type u} [CommRing A] [Algebra A T]

def RawDrinfeldPair.relabel (𝒢 : GroupLaws A) (g : Matrix (Fin 2) (Fin 2) ℤ) (x : RawDrinfeldPair T)
    (hΔ : IsUnit x.curve.Δ) : RawDrinfeldPair T :=
  ⟨x.curve,
    zlinComb (𝒢 T x.curve hΔ) x.P x.Q (g 0 0) (g 1 0),
    zlinComb (𝒢 T x.curve hΔ) x.P x.Q (g 0 1) (g 1 1)⟩

end Drinfeld

section Pin

open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

def IsModuliRelabelling (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : Polynomial T), W.IsCyclicKernel M' h →
        (C • W).IsCyclicKernel M' (ModularCurve.kernelVariableChangeDeg C ((M' - 1) / 2) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidData A ℓ M' q hℓ hN 𝒢 𝒯).toLevelModuliDatum.ProblemAut) : Prop :=
  ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type u) [Field T] [Algebra A T]
    (x x' : (rigidData A ℓ M' q hℓ hN 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
    x'.curve = x.curve →
    x'.level.1 = x.level.1 →
    x'.level.2.1 = LevelPData.relabel x.curve ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
    x'.level.2.2 = RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
    (ρ γ).act (Quot.mk _ x) = Quot.mk _ x'

end Pin

end ModularCurve.LevelRelabelling

end


