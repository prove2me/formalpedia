-- Prove2me | Definitions.Def_ModularCurve_JHTwistType
-- name    : ModularCurve_JHTwistType
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/2cb04cde-f8b6-5c74-9984-654e1108f629
-- title:
--   Twist vectors and twist type for node annuli at p
-- statement:
--   Standing context: a prime $p$, a level $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field is algebraically closed of characteristic $p$, a specialisation datum `Psp : JHPlaceSpecialization p M H hpM A`, two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha,\beta$ from the function field at level $(M/p, \mathrm{infSubgroup})$ into $\overline{\mathbb{Q}}\cdot X_H(M)$'s function field, a self-map $\delta$ of the places of the special-fibre field, a finite set $SS$ of pairs of such places (the glued nodes), widths $e : SS \to \mathbb{N}$, annuli $An : SS \to$ `Annulus`, and a rational position function $pos$ on places.
--
--   `TwistVec ι` is a record of two integers `aZ`, `aZ'` together with a family `aE : ι → ℕ → ℤ`: one value at each of the two ends of every chain and one at each interior link. `AnnulusPositionLaw` asserts that for each $s \in SS$ and each place $V$ in the domain of $An\,s$ one has $0 < pos\,s\,V < e\,s$ and $v_A\bigl(V(\pi_s z_s^{-1})\bigr)^{\mathrm{den}} = v_A(p)^{\mathrm{num}}$, where $\pi_s$ is the modulus and $z_s$ the parameter of the annulus and $\mathrm{num}, \mathrm{den}$ are those of $pos\,s\,V$; so $pos$ is a rational depth measured from the reciprocal end parameter. `twistChainVal` reads a twist vector as a function of $d \in \mathbb{N}$: `aZ` at $d = 0$, `aZ'` for $d \ge e\,s$, `aE s d` in between. `twistCircleDeg D s d` is the tent-weighted rational degree $\sum_V D(V)\max(0, 1 - |pos\,s\,V - d|)$ over the support of $D$ inside the annulus. `twistEndShareFst`/`Snd` take the numerator of this quantity at $d = 0$, resp. $d = e\,s$, when it is an integer and $0$ otherwise; `twistEndOrderFst`/`Snd` add these shares to the first difference of `twistChainVal` at the respective end. `IsTwistOf a D` asserts three equations: the degrees of `Psp.fstDiv` and `Psp.sndDiv` of $D$ (the parts of $D$ supported on strictly-first, resp. strictly-second, places) equal minus the sums over $s \in SS$ of the two end orders, and for $1 \le d \le e\,s - 1$ the tent degree `twistCircleDeg D s d` equals minus the second difference $a(d-1) - 2a(d) + a(d+1)$ of `twistChainVal`. `IsTwistType D` is the existence of such a twist vector. All are total definitions, with the junk value $0$ where the integrality condition in the end shares fails.
--
--   **Relation to Mathlib.** Mathlib has no notion of annuli or component charts of a semistable model, of divisors on a function field indexed by places, or of twist vectors; these are the project's own, built on the project's `Annulus` and `Divisor` structures.
--
--   **Where it is used.** These predicates describe the discrete data attached to an inertia-invariant divisor class on $X_H(M)$ near the supersingular nodes at $p \mid M$: the twist vector records the values of a piecewise-linear function on the chain of exceptional components over each node, and the equations of `IsTwistOf` are the balancing conditions linking it to the degrees of the two branch parts of the divisor. They feed the analysis of the component group of the Jacobian at $p$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JHTwistType.lean

import Definitions.Def_ModularCurve_JHNodeDepthInf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

structure TwistVec (ι : Type*) where

  aZ : ℤ

  aZ' : ℤ

  aE : ι → ℕ → ℤ

section

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

variable (Psp : JHPlaceSpecialization p M H hpM A)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
  (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (e : ↥SS → ℕ) (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)

def AnnulusPositionLaw : Prop :=
  ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom →
    0 < pos s V ∧ pos s V < e s ∧
      A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * ((An s).param)⁻¹)) ^ (pos s V).den =
        A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ (pos s V).num.toNat

def twistChainVal (a : TwistVec ↥SS) (s : ↥SS) (d : ℕ) : ℤ :=
  if d = 0 then a.aZ else if e s ≤ d then a.aZ' else a.aE s d

open Classical in

def twistCircleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) (d : ℕ) : ℚ :=
  ∑ V ∈ D.support with V ∈ (An s).dom, (D V : ℚ) * max 0 (1 - |pos s V - d|)

def twistEndShareFst (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  if (twistCircleDeg SS An pos D s 0).den = 1 then (twistCircleDeg SS An pos D s 0).num else 0

def twistEndShareSnd (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  if (twistCircleDeg SS An pos D s (e s)).den = 1 then (twistCircleDeg SS An pos D s (e s)).num else 0

def twistEndOrderFst (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  (twistChainVal SS e a s 1 - twistChainVal SS e a s 0) + twistEndShareFst SS An pos D s

def twistEndOrderSnd (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  (twistChainVal SS e a s (e s - 1) - twistChainVal SS e a s (e s)) + twistEndShareSnd SS e An pos D s

def IsTwistOf (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Prop :=
  Divisor.degree (Psp.fstDiv α β hα hβ δ D) = -∑ s : ↥SS, twistEndOrderFst SS e An pos a D s ∧
    Divisor.degree (Psp.sndDiv α β hα hβ δ D) = -∑ s : ↥SS, twistEndOrderSnd SS e An pos a D s ∧
    ∀ (s : ↥SS) (d : ℕ), 1 ≤ d → d + 1 ≤ e s →
      twistCircleDeg SS An pos D s d =
        -((twistChainVal SS e a s (d - 1) - 2 * twistChainVal SS e a s d + twistChainVal SS e a s (d + 1) : ℤ) : ℚ)

def IsTwistType (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Prop :=
  ∃ a : TwistVec ↥SS, Psp.IsTwistOf α β hα hβ δ SS e An pos a D

end

end JHPlaceSpecialization
end ModularCurve

end


