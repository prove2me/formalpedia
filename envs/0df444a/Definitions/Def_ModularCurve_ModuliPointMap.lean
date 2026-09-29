-- Prove2me | Definitions.Def_ModularCurve_ModuliPointMap
-- name    : ModularCurve_ModuliPointMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/dba2b658-5c85-5167-9adc-87c1bd640eec
-- title:
--   Base change of Γ₀(N)-pairs and moduli points, functorially
-- statement:
--   Throughout, $L$, $L'$, $L''$ are fields (in arbitrary universes) and $N$ a natural number. A `Gamma0Pair N L` is a structure carrying a Weierstrass curve over $L$, a proof that it is elliptic, a point `gen` of its affine point group, and the assertion $\mathrm{addOrderOf}(\mathtt{gen}) = N$; the relation `Gamma0Pair.Step P Q` holds when there is an admissible change of variables $\gamma$ with $\gamma \bullet P.\mathtt{toCurve} = Q.\mathtt{toCurve}$ and a natural number $k$ coprime to $N$ with $Q.\mathtt{gen}$ equal (over the identified curves) to $k \cdot \mathtt{vcInvFun}\,\gamma\,P.\mathtt{gen}$, and `ModuliPoint N L` is the quotient `Quot` of pairs by this relation, with `j` induced by the $j$-invariant of the underlying curve.
--
--   This module supplies the base-change functoriality of these data in arbitrary universes, built on the universe-polymorphic point map [`WeierstrassCurve.mapPoint`](../def/WeierstrassCurve_MapPoint.html#L18). For a ring homomorphism $\sigma\colon L \to L'$, `Gamma0Pair.map σ P` has underlying curve $P.\mathtt{toCurve}$ base-changed along $\sigma$ and generator `mapPoint σ P.gen`, whose additive order is again $N$ since `mapPoint` is an injective homomorphism; projections to curve and generator are recorded. The auxiliary lemmas state that $\sigma$ commutes with the inverse change-of-variables formulas $x \mapsto u^{-2}(x-r)$ and $(x,y)\mapsto u^{-3}(y-t-s(x-r))$, and hence that `mapPoint` intertwines `Point.vcInvFun` for $\gamma$ with that for $\gamma$ base-changed, as a heterogeneous equality over the equal curves $(\gamma \bullet V)^\sigma$ and $\gamma^\sigma \bullet V^\sigma$. Consequently `Step` is preserved by `Gamma0Pair.map σ`, so `ModuliPoint.map σ` is well defined on the quotient, satisfies $j(\mathtt{map}\,\sigma\,x) = \sigma(j(x))$, and is functorial: the identity homomorphism induces the identity and $\tau \circ \sigma$ induces `map τ ∘ map σ`, via an extensionality lemma for pairs (equal curves and heterogeneously equal generators). Finally, for fields in the lowest universe, `mapPoint` agrees with `ratPointMap` (and the corresponding additive homomorphisms agree), whence `Gamma0Pair.map σ` equals `gamma0PairMap σ` and `ModuliPoint.map σ` equals the function `moduliPointMapRingHom σ`.
--
--   **Relation to Mathlib.** Mathlib supplies Weierstrass curves, their admissible changes of variables, affine point groups and base change of curves; the Γ₀(N)-pairs, the step relation and the moduli sets `ModuliPoint` are the project's own, as are the two base-change maps on affine points — the universe-polymorphic `mapPoint` and the `Type`-pinned `ratPointMap` — which this module identifies.
--
--   **Where it is used.** The sets `ModuliPoint N L` are the project's elementary model for the non-cuspidal points of $Y_0(N)$ over a field $L$, a pair consisting of an elliptic curve in Weierstrass form together with a point of exact order $N$, taken up to change of variables and prime-to-$N$ multiples of the generator. Functoriality in the field is what allows such points to be compared along field embeddings, reductions and Galois automorphisms, the $j$-invariant being carried along equivariantly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ModuliPointMap.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_WeierstrassCurve_MapPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

set_option autoImplicit false

universe u v w

section Map

variable {L : Type u} {L' : Type v} [Field L] [Field L']
variable [DecidableEq L] [DecidableEq L']

omit [DecidableEq L] [DecidableEq L'] in

theorem vcXInv_map (σ : L →+* L') (γ : VariableChange L) (x : L) :
    σ (vcXInv γ x) = vcXInv (γ.map σ) (σ x) := by
  simp [vcXInv, map_mul, map_pow, map_sub]

omit [DecidableEq L] [DecidableEq L'] in

theorem vcYInv_map (σ : L →+* L') (γ : VariableChange L) (x y : L) :
    σ (vcYInv γ x y) = vcYInv (γ.map σ) (σ x) (σ y) := by
  simp [vcYInv, map_mul, map_pow, map_sub]

omit [DecidableEq L] [DecidableEq L'] in

theorem mapPoint_vcInvFun_heq (σ : L →+* L') (γ : VariableChange L) (V : WeierstrassCurve L)
    (P : V.toAffine.Point) :
    HEq (WeierstrassCurve.mapPoint σ (W₀ := γ • V) (Point.vcInvFun γ V.toAffine P))
        (Point.vcInvFun (γ.map σ) (V.map σ).toAffine (WeierstrassCurve.mapPoint σ (W₀ := V) P)) := by
  have hc : (γ • V).map σ = (γ.map σ) • (V.map σ) :=
    (WeierstrassCurve.map_variableChange V γ σ).symm
  cases P with
  | zero => exact Point.heq_zero hc
  | some x y h => exact Point.heq_some hc (vcXInv_map σ γ x) (vcYInv_map σ γ x y)

variable {N : ℕ}

def Gamma0Pair.map (σ : L →+* L') (P : Gamma0Pair N L) : Gamma0Pair N L' where
  toCurve := P.toCurve.map σ
  isElliptic := inferInstance
  gen := WeierstrassCurve.mapPoint σ (W₀ := P.toCurve) P.gen
  addOrderOf_gen := (WeierstrassCurve.addOrderOf_mapPoint σ P.gen).trans P.addOrderOf_gen

@[simp] theorem Gamma0Pair.map_toCurve (σ : L →+* L') (P : Gamma0Pair N L) :
    (P.map σ).toCurve = P.toCurve.map σ := rfl

@[simp] theorem Gamma0Pair.map_gen (σ : L →+* L') (P : Gamma0Pair N L) :
    (P.map σ).gen = WeierstrassCurve.mapPoint σ (W₀ := P.toCurve) P.gen := rfl

theorem Gamma0Pair.Step.map (σ : L →+* L') {P Q : Gamma0Pair N L}
    (h : Gamma0Pair.Step P Q) :
    Gamma0Pair.Step (P.map σ) (Q.map σ) := by
  obtain ⟨γ, hγ, k, hk, hgen⟩ := h
  obtain ⟨WP, hEP, gP, hgP⟩ := P
  obtain ⟨WQ, hEQ, gQ, hgQ⟩ := Q
  change γ • WP = WQ at hγ
  subst hγ
  change HEq gQ (k • Point.vcInvFun γ WP.toAffine gP) at hgen
  have hgen' : gQ = k • Point.vcInvFun γ WP.toAffine gP := eq_of_heq hgen
  refine ⟨γ.map σ, ?_, k, hk, ?_⟩
  · show γ.map σ • WP.map σ = (γ • WP).map σ
    exact WeierstrassCurve.map_variableChange WP γ σ
  · show HEq (WeierstrassCurve.mapPoint σ (W₀ := γ • WP) gQ)
      (k • Point.vcInvFun (γ.map σ) (WP.map σ).toAffine (WeierstrassCurve.mapPoint σ (W₀ := WP) gP))
    rw [hgen']
    refine HEq.trans (heq_of_eq (WeierstrassCurve.mapPoint_nsmul σ k
      (Point.vcInvFun γ WP.toAffine gP))) ?_
    exact Point.heq_nsmul (WeierstrassCurve.map_variableChange WP γ σ).symm k
      (mapPoint_vcInvFun_heq σ γ WP gP)

def ModuliPoint.map (σ : L →+* L') : ModuliPoint N L → ModuliPoint N L' :=
  Quot.lift (fun P => (Quot.mk _ (P.map σ) : ModuliPoint N L'))
    fun _ _ h => Quot.sound (Gamma0Pair.Step.map σ h)

@[simp] theorem ModuliPoint.map_mk (σ : L →+* L') (P : Gamma0Pair N L) :
    ModuliPoint.map σ (Quot.mk _ P : ModuliPoint N L) = (Quot.mk _ (P.map σ) : ModuliPoint N L') :=
  rfl

theorem ModuliPoint.j_map (σ : L →+* L') (x : ModuliPoint N L) :
    (ModuliPoint.map σ x).j = σ x.j := by
  induction x using Quot.ind with
  | _ P => exact (P.toCurve.map_j σ)

end Map

section Functor

variable {L : Type u} {L' : Type v} {L'' : Type w} [Field L] [Field L'] [Field L'']
variable [DecidableEq L] [DecidableEq L'] [DecidableEq L''] {N : ℕ}

theorem Gamma0Pair.ext_heq {P Q : Gamma0Pair N L} (h1 : P.toCurve = Q.toCurve) (h2 : HEq P.gen Q.gen) :
    P = Q := by
  obtain ⟨WP, hEP, gP, hgP⟩ := P
  obtain ⟨WQ, hEQ, gQ, hgQ⟩ := Q
  cases h1
  cases h2
  rfl

theorem ModuliPoint.map_id (x : ModuliPoint N L) : ModuliPoint.map (RingHom.id L) x = x := by
  induction x using Quot.ind with
  | _ P =>
    rw [ModuliPoint.map_mk]
    congr 1
    exact Gamma0Pair.ext_heq (WeierstrassCurve.map_id P.toCurve)
      (WeierstrassCurve.mapPoint_id_heq P.toCurve P.gen)

theorem ModuliPoint.map_comp (σ : L →+* L') (τ : L' →+* L'') (x : ModuliPoint N L) :
    ModuliPoint.map (τ.comp σ) x = ModuliPoint.map τ (ModuliPoint.map σ x) := by
  induction x using Quot.ind with
  | _ P =>
    rw [ModuliPoint.map_mk, ModuliPoint.map_mk, ModuliPoint.map_mk]
    congr 1
    exact Gamma0Pair.ext_heq (WeierstrassCurve.map_map P.toCurve σ τ).symm
      (WeierstrassCurve.mapPoint_comp_heq σ τ P.toCurve P.gen)

end Functor

section Bridge

variable {L L' : Type} [Field L] [Field L'] [DecidableEq L] [DecidableEq L'] {N : ℕ}

omit [DecidableEq L] [DecidableEq L'] in
@[simp] theorem _root_.WeierstrassCurve.mapPoint_eq_ratPointMap (σ : L →+* L') (V : WeierstrassCurve L)
    (P : V.toAffine.Point) :
    WeierstrassCurve.mapPoint σ (W₀ := V) P = WeierstrassCurve.ratPointMap σ (W₀ := V) P := by
  cases P <;> rfl

theorem _root_.WeierstrassCurve.mapPointHom_eq_ratPointHom (σ : L →+* L') (V : WeierstrassCurve L) :
    WeierstrassCurve.mapPointHom σ (W₀ := V) = WeierstrassCurve.ratPointHom σ (W₀ := V) := by
  ext P
  exact WeierstrassCurve.mapPoint_eq_ratPointMap σ V P

@[simp] theorem Gamma0Pair.map_eq_gamma0PairMap (σ : L →+* L') (P : Gamma0Pair N L) :
    P.map σ = gamma0PairMap σ P :=
  Gamma0Pair.ext_heq rfl (heq_of_eq (WeierstrassCurve.mapPoint_eq_ratPointMap σ P.toCurve P.gen))

@[simp] theorem ModuliPoint.map_eq_moduliPointMapRingHom (σ : L →+* L') :
    (ModuliPoint.map σ : ModuliPoint N L → ModuliPoint N L') = moduliPointMapRingHom σ := by
  funext x
  induction x using Quot.ind with
  | _ P => rw [ModuliPoint.map_mk, moduliPointMapRingHom_mk, Gamma0Pair.map_eq_gamma0PairMap]

theorem ModuliPoint.map_apply_eq_moduliPointMapRingHom (σ : L →+* L') (x : ModuliPoint N L) :
    ModuliPoint.map σ x = moduliPointMapRingHom σ x := by
  rw [ModuliPoint.map_eq_moduliPointMapRingHom]

end Bridge

end ModularCurve

end


