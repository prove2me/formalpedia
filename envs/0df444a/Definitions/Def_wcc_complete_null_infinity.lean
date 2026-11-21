-- Prove2me | Definitions.Def_wcc_complete_null_infinity
-- name    : wcc_complete_null_infinity
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T12:54:36.533002+00:00
-- url     : https://prove2.me/theorems/4b7a2ee5-5ded-430f-a5e0-fde875ce62f5
-- title:
--   Complete future null infinity (Christodoulou) and genericity
-- statement:
--   This file defines **complete future null infinity** in Christodoulou's sense and the notion of **generic** initial data used by the goal.
--
--   `sphereNormal3 h x` is the outward $\bar g$-unit normal to the Euclidean sphere $\|x\|=R$ in $\mathbb R^3$ (the Euclidean radial covector raised by $\bar g$ and normalized); `devNormal` is the future unit normal to the initial surface of a development. Pushed forward by $\iota$, these give the null tangents $L_+=n+N$ (outgoing) and $L_-=n-N$ (incoming) of the source.
--
--   `HasCompleteFutureNullInfinity h k D` asserts: there is a radius $R_0>0$ such that every outgoing null geodesic from $\partial B_{R_0}$ with tangent $n+N$ is defined on all of $[0,\infty)$ (the boundary $C_0^+=\partial J^+(B_{R_0})$ has future-complete generators), and for every $A>0$ there is $R\ge R_0$ such that every incoming null geodesic from $\partial B_R$ with tangent $n-N$ meets $C_0^+$ at some parameter $\tau_c\ge0$ and extends as a null geodesic to parameter $\tau_c+A$ (affine length at least $A$ beyond the meeting). This is Christodoulou's definition (CQG 16 (1999) A26–A27), with Euclidean balls as the cofinal family of domains.
--
--   `CompletesNullInfinity h k` says every maximal development of $(h,k)$ has complete future null infinity; `GoodData` is the set of asymptotically flat data with this property; `dataDist` is the weighted $C^3$ distance; `GenericOpenDense S` says $S$ is open and dense in the asymptotically flat data for `dataDist`.
--
--   **Formalization Note.** The affine origin is taken at $\partial B$ (parameter $0$) rather than at $C^-\cap C_0^+$; affine length is translation-invariant, so the condition "extends to $\tau_c+A$" is exactly "affine length $\ge A$ from the meeting". `dataDist` uses `ENNReal.toReal`, which is the genuine value on asymptotically flat pairs (finite weighted size).
-- source:
--   Christodoulou 1999, CQG 16 A23-A35, §1 pp. A26-A27 (definition of complete future null infinity, normalization L_-=T-N, affine parameter); https://doi.org/10.1088/0264-9381/16/12A/302

import Mathlib
import Definitions.Def_scc_coordinate_framework
import Definitions.Def_wcc_initial_data
import Definitions.Def_wcc_spacetime

open scoped Matrix
open Set StrongCosmicCensorship

namespace WeakCosmicCensorship

noncomputable def sphereNormal3 (h : Field3) (x : Coords3) : Coords3 :=
  let v : Coords3 := fun a => x a / ‖x‖
  let nv : Coords3 := fun a => ∑ b : Fin 3, ginv3 h x a b * v b
  let norm := Real.sqrt (∑ a : Fin 3, ∑ b : Fin 3, ginv3 h x a b * v a * v b)
  fun a => nv a / norm

noncomputable def devNormal (h k : Field3) (D : Development h k) : Coords3 → Coords :=
  Classical.choose D.induced

noncomputable def HasCompleteFutureNullInfinity (h k : Field3) (D : Development h k) : Prop :=
  let n := devNormal h k D
  ∃ R₀ : ℝ, 0 < R₀ ∧
    (∀ x : Coords3, ‖x‖ = R₀ → ∃ γ : ℝ → Coords,
      IsNullGeodesicOn D.U D.g (Ici 0) γ ∧ γ 0 = D.ι x ∧
        vel γ 0 = (fun A => n x A + (jac34 D.ι x).mulVec (sphereNormal3 h x) A)) ∧
    (∀ A : ℝ, 0 < A → ∃ R : ℝ, R₀ ≤ R ∧
      ∀ x : Coords3, ‖x‖ = R →
        ∃ γ : ℝ → Coords, ∃ τc : ℝ, 0 ≤ τc ∧
          IsNullGeodesicOn D.U D.g (Icc 0 (τc + A)) γ ∧
          γ 0 = D.ι x ∧
          vel γ 0 = (fun A => n x A - (jac34 D.ι x).mulVec (sphereNormal3 h x) A) ∧
          γ τc ∈ frontier (causalFuture D.U D.g D.T (D.ι '' {y : Coords3 | ‖y‖ ≤ R₀})))

noncomputable def dataDist (p q : Field3 × Field3) : ℝ :=
  (weightedSize3 3 1 (fun x => p.1 x - q.1 x)).toReal +
  (weightedSize3 3 2 (fun x => p.2 x - q.2 x)).toReal

def CompletesNullInfinity (h k : Field3) : Prop :=
  ∀ D : Development h k, IsMaximalDevelopment h k D → HasCompleteFutureNullInfinity h k D

def GoodData : Set (Field3 × Field3) :=
  {p | IsAFInitialData p.1 p.2 ∧ CompletesNullInfinity p.1 p.2}

def GenericOpenDense (S : Set (Field3 × Field3)) : Prop :=
  (∀ p ∈ S, ∃ ε : ℝ, 0 < ε ∧
    ∀ q : Field3 × Field3, IsAFInitialData q.1 q.2 → dataDist p q < ε → q ∈ S) ∧
  (∀ p : Field3 × Field3, IsAFInitialData p.1 p.2 →
    ∀ ε : ℝ, 0 < ε → ∃ q ∈ S, dataDist p q < ε)

end WeakCosmicCensorship


