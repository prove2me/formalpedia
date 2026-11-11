-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Repulsion
-- name    : ConstrainedCorrelationRepulsion_Main_Repulsion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:56.140391+00:00
-- url     : https://prove2.me/theorems/a74ef8f0-ee73-4620-9a2c-e7ad6f8d493c
-- title:
--   Finite categorical sampling and both Repulsion recursions
-- statement:
--   Repulsion uses a strict ball in the current vertex set and recurses on both parts of a proper split. Empty sets return no cluster; terminal sets return one cluster. Radius $2/3$ has both uniform proper-center sampling and deterministic minimum-excess selection. Radius one uses the deterministic minimum-excess rule, with ties broken by vertex order.
--
--   The capped function is $b(x)=2x^2/(1-x)$ below $(\sqrt5-1)/2$, and $b(x)=2$ above that threshold, including $b(1)=2$. At distance one the radius-one pair potential is the positive-label indicator; below one it is $1-a+a b(x)$. The radius-$2/3$ potential is the Appendix A potential. Fuel and invalid categorical fallbacks totalize the functions; the theorems prove that valid inputs follow the stated recursion. Categorical laws retain exactly the supplied probabilities when valid, rather than silently renormalizing them.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), §2.1, §6.1, Appendix A, printed pp.4–5, 30–31, 41–42 (PDF pp.5–6, 31–32, 42–43)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Units

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

/-- Finite categorical sampling, totalized by `none` when the supplied masses are invalid.
On its intended domain its masses are exactly the specified masses (not renormalized). -/
noncomputable def categorical {A : Type} [Fintype A] (w : A → ℝ) : PMF (Option A) :=
  if h : (∑ a, ENNReal.ofReal (w a)) = 1 ∧ ∀ a, 0 ≤ w a then
    (PMF.ofFintype (fun a => ENNReal.ofReal (w a)) h.1).map some
  else PMF.pure none

noncomputable def b (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < (Real.sqrt 5 - 1) / 2 then 2 * x ^ 2 / (1 - x) else 2

noncomputable def potentialOne {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (u v : Fin n) : ℝ :=
  if x u v < 1 then (if I.positive.Adj u v then b (x u v) else 1)
  else if I.positive.Adj u v then 1 else 0

noncomputable def potentialTwoThirds {n : ℕ} (I : Instance n)
    (x : Fin n → Fin n → ℝ) (u v : Fin n) : ℝ :=
  if x u v < 2 / 3 then (if I.positive.Adj u v then 3 * x u v else 1)
  else if I.positive.Adj u v then 1 else 0

noncomputable def potentialSum {n : ℕ} (phi : Fin n → Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ := pairSum (fun u v => if u ∈ S ∧ v ∈ S then phi u v else 0)

noncomputable def ball {n : ℕ} (x : Fin n → Fin n → ℝ) (theta : ℝ)
    (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := S.filter (fun u => x v u < theta)

noncomputable def properCenters {n : ℕ} (x : Fin n → Fin n → ℝ) (theta : ℝ)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun v => (ball x theta S v).Nonempty ∧ ball x theta S v ≠ S)

noncomputable def boundary {n : ℕ} (I : Instance n) (A B : Finset (Fin n)) : ℝ :=
  ∑ u ∈ A, ∑ v ∈ B, if I.positive.Adj u v then 1 else 0

noncomputable def excess {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (theta : ℝ) (phi : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (v : Fin n) : ℝ :=
  let A := ball x theta S v
  boundary I A (S \ A) + potentialSum phi A + potentialSum phi (S \ A) - potentialSum phi S

/-- Minimum excess among proper centers, ties broken by the vertex order. This scans at most
n centers; it does not optimize a partition. -/
noncomputable def minimizingCenter {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (theta : ℝ) (phi : Fin n → Fin n → ℝ) (S : Finset (Fin n)) : Option (Fin n) :=
  let candidates := (properCenters x theta S).filter (fun v =>
    ∀ w ∈ properCenters x theta S, excess I x theta phi S v ≤ excess I x theta phi S w)
  if h : candidates.Nonempty then some (candidates.min' h) else none

/-- The empty-set and terminal rules are explicit. Fuel n suffices on a feasible pseudometric;
the zero-fuel fallback is only a totalization. Both sides of a proper split are recursed on. -/
noncomputable def repulsionBlocks {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (theta : ℝ) (phi : Fin n → Fin n → ℝ) : ℕ → Finset (Fin n) → List (Finset (Fin n))
  | 0, S => S.toList.map (fun v => {v})
  | fuel + 1, S =>
    if S = ∅ then [] else
    if ∀ u ∈ S, ∀ v ∈ S, x u v < theta then [S] else
    match minimizingCenter I x theta phi S with
    | none => S.toList.map (fun v => {v})
    | some v =>
      let A := ball x theta S v
      repulsionBlocks I x theta phi fuel A ++ repulsionBlocks I x theta phi fuel (S \ A)

noncomputable def randomRepulsionBlocks {n : ℕ} (I : Instance n)
    (x : Fin n → Fin n → ℝ) : ℕ → Finset (Fin n) → PMF (List (Finset (Fin n)))
  | 0, S => PMF.pure (S.toList.map (fun v => {v}))
  | fuel + 1, S =>
    if S = ∅ then PMF.pure [] else
    if ∀ u ∈ S, ∀ v ∈ S, x u v < 2 / 3 then PMF.pure [S] else
    (categorical (fun v : Fin n => if v ∈ properCenters x (2/3) S then
      1 / ((properCenters x (2/3) S).card : ℝ) else 0)).bind fun c =>
      match c with
      | none => PMF.pure (S.toList.map (fun v => {v}))
      | some v =>
        let A := ball x (2/3) S v
        (randomRepulsionBlocks I x fuel A).bind fun left =>
        (randomRepulsionBlocks I x fuel (S \ A)).map fun right => left ++ right

noncomputable def partitionOfBlocks {n : ℕ} (blocks : List (Finset (Fin n))) : Partition n :=
  fun v =>
    let C := (blocks.find? (fun C => decide (v ∈ C))).getD {v}
    if h : C.Nonempty then C.min' h else v

noncomputable def repair {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (D : Finset (Fin n)) : List (Finset (Fin n)) :=
  repulsionBlocks I x 1 (potentialOne I x) n D

noncomputable def internalCost {n : ℕ} (I : Instance n) (D : Finset (Fin n))
    (P : Partition n) : ℝ :=
  pairSum (fun u v => if u ∈ D ∧ v ∈ D then
    (if I.positive.Adj u v then (if P u = P v then 0 else 1)
      else if P u = P v then 1 else 0) else 0)

end ConstrainedCorrelationRepulsion.Main


