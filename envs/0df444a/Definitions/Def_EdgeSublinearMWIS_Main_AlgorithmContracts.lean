-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts
-- name    : EdgeSublinearMWIS_Main_AlgorithmContracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:44:15.002914+00:00
-- url     : https://prove2.me/theorems/c0b20499-4749-46b7-b93f-1abd5adeb0a9
-- title:
--   Primitive obligations, the full Solve invariant and dyadic accuracy
-- statement:
--   The separator contract states actual halting with a light balanced separator, under exactly the light-separator cost hypotheses. The feasibility contract and a bound on the encoded cuts remain obligations as well. They are propositions asserted by theorem conclusions, never fields in the raw implementation record.
--
--   The full operational invariant is
--   $$I_G\text{ independent},\qquad\alpha(G)\le u_G\le |V(G)|,\qquad |I_G|\ge(1-\delta)^{h(|V(G)|)}u_G.$$
--   Termination is expressed by existence of a finite derivation of the operational execution relation; the invariant is required of every result. The accuracy routine chooses the least dyadic denominator with $\varepsilon/2<\varepsilon'\le\varepsilon$ on the guarded domain. Its implementation and preprocessing cost are asserted in the runtime target. No logarithm at zero or division by zero is used in an active algorithm branch.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §5.1–§5.3, Eqs. (22)–(26), p.18 (PDF p.18), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Ellipsoid
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

noncomputable def energyOn {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  edgeEnergy G (fun v => if v ∈ W then x v else 0)

/-- A specification whose truth is a theorem conclusion; raw Routines has no such field.
The active set W is an induced input with original labels, not a stronger graph promise. -/
def SeparatorContract (C : GraphClass) (a B : ℕ) (P : Program) (time : Polynomial ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (x : Fin n → ℚ) (δ : ℚ),
    C n G → 2 ≤ W.card → 0 < δ → δ < 1 →
    (∀ v ∈ W, 0 ≤ x v ∧ x v ≤ 1) →
    (threshold B a W.card δ : ℝ) ≤ vertexSum (fun v => (x v : ℝ)) W →
    energyOn G W (fun v => (x v : ℝ)) ≤
      (vertexSum (fun v => (x v : ℝ)) W) ^ 2 / threshold B a W.card δ →
    ∃ (S : Finset (Fin n)) (t : ℕ),
      Runs P (separatorInput G W δ x) (mask S) t ∧
      t ≤ time.eval ((separatorInput G W δ x).length + 1) ∧
      Light G W S δ (fun v => (x v : ℝ))

/-- Primitive implementation properties are obligations, not assumptions on any source item.
The ellipsoid part applies to every 0–1 hull, including empty hulls and affine subspaces. -/
def PrimitiveContract (C : GraphClass) (a B : ℕ) (M : Routines) : Prop :=
  (∃ time : Polynomial ℕ, SeparatorContract C a B M.separator time) ∧
  ∃ queries work coordinates : Polynomial ℕ,
    ExactEllipsoid M.ellipsoid M.descriptionBound queries work coordinates ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (P : Parameters) (k : ℕ)
      (y : Finset (Fin n) → ℚ) (c : Cut n),
      C n G → 1 ≤ P.r → k ≤ W.card →
      Execute G P M (.round W k y) (.inequality c) →
      (encodeCut W P.r c).length ≤ M.descriptionBound.eval ((Coordinates W P.r).card + 1)

/-- Non-computability of a specification is not algorithm semantics: Solve means Execute.
This predicate only abbreviates the full invariant to be *proved*, with existence explicit. -/
def SolveInvariant (C : GraphClass) (a B : ℕ) (M : Routines) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℚ) (W : Finset (Fin n)),
    C n G → 0 < ε → ε < 1 →
    (∃ (I : Finset (Fin n)) (u : ℕ), Execute G (parameters B a n ε) M (.solve W) (.solved I u)) ∧
    ∀ (I : Finset (Fin n)) (u : ℕ),
      Execute G (parameters B a n ε) M (.solve W) (.solved I u) →
      I ⊆ W ∧ G.IsIndepSet (I : Set (Fin n)) ∧
        alpha G W ≤ u ∧ u ≤ W.card ∧
        (1 - ((parameters B a n ε).delta : ℝ)) ^ height W.card * u ≤ (I.card : ℝ)

/-- Minimal dyadic denominator test. Arbitrary rational encodings are read and
normalized before this value is used; that work is separately charged. -/
def roundedAccuracy (ε : ℚ) : ℚ :=
  let b := Nat.log 2 ε.den + 2
  let j := ((List.range (b + 1)).find?
    (fun j => decide ((ε.den : ℤ) ≤ ε.num * (2 : ℤ) ^ j))).getD b
  1 / (2 : ℚ) ^ j

noncomputable def unweightedInput {n : ℕ} (G : SimpleGraph (Fin n)) (ε : RationalCode) : List Bool :=
  graphBits G ++ ε.bits

end EdgeSublinearMWIS.Main


