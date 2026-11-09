-- Prove2me | Definitions.Def_BinaryThreeLCC_Main_Kikuchi
-- name    : BinaryThreeLCC_Main_Kikuchi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:01.057012+00:00
-- url     : https://prove2.me/theorems/4560be4c-c4de-46eb-8a26-c5ea765e6a67
-- title:
--   Ordered chain Kikuchi graph, vector labels and product averages
-- statement:
--   For a tuple system and a palette $\mathcal C\subseteq\Omega$, an $r$-chain chooses states $u_0,\ldots,u_r$ and an actual tuple copy $(u_{j-1},a_j,b_j,u_j)$ at every step, with $u_0\in\mathcal C$. Its graph edge has colour $u_0$, left endpoint $(\vec a,u_r)$ and right endpoint $\vec b$. The vertex sets are the tagged disjoint union
--
--   $$V_L=\Lambda^r\times\Omega,\qquad V_R=\Lambda^r.$$
--
--   All coordinates are ordered and may repeat; every chain copy gives its own edge. The left label is $v_u+\sum_jw_{a_j}$ and the right label is $\sum_jw_{b_j}$. The head is excluded from the chain output label. The associated product-difference average chooses both colours and every coordinate independently and uniformly. This implements Definition 5.1 rather than its set-based proof-overview analogue.
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Definition 5.1, printed p.13, PDF p.15; Observation 5.2 and Equation (2), printed p.14, PDF p.16; Claim 5.6, printed p.15, PDF p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_TupleSystem
import Definitions.Def_BinaryThreeLCC_Main_Spectral

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- States include the head and tail. Each step chooses an actual tuple copy. -/
def Chain {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) (C : Finset Ω) (r : ℕ) : Type :=
  {p : (Fin (r + 1) → Ω) × (Fin r → TupleCopy H) //
    p.1 0 ∈ C ∧ ∀ j : Fin r,
      (tupleAt H (p.2 j)).1 = p.1 j.castSucc ∧
      (tupleAt H (p.2 j)).2.2.2 = p.1 j.succ}

noncomputable instance chainFintype {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) (C : Finset Ω) (r : ℕ) : Fintype (Chain H C r) := by
  classical
  unfold Chain
  infer_instance

noncomputable def chainHead {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    {H : TupleSystem Ω Λ} {C : Finset Ω} {r : ℕ} (e : Chain H C r) : C :=
  ⟨e.val.1 0, e.property.1⟩

noncomputable def chainLeft {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    {H : TupleSystem Ω Λ} {C : Finset Ω} {r : ℕ} (e : Chain H C r) : (Fin r → Λ) × Ω :=
  (fun j => (tupleAt H (e.val.2 j)).2.1, e.val.1 (Fin.last r))

noncomputable def chainRight {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    {H : TupleSystem Ω Λ} {C : Finset Ω} {r : ℕ} (e : Chain H C r) : Fin r → Λ :=
  fun j => (tupleAt H (e.val.2 j)).2.2.1

/-- The vertex union is tagged, even if the original coordinate types overlap. -/
noncomputable def kikuchiGraph {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) (C : Finset Ω) (r : ℕ) :
    ColouredGraph (((Fin r → Λ) × Ω) ⊕ (Fin r → Λ)) (Chain H C r) C where
  graph := { src := fun e => Sum.inl (chainLeft e), tgt := fun e => Sum.inr (chainRight e) }
  colour := chainHead

noncomputable def leftVector {Ω Λ : Type} {W : Type*} [AddCommGroup W] [Module Bit W]
    {r : ℕ} (v : Ω → W) (w : Λ → W) (p : (Fin r → Λ) × Ω) : W :=
  v p.2 + ∑ j, w (p.1 j)

noncomputable def rightVector {Λ : Type} {W : Type*} [AddCommGroup W] [Module Bit W]
    {r : ℕ} (w : Λ → W) (b : Fin r → Λ) : W := ∑ j, w (b j)

noncomputable def productDifferenceAverage {Ω Λ : Type} [Fintype Ω] [DecidableEq Ω]
    [Fintype Λ] (H : TupleSystem Ω Λ) (C : Finset Ω) (r : ℕ) : ℝ :=
  average (fun i : C => average (fun j : C => average (fun a : Fin r → Λ =>
    squaredNorm ((matrixProduct (fun t => transitionM H (a t))).mulVec
      (unitVector i.val - unitVector j.val)))))

end BinaryThreeLCC.Main


