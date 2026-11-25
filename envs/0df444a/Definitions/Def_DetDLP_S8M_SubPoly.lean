-- Prove2me | Definitions.Def_DetDLP_S8M_SubPoly
-- name    : DetDLP_S8M_SubPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T23:51:42.756721+00:00
-- url     : https://prove2.me/theorems/882b1cc1-d00b-4887-bea2-c3b48def4685
-- title:
--   Tag 6 SubPoly models
-- statement:
--   Efficient compositional proofs for the Tag 6 routed elliptic-curve packet blocks.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_FoldModel

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.SubPoly

open Groundwork S8H0.RegisterMap S8H0.NamedBlocks S8H.PointAddresses
open S8H0.GateRoutes (Coeff Path)
open DetDLP.S8M.Routes DetDLP.S8M.MakePacket

/-- A code and its total address function are efficient when each dimension,
indexed gate lookup, and indexed address lookup is polynomial-time computable. -/
def Eff {α : Type} [Enc α] (F : α → NC) : Prop :=
  PolyT (fun x => (F x).1.ng) ∧ PolyT (fun x => (F x).1.ne) ∧
    ∀ {I : α → ℕ}, PolyT I →
      PolyT (fun x => (F x).1.gate (I x)) ∧ PolyT (fun x => (F x).2 (I x))

/-- Concatenation preserves polynomial-time code and address lookup. -/
theorem catP {α : Type} [Enc α] {A B : α → NC}
    (ha : Eff A) (hb : Eff B) : Eff (fun x => catN (A x) (B x)) := by
  refine ⟨PolyT.add ha.1 hb.1, PolyT.add ha.2.1 hb.2.1, fun h => ?_⟩
  have j := hb.2.2 (PolyT.sub h ha.2.1)
  have i := ha.2.2 h
  have k := PolyT.decide_lt h ha.2.1
  exact ⟨P2M_Groundwork_PolyT_ite__226169acf219 k i.1
      (PolyT.add ha.1 j.1),
    P2M_Groundwork_PolyT_ite__226169acf219 k i.2 j.2⟩

/-- Repeating a fixed code stores the block and local-address indices as the
quotient and remainder of the global edge number. -/
def repeatN (n : ℕ) (c : Code) (f : ℕ → ℕ → ℕ) : NC :=
  (⟨n*c.ng, n*c.nb, n*c.ne,
      fun i => i/c.ne*c.ng+c.gate (i%c.ne),
      fun i => i/c.ne*c.nb+c.bit (i%c.ne)⟩,
    fun i => f (i/c.ne) (i%c.ne))

theorem repeatP {α : Type} [Enc α] {n : α → ℕ} {c : α → Code}
    {f : α → ℕ → ℕ → ℕ}
    (hn : PolyT n) (hng : PolyT fun x => (c x).ng)
    (hne : PolyT fun x => (c x).ne)
    (hgate : ∀ {I : α → ℕ}, PolyT I →
      PolyT (fun x => (c x).gate (I x)))
    (hbit : ∀ {I : α → ℕ}, PolyT I →
      PolyT (fun x => (c x).bit (I x)))
    (hf : ∀ {I J : α → ℕ}, PolyT I → PolyT J →
      PolyT (fun x => f x (I x) (J x))) :
    Eff (fun x => repeatN (n x) (c x) (fun i j => f x i j)) := by
  refine ⟨PolyT.mul hn hng, PolyT.mul hn hne, fun hi => ?_⟩
  have q := PolyT.div hi hne
  have r := PolyT.mod hi hne
  exact ⟨PolyT.add (PolyT.mul q hng) (hgate r), hf q r⟩

/-- Compose efficient models for the atom bank, map bank, fold, and prefix
into an efficient four-block code/name model. -/
theorem baseP {α : Type} [Enc α] {A M F P : α → NC}
    (ha : Eff A) (hm : Eff M) (hf : Eff F) (hp : Eff P) :
    Eff (fun x => catN (A x) (catN (M x) (catN (F x) (P x)))) := by
  exact catP ha (catP hm (catP hf hp))

/-- Exact atom fits are inherited from the abstract register-offset proofs. -/
theorem atom_spec {m d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (S : SeedData m) (i : Fin (2*m)) :
    Fits (atomN hd p T c S i) (atomRows hd p T c S i) :=
  AtomMapModel.atom_spec hd p T c S i

/-- Exact conversion-map fits are inherited from the abstract register-offset proofs. -/
theorem map_spec {m d : ℕ} (hd : 1 ≤ d) (p b2 a1 a3 : ℕ)
    (i : Fin (2*m)) :
    Fits (mapN (m := m) hd p b2 a1 a3 i)
      (mapRows (m := m) hd p b2 a1 a3 i) :=
  AtomMapModel.map_spec hd p b2 a1 a3 i

/-- Each short-Weierstrass addition step fits its routed block. -/
theorem step_spec {m d e : ℕ} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (flag0 : Ref (Routes.bank m d e)) (x0 y0 : S8H0.HashRows.Word (Routes.bank m d e))
    (flag1 : Ref (Routes.bank m d e)) (x1 y1 : S8H0.HashRows.Word (Routes.bank m d e))
    (path : Path (DetDLP.S8N.ECAddRoutes.addShape d e) (Routes.bank m d e)) :
    Fits (addStepN hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path)
      (DetDLP.S8N.ECAddRoutes.addBlock hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path) :=
  FoldModel.step_spec hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path

/-- The routed accumulator includes all `2*m-1` short-Weierstrass additions. -/
theorem fold_spec {m d e : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (p neg1 three c4 : ℕ) (t : Routes.Target) :
    Fits (foldN hd hm p neg1 three c4 t) (foldRows hd hm p neg1 three c4 t) :=
  FoldModel.fold_spec hd hm p neg1 three c4 t

/-- The public prefix rows are represented by their canonical code and names. -/
theorem prefix_spec {m d e : ℕ} (b : ℕ) (η : List Bool) :
    Fits (codeOf (Routes.prefixRows (m := m) (d := d) (e := e) b η))
      (Routes.prefixRows (m := m) (d := d) (e := e) b η) :=
  FoldModel.prefix_spec b η

end DetDLP.S8M.SubPoly


