-- Prove2me | Definitions.Def_DetDLP_S8M_PacketCode
-- name    : DetDLP_S8M_PacketCode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T22:34:33.198604+00:00
-- url     : https://prove2.me/theorems/09ec31ab-cd7f-4863-aa41-220609a03e98

import Definitions.Def_DetDLP_S8M_Routes

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1200000

namespace DetDLP.S8M.MakePacket
open S8H0 S8H0.RegisterMap S8H0.NamedBlocks S8H.PointAddresses Groundwork
open S8H0.GateRoutes S8H0.HashRows
open DetDLP.S8M.Routes
open DetDLP.S8N.ECAddRoutes

variable {m d e : ℕ}

/-- A code together with its total register-name lookup. -/
abbrev NC := Code × (ℕ → ℕ)

def catN (a b : NC) : NC :=
  (sum a.1 b.1, fun i => if i < a.1.ne then a.2 i else b.2 (i-a.1.ne))

def Fits {k : ℕ} (c : NC) (b : B k) : Prop :=
  Models c.1 b.core.A ∧ ∀ i : Fin b.core.A.ne, c.2 i.val = (b.name i).val

/-- The canonical code/name view of a named block. -/
def codeOf {k : ℕ} (b : B k) : NC :=
  (⟨b.core.A.ng, b.core.A.nb, b.core.A.ne,
    fun i => if h : i < b.core.A.ne then (b.core.A.gate ⟨i,h⟩).val else 0,
    fun i => if h : i < b.core.A.ne then (b.core.A.bit ⟨i,h⟩).val else 0⟩,
   fun i => if h : i < b.core.A.ne then (b.name ⟨i,h⟩).val else 0)

theorem codeOf_spec {k : ℕ} (b : B k) : Fits (codeOf b) b := by
  refine ⟨?_, ?_⟩
  · refine ⟨rfl,rfl,rfl,?_,?_⟩ <;> intro i <;> simp [codeOf,i.isLt]
  · intro i
    simp [codeOf,i.isLt]

theorem cat_spec {k : ℕ} {a b : NC} {u v : B k}
    (h : Fits a u) (j : Fits b v) : Fits (catN a b) (joinB u v) := by
  refine ⟨sum_spec h.1 j.1, ?_⟩
  intro i
  induction i using Fin.addCases with
  | left i => simp [catN,joinB,h.1.ne,i.isLt,h.2]
  | right i => simp [catN,joinB,h.1.ne,j.2]

/-- Atom-slot code for one routed elliptic-curve seed query. -/
def atomN (hd : 1 ≤ d) (p T : ℕ) (c : Coeff) (S : SeedData m)
    (i : Fin (2*m)) : NC := codeOf (atomRows hd p T c S i)

/-- Conversion-map code for one routed short-Weierstrass conversion. -/
def mapN (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (i : Fin (2*m)) : NC :=
  codeOf (mapRows (m:=m) hd p b2 a1 a3 i)

/-- One addition tile in the accumulator chain. -/
def addStepN (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (flag0 : Ref (bank m d e)) (x0 y0 : Word (bank m d e))
    (flag1 : Ref (bank m d e)) (x1 y1 : Word (bank m d e))
    (path : Path (addShape d e) (bank m d e)) : NC :=
  codeOf (addBlock hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path)

/-- Code for the complete accumulator fold block. -/
def foldN (hd : 1 ≤ d) (hm : 1 ≤ m) (p neg1 three c4 : ℕ) (t : Target) : NC :=
  codeOf (foldRows hd hm p neg1 three c4 t)

/-- Code for the Tag 6 route network before the layout's external anchors. -/
def base (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : Coeff) (S : SeedData m)
    (b2 neg1 three c4 : ℕ) (η : List Bool) (t : Target) : NC :=
  codeOf (networkAt hd hm p T c S b2 neg1 three c4 η t)

theorem atomN_Fits (hd : 1 ≤ d) (p T : ℕ) (c : Coeff) (S : SeedData m)
    (i : Fin (2*m)) : Fits (atomN hd p T c S i) (atomRows hd p T c S i) := codeOf_spec _
theorem mapN_Fits (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (i : Fin (2*m)) :
    Fits (mapN hd p b2 a1 a3 i) (mapRows (m:=m) hd p b2 a1 a3 i) := codeOf_spec _
theorem addStepN_Fits (hd : 1 ≤ d) (p n three c4 : ℕ)
    (flag0 : Ref (bank m d e)) (x0 y0 : Word (bank m d e))
    (flag1 : Ref (bank m d e)) (x1 y1 : Word (bank m d e))
    (path : Path (addShape d e) (bank m d e)) :
    Fits (addStepN hd p n three c4 flag0 x0 y0 flag1 x1 y1 path)
      (addBlock hd p n three c4 flag0 x0 y0 flag1 x1 y1 path) := codeOf_spec _
theorem foldN_Fits (hd : 1 ≤ d) (hm : 1 ≤ m) (p n three c4 : ℕ) (t : Target) :
    Fits (foldN hd hm p n three c4 t) (foldRows hd hm p n three c4 t) := codeOf_spec _
theorem base_Fits (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : Coeff) (S : SeedData m)
    (b2 n three c4 : ℕ) (η : List Bool) (t : Target) :
    Fits (base hd hm p T c S b2 n three c4 η t)
      (networkAt hd hm p T c S b2 n three c4 η t) := codeOf_spec _

end DetDLP.S8M.MakePacket


