-- Prove2me | Definitions.Def_DetDLP_M3D_OrderEntry
-- name    : DetDLP_M3D_OrderEntry
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:06:16.605542+00:00
-- url     : https://prove2.me/theorems/42464eb4-9a5a-40eb-9aa3-f325109d85ac
-- title:
--   M3D elliptic order-query entry
-- statement:
--   Polynomial-time order-query construction and correctness for elliptic-curve Stage II dispatch.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M89_S1_Queries
import Definitions.Def_DetDLP_W3C_NewtonPoly

set_option autoImplicit false
namespace DetDLP
open Groundwork OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

attribute [local fun_prop] PolyT.comp PolyT.const PolyT.id' PolyT.fst PolyT.snd
  w5_M6Sort.decode_poly w5_M6Sort.encode_poly DetDLP_W1_Queries.frame_poly
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86

/-- Six leading fields are the curve. The point coordinates must not be sent to tag zero. -/
def DetDLP_M3D_curve (w : List Bool) := encodeNatListBin ((w5_M6Sort.decode w).take 6)

def DetDLP_M3D_orderQuery (w : List Bool) := M89S1.queryWord 0 (DetDLP_M3D_curve w) []

def DetDLP_M3D_scalar (w : List Bool) := (w5_M6Sort.decode w).getD 0 0

/-- First argument is the original input, second is the word returned by tag zero. -/
def DetDLP_M3D_dispatch (input answer : List Bool) :=
  W3C.NewtonPoly.largeCheck (DetDLP_M3D_scalar input) (DetDLP_M3D_scalar answer)

@[local fun_prop] theorem m3d_curve_poly : PolyT DetDLP_M3D_curve := by
  unfold DetDLP_M3D_curve; fun_prop

theorem m3d_orderQuery_poly : PolyT DetDLP_M3D_orderQuery := by
  change PolyT (fun w => M89S1.queryWord 0 (DetDLP_M3D_curve w) [])
  simp only [M89S1.queryWord, Encoding.encodeList, id_eq,
    ← DetDLP_W1_Queries.frame_correct]; fun_prop

@[local fun_prop] theorem m3d_scalar_poly : PolyT DetDLP_M3D_scalar := by
  unfold DetDLP_M3D_scalar; fun_prop

theorem m3d_dispatch_poly : PolyT (fun z : List Bool × List Bool => DetDLP_M3D_dispatch z.1 z.2) := by
  unfold DetDLP_M3D_dispatch; apply W3C.NewtonPoly.largeCheck_poly <;> apply PolyT.comp m3d_scalar_poly <;> fun_prop

section Correctness
variable {p : ℕ} [NeZero p] (E : WeierstrassCurve (ZMod p)) (P Q : E.toAffine.Point)

@[simp] theorem m3d_curve_eq : DetDLP_M3D_curve (encodeECDLPInput p E P Q) = encodeCurveInput p E := by
  simp [DetDLP_M3D_curve, encodeECDLPInput, encodeCurveInput]

@[simp] theorem m3d_orderQuery_eq : DetDLP_M3D_orderQuery (encodeECDLPInput p E P Q) =
    M89S1.queryWord 0 (encodeCurveInput p E) [] := by simp [DetDLP_M3D_orderQuery]

@[simp] theorem m3d_dispatch_true (M : ℕ) :
    DetDLP_M3D_dispatch (encodeECDLPInput p E P Q) (encodeNatListBin [M]) = true ↔ w3_large p M := by
  simpa [DetDLP_M3D_dispatch, DetDLP_M3D_scalar, encodeECDLPInput] using
    W3C.NewtonPoly.largeCheck_correct p M

theorem m3d_dispatch_false (M : ℕ) :
    DetDLP_M3D_dispatch (encodeECDLPInput p E P Q) (encodeNatListBin [M]) = false ↔ ¬ w3_large p M := by
  rw [← m3d_dispatch_true E P Q]; cases DetDLP_M3D_dispatch _ _ <;> decide
end Correctness

/-- The same oracle machine answers every canonical order request, independently of P and Q. -/
theorem m3d_order_call (hord : M89S1.CountOracle) :
    ∃ (ord : PrimitiveMachine) (out : Fin ord.tapeCount) (K : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
        (P Q : E.toAffine.Point),
        RunsWithin ord out (DetDLP_M3D_orderQuery (encodeECDLPInput p E P Q))
          (encodeNatListBin [@Fintype.card _ (ecPointFintype E)])
          (mainSpaceBound K (bitLen p)) (polyBound K (bitLen p)) := by
  obtain ⟨ord,out,K,run⟩ := hord
  refine ⟨ord,out,K,?_⟩
  intro p hp h3 E hE P Q
  rw [m3d_orderQuery_eq]
  exact run _ _ _ (.ecOrder p h3 E)

end DetDLP


