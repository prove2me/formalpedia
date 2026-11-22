-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_PaddedFrame
-- name    : CatalyticTreeEval_Main_PaddedFrame
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T23:21:15.968892+00:00
-- url     : https://prove2.me/theorems/333f8151-2a71-4045-a333-c350c83cdd06
-- title:
--   Zero-padded matching frames and the one-level implementation interface
-- statement:
--   For a frame $F$ over $\\mathbb Z/m\\mathbb Z$, let $D=\\max(d,\\lceil\\ell/\\lfloor\\log_2m\\rfloor\\rceil)$. The padded frame has exactly the same modulus, labels, decoder and access-space parameter, while every matching vector is extended from $\\mathbb Z_m^d$ to $\\mathbb Z_m^D$ by zero coordinates. This is the padding step used in §4.3 before packed-label readout.
--
--   The definition also packages the precise uniform conclusion of the one-level theorem as `OneLevelImplementation`. For every auxiliary output family with a space-bounded printer it requests one oracle machine and uniform positive constants, with the exact net register update, inverse-update pairing, $4k+4$ query count, local/retained space bounds and polynomial time bound. Supplying this interface separately for $U$, $V$ and the packed readout family is the interface consumed by the recursive construction.
--
--   **Formalization Note.** Vector extension is literal coordinatewise zero extension. The one-level proposition retains `MV` and `MD` in its signature so that it has the same uniform parameter interface as Theorem 4.4, although they occur only in the surrounding frame/access hypotheses.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Theorem 4.4, printed p.22 (PDF p.24), and §4.3 zero-padding/readout paragraphs, printed pp.25–26 (PDF pp.27–28); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Readout

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Extend a vector by zero coordinates, as in the padding step of §4.3. -/
def zeroExtendVec {m d D : ℕ} (v : Vec m d) : Vec m D :=
  fun i => if h : i.val < d then v ⟨i.val, h⟩ else 0

/-- The matching-vector frame after padding every vector to the readout dimension. -/
def paddedFrame (F : Frame) : Frame where
  m := F.m
  d := paddedDimension F
  l := F.l
  k := F.k
  s := F.s
  S := F.S
  U := fun y => zeroExtendVec (F.U y)
  V := fun y => zeroExtendVec (F.V y)
  D := F.D

/-- The complete output-contract interface supplied independently to each of the
three output families in the recursive proof of Theorem 4.1. -/
def OneLevelImplementation (F : List Bool → Frame) (domain : Set (List Bool))
    (MV MD : Machine) (A : ℕ) : Prop :=
  ∀ (W : (a : List Bool) → Label (F a).l → Vec (F a).m (F a).d) (MW : Machine),
    (∀ a ∈ domain, OutputAccess (F a) (W a) a MW A) →
    ∃ (P : OracleMachine) (Cs Cr Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cr ∧ 0 < Ct ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ (f : Label (F a).l → Label (F a).l → Label (F a).l)
        (x : Fin 2 → Label (F a).l) (α : ZMod (F a).m) (R : Registers (F a).m (F a).d),
        let ops := oneLevelProgram (F a).U (F a).V (W a) (F a).D f x α R
        execute (F a).U (F a).V x R ops = addAt R 2 (α • W a (f (x 0) (x 1))) ∧
        InversePairs ops ∧
        (ops.filter (fun op => match op with | .query _ _ _ => true | _ => false)).length =
          4 * (F a).k + 4 ∧
        OracleExecution P (F a).U (F a).V x (oneLevelInput (F a) a f) α R ops
          (Cs * ((F a).l + (F a).s + lg (F a).k))
          (Cr * (lg (F a).k + log₂ (F a).m))
          (some (Ct * ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q))
          none

end CatalyticTreeEval.Main


