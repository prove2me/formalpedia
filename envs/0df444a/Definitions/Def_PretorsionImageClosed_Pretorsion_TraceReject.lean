-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
-- name    : PretorsionImageClosed_Pretorsion_TraceReject
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:26:35.336385+00:00
-- url     : https://prove2.me/theorems/139bee41-4534-4d6a-a73f-9114145a13bb
-- title:
--   Trace Reject
-- statement:
--   Definitions and structural lemmas for Trace Reject, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits ZeroObject
namespace Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (T F : Subcategory C) (X : C)
structure TraceRejectCondition : Prop where
  /-- `r(X) ⊆ t(X)`. -/
  reject_le_trace : F.reject X ≤ T.trace X
  /-- `r(t(X)) = r(X)`, as subobjects of `t(X)`. -/
  reject_trace : F.reject (T.trace X : C) =
    Subobject.mk (Subobject.ofLE (F.reject X) (T.trace X) reject_le_trace)
  /-- `t(X/r(X)) = t(X)/r(X)`, as subobjects of `X/r(X)`. -/
  trace_cokernel : T.trace (cokernel (F.reject X).arrow) =
    imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))
variable {T F X}
section Converse
variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed) (h : TraceRejectCondition T F X)
include hT hF h
end Converse
section Forward
variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
include hT hF
end Forward
section Reconstruction
variable (hP : IsPretorsionTheory T.prop F.prop)
include hP
end Reconstruction
end Statement
end PretorsionImageClosed


