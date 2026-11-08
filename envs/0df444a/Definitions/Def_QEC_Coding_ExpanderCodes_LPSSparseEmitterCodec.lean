-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
-- name    : QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:32:13.179828+00:00
-- url     : https://prove2.me/theorems/4485f73a-69f3-4d05-9bde-18591e237402
-- title:
--   LPSSparse Emitter Codec
-- statement:
--   Definitions and structural lemmas for LPSSparse Emitter Codec, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
abbrev Row:=List (ℕ×ℕ)
def entryFields (r:Row):List ℕ:=r.flatMap (fun e=>[e.2,e.1])
def rowFields (rs:List Row):List ℕ:=rs.flatMap (fun r=>r.length::entryFields r)
def decodeEntries:ℕ→List ℕ→Option (Row×List ℕ)
 | 0,xs=>some ([],xs)
 | n+1,k::p::xs=>(decodeEntries n xs).map (fun rs=>((p,k)::rs.1,rs.2))
 | _+1,_=>none
def decodeRows:ℕ→List ℕ→Option (List Row×List ℕ)
 | 0,xs=>some ([],xs)
 | n+1,k::xs=>(decodeEntries k xs).bind (fun r=>(decodeRows n r.2).map (fun rs=>(r.1::rs.1,rs.2)))
 | _+1,[]=>none
def fields (rs:List Row):List ℕ:=rs.length::rowFields rs.reverse
def decodeFields:List ℕ→Option (List Row)
 | []=>none
 | n::xs=>(decodeRows n xs).bind (fun rs=>if rs.2=[] then some rs.1.reverse else none)
def encode (rs:List Row):List Bool:=stream (fields rs)
example:decodeFields (fields [[],[(0,0),(0,0)],[]])=some [[],[(0,0),(0,0)],[]]:=by decide
example:fields [[],[(0,0)],[]]≠fields [[(0,0)],[],[]]:=by decide
example:decodeFields [1,2,0,0]=none:=by decide
example:decodeFields [1,0,0]=none:=by decide
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection
def parseFields:ℕ→List Bool→Option (List ℕ)
 | n,[]=>if n=0 then some [] else none
 | n,true::xs=>parseFields (n+1) xs
 | n,false::xs=>(parseFields 0 xs).map (n::·)
def decode (w:List Bool):Option (List Row):=(parseFields 0 w).bind decodeFields
def typedEntry (n s:ℕ) (e:ℕ×ℕ):Option (Fin n×Fin s):=
 if hp:e.1 < n then if hk:e.2 < s then some (⟨e.1,hp⟩,⟨e.2,hk⟩) else none else none
def typedRow (n s:ℕ):Row→Option (List (Fin n×Fin s))
 | []=>some []
 | e::es=>(typedEntry n s e).bind (fun e'=>(typedRow n s es).map (e'::·))
def typedRows (n s:ℕ):List Row→Option (List (List (Fin n×Fin s)))
 | []=>some []
 | r::rs=>(typedRow n s r).bind (fun r'=>(typedRows n s rs).map (r'::·))
def numeric (n s:ℕ) (rs:List (List (Fin n×Fin s))):List Row:=
 rs.map (fun r=>r.map (fun e=>(e.1.val,e.2.val)))
def decodeTyped (n s:ℕ) (w:List Bool):Option (List (List (Fin n×Fin s))):=
 (decode w).bind (typedRows n s)
example:decode [true]=none:=by decide +kernel
example:decode (encode [[],[(0,0),(0,0)],[(7,4)]])=some [[],[(0,0),(0,0)],[(7,4)]]:=by decide +kernel
example:decodeTyped 1 1 (encode [[(1,0)]])=none:=by decide +kernel
example:decodeTyped 1 1 (encode [[(0,1)]])=none:=by decide +kernel
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
def rowsOrEmpty (n s:ℕ) (w:List Bool):List (List (Fin n×Fin s)):=
 (decodeTyped n s w).getD []
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec


