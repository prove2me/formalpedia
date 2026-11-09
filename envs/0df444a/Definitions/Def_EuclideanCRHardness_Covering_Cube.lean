-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Cube
-- name    : EuclideanCRHardness_Covering_Cube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:40.908195+00:00
-- url     : https://prove2.me/theorems/688c8ad8-dfe5-401f-85eb-2f9e58f65e02
-- title:
--   Sixteen-edge cube gadget and shared-reference assembly
-- statement:
--   Index terminals in the order $000,011,101,110$. Their signs are $z,cx_1,x_2,x_3$. Auxiliary $j$ prefers equality with its opposite terminal $j$ and inequality with the other three terminals. A negative literal switches the four preferences incident to that terminal occurrence.
--
--   Each equation receives four fresh auxiliaries; one reference vertex is shared by all equations. The full graph is computed from the input list, with sixteen edge objects per equation. Repeated terminals are identified without identifying auxiliaries. The local gadget optimum fixes $z=+1$ and maximizes only over the four auxiliary signs.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), Lemma 3.4 and equation (3.3), printed p. 6 / PDF p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf Assembly identities in Proposition 3.1 proof, printed p. 7 / PDF p. 8.

import Definitions.Def_EuclideanCRHardness_Covering_Parity

namespace EuclideanCRHardness.Covering

/-- Terminal order: 000,011,101,110; auxiliary j is opposite terminal j. -/
def terminal (e : Equation) (k : Fin 4) : ℕ :=
  if k = 0 then 0 else if k = 1 then e.a+1 else if k = 2 then e.b+1 else e.d+1

def gadgetEdges (n row : ℕ) (e : Equation) : List SignedEdge :=
  (List.finRange 4).flatMap (fun j => (List.finRange 4).map (fun k =>
    ⟨terminal e k, n+1+4*row+j.val,
      if k = 1 ∧ e.rhs = false then !(j == k) else j == k⟩))

def cube (P : ParityInstance) : SignedInstance :=
  ⟨P.n+1+4*P.eqs.length,
    (P.eqs.zipIdx).flatMap (fun er => gadgetEdges P.n er.2 er.1)⟩

def gadgetValue (x : Fin 3 → Bool) (c : Bool) (y : Fin 4 → Bool) : ℕ :=
  let q : Fin 4 → Bool := ![true, if c then x 0 else !(x 0), x 1, x 2]
  (Finset.univ : Finset (Fin 4 × Fin 4)).sum (fun jk =>
    if ((y jk.1 == q jk.2) == (jk.1 == jk.2)) then 1 else 0)

def gadgetOpt (x : Fin 3 → Bool) (c : Bool) : ℕ := Finset.univ.sup (gadgetValue x c)

def cubeBits (bits : List Bool) : List Bool :=
  match decodeParity bits with
  | none => []
  | some P => encodeSigned (cube P)

end EuclideanCRHardness.Covering


