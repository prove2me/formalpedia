-- Prove2me | Definitions.Def_TraceAdopt_LPReform_BiLP10Graph
-- name    : TraceAdopt_LPReform_BiLP10Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:17.829023+00:00
-- url     : https://prove2.me/theorems/6a688457-074c-4b12-bc69-bd25395bc9e7
-- title:
--   Definition 4 for formulation (10) — its variables, constraint supports, and intersection graph
-- statement:
--   After substituting the bit expansions (10d) and (10h), formulation (10) is a binary linear program whose variables are the seed indicators $s_i$, the orientation variables $\ell_{pq}$ ($p,q\in N'$), and the bits $u^\tau_{iz},\tilde u^\tau_{iz}$ ($0\le\tau\le n_u$) and $v^\tau_{jz},\tilde v^\tau_{jz}$ ($0\le\tau\le n_v$). Each constraint of (10) involves the following variables:
--
--   1. (10a) at $(i,z)$, $i\in X'_z$: $\ell_{ji}$ for $j\in J^i_z$, and all bits $u^\tau_{iz}$;
--   2. (10b) at $(i,z)$, $z$ not the root of $T'_i$: the bits $u^\tau_{iz}$, $\tilde u^\tau_{iz}$, and $\tilde u^\tau_{iz'}$ for the children $z'$ of $z$ in $T'_i$; (10c) at the root: $u^\tau_{iz}$, $\tilde u^\tau_{iz'}$ for the children, and $s_i$;
--   3. (10e)–(10g) likewise for supply chains, without $s$;
--   4. (10i): $\ell_{pq},\ell_{qp}$; (10j): $\ell_{pq},\ell_{qx},\ell_{xp}$, for distinct vertices of a bag.
--
--   The **intersection graph** of (10) (Definition 4, p. 15) has a vertex for each variable and an edge between two distinct variables that occur in a common constraint.
--
--   **Formalization Note** The variable type also contains variables that (10) does not declare (for instance $\ell_{pq}$ for $p,q$ in no common bag); they occur in no constraint and are isolated vertices, which do not change treewidth. A variable counts as occurring in a constraint whenever its term is displayed, even if its coefficient $r_{ji}$ is $0$; this can only add edges, so a treewidth bound for this graph also bounds the graph of nonzero coefficients. The binary domain constraints involve one variable each and add no edges.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 15, Definition 4; pp. 39–40, formulation (10); p. 41, proof of Proposition 9

import Definitions.Def_TraceAdopt_LPReform_BiLP10
import Definitions.Def_TraceAdopt_LPReform_LinearSystem

namespace TraceAdopt.LPReform

/-- The variables of formulation (10) after substituting the bit expansions (10d)
and (10h): `s_i`, the orientation variables `ℓ_{pq}` (`p, q ∈ N′`), and the bits
`u^τ_{iz}, ũ^τ_{iz}` (`τ ≤ nu`) and `v^τ_{jz}, ṽ^τ_{jz}` (`τ ≤ nv`). Variables that
(10) does not declare (for instance `ℓ_{pq}` for `p, q` in no common bag) occur in no
constraint and are isolated vertices of the intersection graph. -/
inductive Var10 (I : Instance) (T : Type) : Type where
  | s : Fin I.n → Var10 I T
  | l : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → Var10 I T
  | u : Fin I.n → T → Fin (nu I + 1) → Var10 I T
  | ut : Fin I.n → T → Fin (nu I + 1) → Var10 I T
  | v : Fin I.m → T → Fin (nv I + 1) → Var10 I T
  | vt : Fin I.m → T → Fin (nv I + 1) → Var10 I T
  deriving DecidableEq

/-- Indices of the constraints of (10): `a i z` is (10a), `b i z` is (10b), or (10c)
when `z` is the root of `T′_i`; `e j z` is (10e), `f j z` is (10f), or (10g) at the
root of `T′_j`; `pair z p q` is (10i) and `triple z p q x` is (10j). -/
inductive Con10 (I : Instance) (T : Type) : Type where
  | a : Fin I.n → T → Con10 I T
  | b : Fin I.n → T → Con10 I T
  | e : Fin I.m → T → Con10 I T
  | f : Fin I.m → T → Con10 I T
  | pair : T → Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → Con10 I T
  | triple : T → Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → Con10 I T

open Classical in
/-- The variables occurring in each constraint of (10), exactly as written in
`BiLP10Feasible` (every displayed term, including terms whose coefficient `r_{ji}` may
vanish). A constraint index that (10) does not instantiate has empty support. -/
noncomputable def supp10 (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
    (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n)) :
    Con10 I T → Finset (Var10 I T)
  | .a i z =>
      if Sum.inl i ∈ X' z then
        (J i z).image (fun j => Var10.l (Sum.inr j) (Sum.inl i)) ∪
          Finset.univ.image (Var10.u i z)
      else ∅
  | .b i z =>
      if Sum.inl i ∈ X' z then
        Finset.univ.image (Var10.u i z) ∪
          ((children rt par z).filter (fun z' => Sum.inl i ∈ X' z')).biUnion
            (fun z' => Finset.univ.image (Var10.ut i z')) ∪
          (if IsSubtreeRoot I X' rt par (Sum.inl i) z then {Var10.s i}
            else Finset.univ.image (Var10.ut i z))
      else ∅
  | .e j z =>
      if Sum.inr j ∈ X' z then
        (Ip j z).image (fun i => Var10.l (Sum.inl i) (Sum.inr j)) ∪
          Finset.univ.image (Var10.v j z)
      else ∅
  | .f j z =>
      if Sum.inr j ∈ X' z then
        Finset.univ.image (Var10.v j z) ∪
          ((children rt par z).filter (fun z' => Sum.inr j ∈ X' z')).biUnion
            (fun z' => Finset.univ.image (Var10.vt j z')) ∪
          (if IsSubtreeRoot I X' rt par (Sum.inr j) z then ∅
            else Finset.univ.image (Var10.vt j z))
      else ∅
  | .pair z p q =>
      if p ∈ X' z ∧ q ∈ X' z ∧ p ≠ q then {Var10.l p q, Var10.l q p} else ∅
  | .triple z p q x =>
      if p ∈ X' z ∧ q ∈ X' z ∧ x ∈ X' z ∧ p ≠ q ∧ q ≠ x ∧ p ≠ x then
        {Var10.l p q, Var10.l q x, Var10.l x p}
      else ∅

/-- The intersection graph of (10) (Definition 4, p. 15). -/
noncomputable def intersectionGraph10 (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
    (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n)) :
    SimpleGraph (Var10 I T) :=
  intersectionGraph (supp10 I X' rt par J Ip)

end TraceAdopt.LPReform


