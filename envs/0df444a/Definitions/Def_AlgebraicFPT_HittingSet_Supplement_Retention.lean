-- Prove2me | Definitions.Def_AlgebraicFPT_HittingSet_Supplement_Retention
-- name    : AlgebraicFPT_HittingSet_Supplement_Retention
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:42:22.801227+00:00
-- url     : https://prove2.me/theorems/f3b55466-8037-4801-ba3b-585bc91631bf
-- title:
--   Computable representative selection and initialized legal path maintenance
-- statement:
--   Given an explicit finite family $A$ of ordered vertex lists, first retain the lexicographically least witness for each support present in $A$. A finite branching routine with budget $q$ then returns the empty family if its candidates are empty; otherwise it keeps the least remaining witness $P$. When $q>0$, it also takes the union of the outputs at budget $q-1$ on candidates avoiding $x$, for each $x\in V(P)$. Finite unions remove repeated witnesses. This defines $\operatorname{select}(q,A)$ with no assumptions about its correctness or size.
--
--   For a family $F_w$ at each endpoint $w$, define exactly the legal candidates ending at $v$:
--
--   $$C(F,v)=\bigcup_{w:\,wv\in E(G)}\{P\cdot v:P\in F_w,\ v\notin V(P)\}.$$
--
--   For a fixed root $s$ and target size $k$, initialize $R_{1,s,s}=\{(s)\}$ and $R_{1,s,v}=\varnothing$ for $v\ne s$. At every $h\ge2$ set
--
--   $$R_{h,s,v}=\operatorname{select}\bigl(k-h,C(R_{h-1,s,\cdot},v)\bigr).$$
--
--   The definitions implement representative selection and the maintenance procedure of Section 5.2 and Appendix D. Their size and preservation guarantees remain theorem conclusions.
--
--   **Formalization Note** The routine is a terminating computable function using the finite vertex order, without classical choice of a correct subfamily. Round zero is empty; values beyond $h=k$ are defined but unused. Theorems quantify only over $1\le h\le k$, so their natural subtraction $k-h$ agrees with ordinary subtraction.
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), pp.11–12, Section 5.2; pp.20–21, Appendix D

import Definitions.Def_AlgebraicFPT_HittingSet_Supplement_Paths

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet.Supplement

/-! A concrete finite representative-selection routine for Appendix D.
Lexicographic order resolves all choices. These are executable definitions; correctness,
the size bound and representativity are conclusions of the theorem items, not inputs. -/

/-- Keep the lexicographically first ordered witness for each support present in A. -/
def canonicalWitnesses {n : ℕ} (A : Finset (List (Fin n))) : Finset (List (Fin n)) :=
  A.filter (fun P => ∀ P' ∈ A, support P' = support P → P ≤ P')

/-- A depth-q branching tree: retain a witness, then branch on avoiding each of its vertices.
The budget strictly decreases. Finset union removes repeated witnesses across branches. -/
def retainTree {n : ℕ} : ℕ → Finset (List (Fin n)) → Finset (List (Fin n))
  | 0, A => if ha : A.Nonempty then {A.min' ha} else ∅
  | q + 1, A =>
      if ha : A.Nonempty then
        let P := A.min' ha
        {P} ∪ (support P).biUnion
          (fun x => retainTree q (A.filter (fun P' => x ∉ support P')))
      else ∅

/-- Select supports constructively, keeping one original ordered witness per chosen support. -/
def selectPaths {n : ℕ} (q : ℕ) (A : Finset (List (Fin n))) : Finset (List (Fin n)) :=
  retainTree q (canonicalWitnesses A)

/-- Exactly the legal candidates C_{h,s,v}: extend retained paths ending at a neighbor of v,
and never append a vertex already used. The argument F is the preceding round. -/
def extensions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : Fin n → Finset (List (Fin n))) (v : Fin n) : Finset (List (Fin n)) :=
  Finset.univ.biUnion (fun w => if G.Adj w v then
    ((F w).filter (fun P => v ∉ support P)).image (fun P => P ++ [v]) else ∅)

/-- The simultaneous initialized extension-and-retention construction for one fixed root.
Round zero is empty. Round one is the singleton root path at its own endpoint only.
For h ≥ 2 the query budget is k-h. Values after round k are unused by the theorems. -/
def maintained {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (s : Fin n) :
    ℕ → Fin n → Finset (List (Fin n))
  | 0 => fun _ => ∅
  | 1 => fun v => if v = s then {[s]} else ∅
  | h + 2 => fun v =>
      selectPaths (k - (h + 2)) (extensions G (maintained G k s (h + 1)) v)

end AlgebraicFPT.HittingSet.Supplement


