-- Prove2me | Definitions.Def_DecDynMatch_Supplement_collectionFeedback
-- name    : DecDynMatch_Supplement_collectionFeedback
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:26:53.140106+00:00
-- url     : https://prove2.me/theorems/99336dd6-31d1-4600-8c9f-68d20bc53b4a
-- title:
--   CollectionFeedback$(v,o)$ of SC-PC (Algorithm 5)
-- statement:
--   After proposing to arm $v$ with outcome $o\in\{A,R\}$ in Seek or Root:
--
--   1. if $v=$ BUS: on $A$, $x\leftarrow\max\{x,0\}+1$; on $R$, $x\leftarrow\min\{x,0\}-1$;
--   2. in Seek: if $x\le-3$ then $c\leftarrow a+J_L+\chi_L+3$; if $a\ge b$, $x<0$ and $\min\{-x,a-b+1\}\ge K$ then armed $\leftarrow$ true; if $a\ge b+2$ and $x\ge3$ then $\nu\leftarrow$ Work if armed, else $\nu\leftarrow$ Root; return;
--   3. in Root: if $v=$ BUS and $x=-K$ then $\nu\leftarrow\textsc{Seek}_{\rm armed}$; return;
--   4. stage Clear: if $a+1\ge c$ then $\nu\leftarrow$ Scan;
--   5. stage Scan: if $v=$ BUS then busNext $\leftarrow$ false; otherwise busNext $\leftarrow$ true and, on $A$, $\nu\leftarrow$ Commit if $j=K-1$, else $j\leftarrow j+1$;
--   6. stage Commit: if $a+1\ge v_C+M_L$ and $x\ge R_{c,L}$ then $\nu\leftarrow$ Work.
--
--   **Formalization Note** $x$ is an integer and the comparisons with $a,b$ are in $\mathbb Z$; outcomes are booleans (true $=A$).
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithm 5, p.33

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_stateUpdate

namespace DecDynMatch.Supplement

open DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **CollectionFeedback(v, o)** of SC-PC (Seek and Root). J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), Algorithm 5, p.33, verbatim
control flow (`o = true` is A, `o = false` is R):
1. if `v = BUS`: on A `x ← max{x, 0} + 1`, on R `x ← min{x, 0} − 1`;
2. if `m = Seek`: if `x ≤ −3` then `c ← a + J_L + χ_L + 3`; if `a ≥ b`, `x < 0` and
   `min{−x, a − b + 1} ≥ K` then `armed ← true`; if `a ≥ b + 2` and `x ≥ 3` then `ν ← Work` if
   armed, else `ν ← Root`; return;
3. (Root) if `v = BUS` and `x = −K` then `ν ← Seek_armed`; return;
4. if `s = Clear`: if `a + 1 ≥ c` then `ν ← Scan`;
5. else if `s = Scan`: if `v = BUS` then `busNext ← false`; else `busNext ← true` and, on A,
   `ν ← Commit` if `j = K − 1`, else `j ← j + 1`;
6. else (`s = Commit`) if `a + 1 ≥ v_C + M_L` and `x ≥ R_{c,L}` then `ν ← Work`.

**Formalization Note.** `x` is an integer; the comparisons with `a, b` are made in `ℤ`. The
function is called only in Seek and Root; every mode other than Seek follows the Root branch. -/
def collectionFeedback (I : Instance K ι) (v : Fin K) (o : Bool) (st : PState K) : PState K :=
  let st1 : PState K :=
    if v = bus I then
      (if o = true then { st with x := max st.x 0 + 1 } else { st with x := min st.x 0 - 1 })
    else st
  match st1.m with
  | .seek =>
      let st2 : PState K :=
        if st1.x ≤ -3 then { st1 with c := st1.a + JL K + chiL K + 3 } else st1
      let st3 : PState K :=
        if st2.bq ≤ st2.a ∧ st2.x < 0 ∧ (K : ℤ) ≤ min (-st2.x) ((st2.a : ℤ) - st2.bq + 1) then
          { st2 with armed := true }
        else st2
      if st3.bq + 2 ≤ st3.a ∧ 3 ≤ st3.x then
        (if st3.armed = true then { st3 with ν := some .work } else { st3 with ν := some .root })
      else st3
  | _ =>
      if v = bus I ∧ st1.x = -(K : ℤ) then { st1 with ν := some .seekArmed }
      else
        match st1.s with
        | .clear => if st1.c ≤ st1.a + 1 then { st1 with ν := some .scan } else st1
        | .scan =>
            if v = bus I then { st1 with busNext := false }
            else
              let st2 : PState K := { st1 with busNext := true }
              if o = true then
                (if st2.j = K - 1 then { st2 with ν := some .commit } else { st2 with j := st2.j + 1 })
              else st2
        | .commit =>
            if st1.vC + ML K ≤ st1.a + 1 ∧ (RcL K : ℤ) ≤ st1.x then { st1 with ν := some .work }
            else st1

end DecDynMatch.Supplement


