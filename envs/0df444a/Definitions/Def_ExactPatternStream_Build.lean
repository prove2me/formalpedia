-- Prove2me | Definitions.Def_ExactPatternStream_Build
-- name    : ExactPatternStream_Build
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:00.063088+00:00
-- url     : https://prove2.me/theorems/c29e6229-fee3-4c9f-add0-2bb3f2761a46
-- title:
--   Algorithm 1 and 2 — $\mathrm{Build}(P,T)$, $\mathrm{Match}(P,T)$, jump, $w_i$, $V_i'$, $E'$, $R'$, $\overline{S}_i$, $O_i$, $e_i$, $\gamma_i$
-- statement:
--   **Build** (Algorithm 1). Level $0$ is $P_0=\$\circ P$, $A^{(P)}_0=0\circ1^{m+1}$, $T_0=T$, $A^{(T)}_0=1^{n+1}$, with empty residuals. At level $i$: if $|P_i|=1$ then $h=i$, $c_h=0$. Otherwise $u_i=P_i[1]$ and $c_i=\max\{1\le c<|P_i|:P_i[1\,.\,.\,c]=u_i^c\}$. If $c_i=|P_i|-1$ then $h=i$. Otherwise $u_i^{c_i}\circ v_i=P_i[1\,.\,.\,c_i+1]$, and Pad with a fresh $\#_i$ followed by Group with $F_i$ gives level $i+1$ and the residuals, for pattern and text.
--
--   **Notation.** $w_0=1$, $w_{i+1}=(c_i+2)w_i$. $V_i'=\mathrm{leaves}(P_i[1\,.\,.\,c_i+1])$, $E'=\mathrm{leaves}(P_h[1\,.\,.\,c_h])$, $R'=\mathrm{leaves}(R^{(P)}_h\circ\dots\circ R^{(P)}_0)$, $\overline S_i=\mathrm{leaves}(S_i\circ R^{(S)}_i\circ\dots\circ R^{(S)}_0)$. $\mathrm{jump}_i(x)=\rho^{(T)}_i(x+c_i+1)/(c_i+2)$ on the active trigger occurrences $U^{(T)}_i$. $m_i=|P_i|-1$, $\mathrm{Res}_i=\mathrm{leaves}(R^{(P)}_i\circ\dots\circ R^{(P)}_0)$, $e_i(x)=(x+m_i)w_i+|\mathrm{Res}_i|$, $\gamma_i(e)=|\mathrm{erase}(\overline T_i[0\,.\,.\,e),\#)|$. $O_i$ is the set of active $x\in[0\,.\,.\,|T_i|]$ whose forest $\mathrm{subtrees}((T_i,A^{(T)}_i)[x\,.\,.\,x+m_i))$ equals $\mathrm{subtrees}((P_i,A^{(P)}_i)[1\,.\,.\,m_i])$.
--
--   **Match** (Algorithm 2). For every $k$ with $A^{(T)}_h[k]=1$ and $T_h[k\,.\,.\,k+c_h)=P_h[1\,.\,.\,c_h]$, let $e=(k+c_h)w_h+|R'|$; if $f_R(\overline T_h[e-|R'|\,.\,.\,e))=f_R(R')$, add $\gamma_h(e)-|P|$ to $M$.
--
--   These two procedures are the mathematical content of the algorithm, separated from the streaming implementation.
--
--   **Formalization Note** The hash functions are an argument, as in §§4–5, where they are "specified in Section 7.3". `F` sees the level, the trigger and the group's labels, and returns $(y,z,\alpha)$, so $\#_i$ is fresh at level $i$. Characters are natural numbers. `build` returns the levels $0,\dots,h$, with fuel $|P|+2$, which suffices since $|P_{i+1}|\le\frac23|P_i|$. $M$ is a set of integers, so a candidate with $\gamma_h(e)<|P|$ is negative, not $0$.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), (3)–(8), Algorithm 1, pp.9–11 (PDF 10–12); §5, pp.13–14 (PDF 14–15), Algorithm 2

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree

namespace ExactPatternStream

/-! # `Build(P, T)`, Algorithm 1, and the notation of §4.2–§4.3

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), eqs. (3)–(8), Algorithm 1,
pp.9–11 (PDF 10–12).

**Formalization Note.** `Build` takes the hash functions `F_i` of (6) as an argument `F : GroupHash`,
as §§4–5 of the paper do ("Choose `F_i` as in (6) // specified in Section 7.3"). `F` sees the level, the
trigger, and the labels of a group, and returns the triple `(y, z, α)`, so the value is a `Label.node`
and the marker `#ᵢ` is fresh at level `i`, as (6) requires. Input characters are natural numbers: every
finite `Σ` embeds. The result is the list of levels `0, …, h`, so `h = |Build F P T| - 1`. `c` at the last
level is `c_h`; the fields `u, v, hat*, rho*` are meaningful only for `i < h`. The recursion stops by
`|P_{i+1}| ≤ ⅔|P_i|`, and fuel `|P| + 2` is enough: `|P_0| = |P| + 1`. `R^(S)_i ◦ ⋯ ◦ R^(S)_0` is stored
as `stackS`. -/

/-- The trigger-indexed hash functions of (6). The arguments are `i`, `u_i`, `v_i`, `c_i`, and the labels
of a group; the value is the triple `(y, z, α)` of the label `Label.node y z α`. -/
abbrev GroupHash := ℕ → Label → Label → ℕ → List Label → List Bool × (ℕ × ℕ) × Bool

/-- One level of the two parse trees. -/
structure Level where
  /-- The level index `i`. -/
  i : ℕ
  /-- The node string `P_i`. -/
  P : List ParseTree
  /-- The annotation `A^(P)_i`. -/
  AP : List Bool
  /-- The node string `T_i`. -/
  T : List ParseTree
  /-- The annotation `A^(T)_i`. -/
  AT : List Bool
  /-- The residual `R^(P)_i`. -/
  RP : List ParseTree
  /-- The residual `R^(T)_i`. -/
  RT : List ParseTree
  /-- `R^(P)_i ◦ ⋯ ◦ R^(P)_0`. -/
  stackP : List ParseTree
  /-- `R^(T)_i ◦ ⋯ ◦ R^(T)_0`. -/
  stackT : List ParseTree
  /-- The width `w_i` of (7). -/
  w : ℕ
  /-- `c_i` of (4), and `c_h` at the last level. -/
  c : ℕ
  /-- `u_i`. -/
  u : Label
  /-- `v_i`. -/
  v : Label
  /-- The labels of `P̂_i`. -/
  hatP : List Label
  /-- `Â^(P)_i`. -/
  hatAP : List Bool
  /-- The labels of `T̂_i`. -/
  hatT : List Label
  /-- `Â^(T)_i`. -/
  hatAT : List Bool
  /-- The nodes of `P̂_i`. -/
  hatPt : List ParseTree
  /-- The nodes of `T̂_i`. -/
  hatTt : List ParseTree
  /-- `ρ^(P)_i = ρ_{P_i→P̂_i}`. -/
  rhoP : ℕ → ℕ
  /-- `ρ^(T)_i = ρ_{T_i→T̂_i}`. -/
  rhoT : ℕ → ℕ
  deriving Inhabited

/-- `c_i` of (4): the length of the run of `u_i = P_i[1]` starting at position `1`. -/
def runLength (ls : List Label) (u : Label) : ℕ := ((ls.drop 1).takeWhile (· = u)).length

/-- The last level, with `c_h = c`. -/
def lastLevel (i w c : ℕ) (P : List ParseTree) (AP : List Bool) (T : List ParseTree)
    (AT : List Bool) (RP RT stackP stackT : List ParseTree) : Level :=
  { i, P, AP, T, AT, RP, RT, stackP, stackT, w, c,
    u := default, v := default, hatP := [], hatAP := [], hatT := [], hatAT := [],
    hatPt := [], hatTt := [], rhoP := id, rhoT := id }

/-- The parent node of a padded group, Definition 4.8: its annotation is that of the first position. -/
def parentNode (F : GroupHash) (i : ℕ) (u v : Label) (c : ℕ) (g : List (Bool × ParseTree)) :
    ParseTree :=
  let r := F i u v c (g.map fun x => x.2.label)
  ParseTree.node (Label.node r.1 r.2.1 r.2.2) ((g.head?.map Prod.fst).getD false) g

/-- Pad and Group applied to one side, with the marker `#ᵢ` of width `w`: returns
`(Ŝ labels, Â, Ŝ nodes, ρ, S_{i+1}, A_{i+1}, R_{i+1})`. -/
def padGroup (F : GroupHash) (i w : ℕ) (u : Label) (c : ℕ) (v : Label) (S : List ParseTree)
    (A : List Bool) :
    List Label × List Bool × List ParseTree × (ℕ → ℕ) × List ParseTree × List Bool ×
      List ParseTree :=
  let ls := labels S
  let r := pad ls A u c v (Label.marker i)
  let ρ := padRho ls A u c v
  let hatS := expand S ρ (ParseTree.padding i w)
  let g := group (r.2.zip hatS) r.2 c (parentNode F i u v c)
  (r.1, r.2, hatS, ρ, g.1, g.2.1, g.2.2.map Prod.snd)

/-- The loop of Algorithm 1, from level `i` on. -/
def buildFrom (F : GroupHash) : ℕ → ℕ → ℕ → List ParseTree → List Bool → List ParseTree →
    List Bool → List ParseTree → List ParseTree → List ParseTree → List ParseTree → List Level
  | 0, i, w, P, AP, T, AT, RP, RT, sP, sT => [lastLevel i w 0 P AP T AT RP RT sP sT]
  | fuel + 1, i, w, P, AP, T, AT, RP, RT, sP, sT =>
      let ls := labels P
      if ls.length = 1 then [lastLevel i w 0 P AP T AT RP RT sP sT]
      else
        let u := ls.getD 1 default
        let c := runLength ls u
        if c = ls.length - 1 then [lastLevel i w c P AP T AT RP RT sP sT]
        else
          let v := ls.getD (c + 1) default
          let gP := padGroup F i w u c v P AP
          let gT := padGroup F i w u c v T AT
          let R'P := gP.2.2.2.2.2.2
          let R'T := gT.2.2.2.2.2.2
          { i, P, AP, T, AT, RP, RT, stackP := sP, stackT := sT, w, c, u, v,
            hatP := gP.1, hatAP := gP.2.1, hatT := gT.1, hatAT := gT.2.1,
            hatPt := gP.2.2.1, hatTt := gT.2.2.1, rhoP := gP.2.2.2.1, rhoT := gT.2.2.2.1 } ::
            buildFrom F fuel (i + 1) (w * (c + 2)) gP.2.2.2.2.1 gP.2.2.2.2.2.1
              gT.2.2.2.2.1 gT.2.2.2.2.2.1 R'P R'T (R'P ++ sP) (R'T ++ sT)

/-- `Build(P, T)`, Algorithm 1, started from level 0 as in (3): `P_0 = $ ◦ P`, `A^(P)_0 = 0 ◦ 1^{m+1}`,
`T_0 = T`, `A^(T)_0 = 1^{n+1}`, empty residuals. The result lists the levels `0, …, h`. -/
def build (F : GroupHash) (P T : List ℕ) : List Level :=
  buildFrom F (P.length + 2) 0 1
    (ParseTree.base Leaf.guard false :: P.map fun a => ParseTree.base (Leaf.sym a) true)
    (false :: List.replicate (P.length + 1) true)
    (T.map fun a => ParseTree.base (Leaf.sym a) true)
    (List.replicate (T.length + 1) true) [] [] [] []

/-- The index `h` of the last level. -/
def topIndex (B : List Level) : ℕ := B.length - 1

/-- The level `i` of a build. -/
def lvl (B : List Level) (i : ℕ) : Level := B.getD i default

namespace Level

variable (L : Level)

/-- `m_i = |P_i| - 1`, p.13. -/
def mi : ℕ := L.P.length - 1

/-- `g_i = c_i + 2`, p.22. -/
def g : ℕ := L.c + 2

/-- The unrolled string `P̄_i` of (8). -/
def Pbar : List Leaf := leavesOf (L.P ++ L.stackP)

/-- The unrolled string `T̄_i` of (8). -/
def Tbar : List Leaf := leavesOf (L.T ++ L.stackT)

/-- `Res_i = leaves(R^(P)_i ◦ ⋯ ◦ R^(P)_0)`, p.14; at the last level this is `R'`. -/
def Res : List Leaf := leavesOf L.stackP

/-- The unrolled trigger `V'_i = leaves(P_i[1 . . c_i + 1])`, p.11. -/
def V' : List Leaf := leavesOf (slice L.P 1 (L.c + 2))

/-- `E' = leaves(P_h[1 . . c_h])`, p.11, read at the last level. -/
def E' : List Leaf := leavesOf (slice L.P 1 (L.c + 1))

/-- `U^(T)_i`, p.10: the active trigger occurrences in `T_i`. -/
def UT : List ℕ := trigOcc (labels L.T) L.AT L.u L.c L.v

/-- `jump_i(x) = ρ^(T)_i(x + c_i + 1) / (c_i + 2)`, p.10. -/
def jump (x : ℕ) : ℕ := L.rhoT (x + L.c + 1) / (L.c + 2)

/-- `e_i(x) = (x + m_i) w_i + |Res_i|`, p.14. -/
def e (x : ℕ) : ℕ := (x + L.mi) * L.w + L.Res.length

/-- `γ_i(e) = |erase(T̄_i[0 . . e), #)|`, p.14. -/
def γ (e : ℕ) : ℕ := (erase (slice L.Tbar 0 e) Leaf.hash).length

/-- The string tested at `k` in Algorithm 2: `T̄_h[e - |R'| . . e)`, `e = (k + c_h) w_h + |R'|`, at the last
level, where `Res = R'`. -/
def scan (k : ℕ) : List Leaf :=
  slice L.Tbar ((k + L.c) * L.w) ((k + L.c) * L.w + L.Res.length)

end Level

/-- `O_i`, p.13: the positions `x ∈ [0 . . |T_i|]`, active, whose forest `subtrees((T_i, A)[x . . x + m_i))`
equals `subtrees((P_i, A)[1 . . m_i])`. Trees retain labels and annotations, so this is list equality. -/
def occSet (L : Level) : Set ℕ :=
  {x | x ≤ L.T.length ∧ L.AT.getD x false = true ∧
    slice L.T x (x + L.mi) = slice L.P 1 (L.mi + 1)}

/-- Algorithm 2, `Match(P, T)`, for a residual hash `fR`. `M` is a set of integers: `γ_h(e) - |P|` is an
integer subtraction, so a candidate with `γ_h(e) < |P|` is a negative element, not `0`. -/
def matchSet {β : Type*} [DecidableEq β] (F : GroupHash) (fR : List Leaf → β) (P T : List ℕ) :
    Finset ℤ :=
  let L := lvl (build F P T) (topIndex (build F P T))
  ((Finset.range (L.T.length + 1)).filter fun k =>
      L.AT.getD k false = true ∧
      slice (labels L.T) k (k + L.c) = slice (labels L.P) 1 (L.c + 1) ∧
      fR (L.scan k) = fR L.Res).image fun k =>
    ((L.γ ((k + L.c) * L.w + L.Res.length) : ℕ) : ℤ) - (P.length : ℤ)

end ExactPatternStream


