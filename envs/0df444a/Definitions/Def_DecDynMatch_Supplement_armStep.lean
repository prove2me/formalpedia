-- Prove2me | Definitions.Def_DecDynMatch_Supplement_armStep
-- name    : DecDynMatch_Supplement_armStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:29:46.293809+00:00
-- url     : https://prove2.me/theorems/626808f1-28d2-40c4-950e-31c288a4ec9a
-- title:
--   One round of an SC-PC arm (Algorithm 3) with the eligible set (49)
-- statement:
--   An arm starts at its first proposal with clock $a=0$, empty-round counter $e=0$ and Business time $\lambda=0$, and per-proposer records $N_i=U_i=0$, $\mathrm{last}[i]=-\infty$. In each later round (including empty ones), with current proposers $R$ and the value of $\lambda$ at the start of the round:
--
--   1. if $R\ne\emptyset$, the eligible proposers are
--   $$
--   Q=\begin{cases}C_a(R),&\lambda>0\ (\textsc{Business}),\\ R,&\lambda=0,\ a\equiv0\pmod{G_L},\\ \{\min_\prec R\},&\lambda=0,\ a\not\equiv0\pmod{G_L},\end{cases}
--   $$
--   and the arm accepts the $i\in Q$ minimizing $\mathrm{last}[i]$ (never-accepted first), ties broken by its private order $\prec$, records its own realized utility $r$ ($N_i\leftarrow N_i+1$, $U_i\leftarrow U_i+r$, $\mathrm{last}[i]\leftarrow a$) and rejects the others; otherwise it accepts nobody;
--   2. $e\leftarrow e+1$ if $R=\emptyset$, else $e\leftarrow0$; $\lambda\leftarrow\tau_L$ if $e\ge2$, else $\lambda\leftarrow\max\{\lambda-1,0\}$; $a\leftarrow a+1$.
--
--   **Formalization Note** The private order is an injective rank $\mathrm{rk}:\iota\to\mathbb N$; the arm's state is `none` before its first proposal. Initializing every player's record up front equals initializing each unseen proposer on arrival.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithm 3 and eq. (49), pp.31–32

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_SCPCParams
import Definitions.Def_DecDynMatch_Supplement_confSet

namespace DecDynMatch.Supplement

/-- Local state of a started SC-PC arm (Algorithm 3, p.32): per-proposer counts `N i`, utility
sums `U i` and last acceptance ages `last i` (`none` = `−∞`), the local clock `a`, the
empty-round counter `e` and the remaining Business time `λ` (field `lam`). -/
structure AState (ι : Type*) where
  N : ι → ℕ
  U : ι → ℝ
  last : ι → Option ℕ
  a : ℕ
  e : ℕ
  lam : ℕ

variable {ι : Type*}

/-- State of an arm at its first proposal (Algorithm 3, lines 1–2): `a = e = λ = 0`, and every
proposer has `N_i = U_i = 0`, `last[i] = −∞` (initializing every player up front is the same as
initializing each previously unseen proposer on arrival). -/
def ainit : AState ι :=
  { N := fun _ => 0, U := fun _ => 0, last := fun _ => none, a := 0, e := 0, lam := 0 }

open Classical in
/-- `{min_≺ R}`: the proposers of `R` that are least in the arm's private order, given as an
injective rank `rk` (a singleton for nonempty `R`). -/
noncomputable def minOrd (rk : ι → ℕ) (R : Finset ι) : Finset ι :=
  R.filter (fun i => ∀ j ∈ R, rk i ≤ rk j)

open Classical in
/-- The eligible proposers `Q` of eq. (49), p.31: `C_a(R)` if `λ > 0` (Business); `R` if `λ = 0` and
`a ≡ 0 (mod G_L)` (fair Control round); `{min_≺ R}` if `λ = 0` and `a ≢ 0 (mod G_L)`. -/
noncomputable def armEligible (K : ℕ) (rk : ι → ℕ) (st : AState ι) (R : Finset ι) : Finset ι :=
  if 0 < st.lam then confSet st.a st.N st.U R
  else if st.a % GLmod K = 0 then R else minOrd rk R

/-- Sort key of a proposer: its last acceptance age (`−∞` first) and then its private rank. -/
def armKey (rk : ι → ℕ) (st : AState ι) (i : ι) : ℕ ×ₗ ℕ :=
  toLex ((match st.last i with | none => 0 | some l => l + 1), rk i)

open Classical in
/-- "Accept the proposer i ∈ Q minimizing last[i], breaking ties by ≺" (Algorithm 3, line 7):
the proposer of `Q` with the least key, `none` if `Q = ∅`. With an injective rank the minimizer is
unique. -/
noncomputable def armPick (rk : ι → ℕ) (st : AState ι) (Q : Finset ι) : Option ι :=
  let W := Q.filter (fun i => ∀ j ∈ Q, armKey rk st i ≤ armKey rk st j)
  if hW : W.Nonempty then some hW.choose else none

open Classical in
/-- One round of a started arm (Algorithm 3, lines 2–13): with proposers `R` and arm-side realized
utilities `r`, if `R ≠ ∅` accept the pick from the eligible set (49) and record
`N_i ← N_i + 1, U_i ← U_i + r, last[i] ← a`; then `e ← e + 1` if `R = ∅` else `e ← 0`; `λ ← τ_L` if
`e ≥ 2` else `λ ← max{λ − 1, 0}`; `a ← a + 1`. The round's mode uses `λ` at the start of the round. -/
noncomputable def armProcess (K : ℕ) (rk : ι → ℕ) (st : AState ι) (R : Finset ι) (r : ι → ℝ) :
    Option ι × AState ι :=
  let acc : Option ι := if R.Nonempty then armPick rk st (armEligible K rk st R) else none
  let st1 : AState ι :=
    match acc with
    | none => st
    | some i =>
        { st with N := Function.update st.N i (st.N i + 1),
                  U := Function.update st.U i (st.U i + r i),
                  last := Function.update st.last i (some st.a) }
  let e' : ℕ := if R = ∅ then st1.e + 1 else 0
  let lam' : ℕ := if 2 ≤ e' then tauL K else st1.lam - 1
  (acc, { st1 with e := e', lam := lam', a := st1.a + 1 })

open Classical in
/-- **One round of an SC-PC arm.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), Algorithm 3 and eq. (49), pp.31–32: "When an arm first
receives a proposal, it starts its local clock at a = 0 and enters Control. Its clock then advances
in every round, including rounds with no proposals. … Here ≺ is the arm's fixed private order of
proposers, which may differ from its utility ranking. … Two consecutive empty rounds start or renew
τ_L rounds of Business service, and each further empty round renews it."

`armStep K rk st R r` takes the arm's state (`none` = not yet started), its private order as an
injective rank `rk`, the set `R` of current proposers and the arm's realized utility `r i` of each
proposer, and returns the accepted proposer (if any) and the new state. An unstarted arm with no
proposer stays unstarted. -/
noncomputable def armStep (K : ℕ) (rk : ι → ℕ) (st : Option (AState ι)) (R : Finset ι)
    (r : ι → ℝ) : Option ι × Option (AState ι) :=
  match st with
  | none =>
      if R.Nonempty then
        let p := armProcess K rk ainit R r
        (p.1, some p.2)
      else (none, none)
  | some s =>
      let p := armProcess K rk s R r
      (p.1, some p.2)

end DecDynMatch.Supplement


