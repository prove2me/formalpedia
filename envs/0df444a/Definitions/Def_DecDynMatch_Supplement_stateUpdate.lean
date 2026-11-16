-- Prove2me | Definitions.Def_DecDynMatch_Supplement_stateUpdate
-- name    : DecDynMatch_Supplement_stateUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:26:20.41176+00:00
-- url     : https://prove2.me/theorems/17b696de-c085-4292-8e9d-f3be7bc71345
-- title:
--   StateUpdate$(u)$ of SC-PC (Algorithm 4) and the initial player state
-- statement:
--   **StateUpdate$(u)$** (Algorithm 4):
--
--   1. $u\in\{\textsc{Seek}_{\rm fresh},\textsc{Seek}_{\rm armed}\}$: $m\leftarrow\textsc{Seek}$, $x\leftarrow0$, armed $\leftarrow(u=\textsc{Seek}_{\rm armed})$, $c\leftarrow a+J_L+\chi_L+4$, and $b\leftarrow a$ if armed, else $b\leftarrow a+E_L$;
--   2. $u=$ Root: $m\leftarrow\textsc{Root}$, $x\leftarrow0$ (retain $c$); if $a<c$ then $s\leftarrow\textsc{Clear}$, else $s\leftarrow\textsc{Scan}$, $j\leftarrow1$, busNext $\leftarrow$ true;
--   3. $u=$ Scan: $s\leftarrow\textsc{Scan}$, $j\leftarrow1$, busNext $\leftarrow$ true;
--   4. $u=$ Commit: $s\leftarrow\textsc{Commit}$, $v_C\leftarrow a$, $x\leftarrow\min\{x,0\}$;
--   5. $u=$ Work: $m\leftarrow\textsc{Work}$, $h\leftarrow0$, $S_i\leftarrow\mathcal K$, held $\leftarrow\bot$, target $\leftarrow\bot$, $z\leftarrow0$;
--   6. $u=$ Replay: $m\leftarrow\textsc{Replay}$.
--
--   The **initial state** (Algorithm 2, lines 1–3) has $N_v=U_v=0$, $\mathrm{lastA}[v]=-\infty$, $a=0$, $P=H_L$, $\ell=\bot$, $\nu=$ none, followed by StateUpdate$(\textsc{Seek}_{\rm fresh})$.
--
--   **Formalization Note** Variables Algorithm 2 leaves uninitialized are given placeholder values that are written before they are read.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithms 2 (lines 1–3) and 4, pp.30, 32

import Mathlib
import Definitions.Def_DecDynMatch_Instance
import Definitions.Def_DecDynMatch_Supplement_SCPCParams
import Definitions.Def_DecDynMatch_Supplement_PState

namespace DecDynMatch.Supplement

open DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **StateUpdate(u)** of SC-PC. J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), Algorithm 4, p.32:
* Seek_fresh / Seek_armed: `m ← Seek; x ← 0; armed ← (u = Seek_armed); c ← a + J_L + χ_L + 4`;
  `b ← a` if armed, else `b ← a + E_L`;
* Root: `m ← Root; x ← 0` (retain `c`); if `a < c` then `s ← Clear`, else `s ← Scan; j ← 1;
  busNext ← true`;
* Scan: `s ← Scan; j ← 1; busNext ← true`;
* Commit: `s ← Commit; v_C ← a; x ← min{x, 0}`;
* Work: `m ← Work; h ← 0; Sᵢ ← 𝒦; held ← ⊥; target ← ⊥; z ← 0`;
* Replay: `m ← Replay`. -/
def stateUpdate (u : Upd) (st : PState K) : PState K :=
  match u with
  | .seekFresh =>
      { st with m := .seek, x := 0, armed := false, c := st.a + JL K + chiL K + 4,
                bq := st.a + EL K }
  | .seekArmed =>
      { st with m := .seek, x := 0, armed := true, c := st.a + JL K + chiL K + 4, bq := st.a }
  | .root =>
      if st.a < st.c then { st with m := .root, x := 0, s := .clear }
      else { st with m := .root, x := 0, s := .scan, j := 1, busNext := true }
  | .scan => { st with s := .scan, j := 1, busNext := true }
  | .commit => { st with s := .commit, vC := st.a, x := min st.x 0 }
  | .work =>
      { st with m := .work, h := 0, S := Finset.univ, held := none, target := none, z := 0 }
  | .replay => { st with m := .replay }

/-- **Initial state of an SC-PC player** (Algorithm 2, lines 1–3, p.30): "For every v ∈ 𝒦, set
N_v = U_v = 0 and lastA[v] = −∞. a ← 0; P ← H_L; ℓ ← ⊥; ν ← none. StateUpdate(Seek_fresh)."

**Formalization Note.** Algorithm 2 leaves `s, j, busNext, v_C, h, Sᵢ, held, target, z, y, q`
uninitialized; each is written before it is read (Root entry sets `s` and, on Scan, `j` and
`busNext`; Commit entry sets `v_C`; Work entry sets `h, Sᵢ, held, target, z`; a Work output sets
`y, q` before Replay). The placeholder values chosen here are never observed. -/
def pinit (I : Instance K ι) : PState K :=
  stateUpdate .seekFresh
    { N := fun _ => 0, U := fun _ => 0, lastA := fun _ => none, a := 0, P := HL K, l := none,
      ν := none, m := .seek, x := 0, armed := false, c := 0, bq := 0, s := .clear, j := 1,
      busNext := true, vC := 0, h := 0, S := Finset.univ, held := none, target := none, z := 0,
      y := bus I, q := 0 }

end DecDynMatch.Supplement


