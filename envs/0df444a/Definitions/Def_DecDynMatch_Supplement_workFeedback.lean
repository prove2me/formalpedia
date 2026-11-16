-- Prove2me | Definitions.Def_DecDynMatch_Supplement_workFeedback
-- name    : DecDynMatch_Supplement_workFeedback
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:28:13.997302+00:00
-- url     : https://prove2.me/theorems/2d5c6e3d-f306-4910-b528-46d3a8346f22
-- title:
--   WorkFeedback$(v,\mathrm{type},o)$ of SC-PC (Algorithm 7) with the waiting-length rule (50)
-- statement:
--   After a Work proposal to $v$ of the given type with outcome $o$:
--
--   1. if type $=$ probe and $o=A$: target $\leftarrow\bot$, $z\leftarrow0$;
--   2. if $h_{D,L}\le h<f_L$, type $\in\{$hold, probe$\}$ and $o=R$: $z\leftarrow z+1$; otherwise $z\leftarrow0$;
--   3. if $z=K$: $S_i\leftarrow S_i\setminus\{v\}$, held $\leftarrow\bot$, target $\leftarrow\bot$, $z\leftarrow0$;
--   4. if $h<J_L-1$: $h\leftarrow h+1$ and return;
--   5. otherwise (output) with the previous $P,\ell$:
--   $$
--   \tilde L=\begin{cases}H_L,&\ell=\bot,\\ H_L+2(a-\ell),&\ell\ne\bot,\end{cases}\qquad P^+=\max\Bigl\{P,\Bigl\lfloor\frac{3P+\tilde L}{4}\Bigr\rfloor\Bigr\},
--   $$
--   $L=P^+$ if held $\ne\bot$ and $o=A$, else $L=H_L$; $(P,\ell,y,q)\leftarrow(P^+,a,v,a+L)$; $\nu\leftarrow$ Replay.
--
--   **Formalization Note** Floor division and $a-\ell$ are natural-number operations; $\ell<a$ always.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithm 7 and eq. (50), pp.34–35

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_stateUpdate

namespace DecDynMatch.Supplement

open DecDynMatch

variable {K : ℕ}

/-- **WorkFeedback(v, type, o)** of SC-PC, with the waiting-length rule (50). J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), Algorithm 7 and
eq. (50), pp.34–35:
1. if type = probe and `o = A`: `target ← ⊥; z ← 0`;
2. if `h_{D,L} ≤ h < f_L`, type ∈ {hold, probe} and `o = R`: `z ← z + 1`; else `z ← 0`;
3. if `z = K`: `Sᵢ ← Sᵢ \ {v}; held ← ⊥; target ← ⊥; z ← 0`;
4. if `h < J_L − 1`: `h ← h + 1`; return;
5. (output) `L̃ = H_L` if `ℓ = ⊥`, `L̃ = H_L + 2(a − ℓ)` otherwise; `P⁺ = max{P, ⌊(3P + L̃)/4⌋}`;
   `L = P⁺` if `held ≠ ⊥` and `o = A`, else `L = H_L`; `(P, ℓ, y, q) ← (P⁺, a, v, a + L)`;
   `ν ← Replay`.

**Formalization Note.** `⌊·/4⌋` is natural-number division. `a − ℓ` is natural-number
subtraction; `ℓ` is an earlier local age, so `ℓ < a` and nothing truncates. -/
def workFeedback (v : Fin K) (ty : PType) (o : Bool) (st : PState K) : PState K :=
  let st1 : PState K :=
    if ty = .probe ∧ o = true then { st with target := none, z := 0 } else st
  let st2 : PState K :=
    if hDL K ≤ st1.h ∧ st1.h < fL K ∧ (ty = .hold ∨ ty = .probe) ∧ o = false then
      { st1 with z := st1.z + 1 }
    else { st1 with z := 0 }
  let st3 : PState K :=
    if st2.z = K then { st2 with S := st2.S.erase v, held := none, target := none, z := 0 }
    else st2
  if st3.h < JL K - 1 then { st3 with h := st3.h + 1 }
  else
    let Lt : ℕ :=
      match st3.l with
      | none => HL K
      | some l => HL K + 2 * (st3.a - l)
    let Pp : ℕ := max st3.P ((3 * st3.P + Lt) / 4)
    let L : ℕ := if st3.held.isSome = true ∧ o = true then Pp else HL K
    { st3 with P := Pp, l := some st3.a, y := v, q := st3.a + L, ν := some .replay }

end DecDynMatch.Supplement


