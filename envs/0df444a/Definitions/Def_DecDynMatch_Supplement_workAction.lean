-- Prove2me | Definitions.Def_DecDynMatch_Supplement_workAction
-- name    : DecDynMatch_Supplement_workAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:27:32.882197+00:00
-- url     : https://prove2.me/theorems/7b49c7e2-ecf0-441e-b492-fd3e8d5e5658
-- title:
--   WorkAction() of SC-PC (Algorithm 6)
-- statement:
--   The proposal of a player in Work after $h$ completed Work rounds:
--
--   1. if $h<d_L$: $z\leftarrow0$, propose to PARK (type park);
--   2. if held $\ne\bot$: propose to the held arm (type hold);
--   3. if $S_i\ne\emptyset$, $h\le f_L$ and $|C_a(S_i)|=1$: certify the unique $v\in C_a(S_i)$ — held $\leftarrow v$, target $\leftarrow\bot$, $z\leftarrow0$ — and propose to $v$ (type hold);
--   4. if target $=\bot$: $Q\leftarrow C_a(S_i)$ if $S_i\ne\emptyset$, else $Q\leftarrow C_a(\mathcal K)$; target $\leftarrow\arg\min_{v\in Q}(N_v,v)$ (lexicographic); $z\leftarrow0$;
--   5. if $a-\mathrm{lastA}[\text{target}]\ge K$: propose to the target (type probe);
--   6. otherwise $z\leftarrow0$ and propose to the filler $\min\{w\in\mathcal K: a-\mathrm{lastA}[w]\ge K\}$ (type filler).
--
--   The confidence sets use the player's own clock, counts and sums (observations through the previous round).
--
--   **Formalization Note** "$a-(-\infty)\ge K$" is true. The paper shows a filler always exists and $C_a(Q)\neq\emptyset$ for $Q\ne\emptyset$; the fallback arm 0 for those impossible cases is never used.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithm 6, p.34

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_stateUpdate
import Definitions.Def_DecDynMatch_Supplement_confSet

namespace DecDynMatch.Supplement

open DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- Arm `w` has not accepted the player in the preceding `K − 1` rounds: `a − lastA[w] ≥ K`, true
when `lastA[w] = −∞` (`none`). -/
def Fresh (K a : ℕ) (l : Option ℕ) : Prop :=
  match l with
  | none => True
  | some l => K ≤ a - l

open Classical in
/-- `arg min_{v ∈ Q} (N_v, v)`: a least-sampled arm of `Q`, ties broken by the smallest arm index
(Algorithm 6, line 12). Returns `dflt` on an empty `Q` (never used). -/
noncomputable def argminNV (N : Fin K → ℕ) (Q : Finset (Fin K)) (dflt : Fin K) : Fin K :=
  if h : Q.Nonempty then
    let W := Q.filter (fun v => N v = Q.inf' h N)
    if hW : W.Nonempty then W.min' hW else dflt
  else dflt

open Classical in
/-- **WorkAction()** of SC-PC. J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), Algorithm 6, p.34, verbatim control flow:
1. if `h < d_L`: `z ← 0`; return (PARK, park);
2. if `held ≠ ⊥`: return (held, hold);
3. if `Sᵢ ≠ ∅`, `h ≤ f_L` and `|C_a(Sᵢ)| = 1`: `v ←` the unique element of `C_a(Sᵢ)`;
   `held ← v; target ← ⊥; z ← 0`; return (v, hold);
4. if `target = ⊥`: `Q ← C_a(Sᵢ)` if `Sᵢ ≠ ∅`, else `Q ← C_a(𝒦)`; `target ← arg min_{v∈Q}(N_v, v)`;
   `z ← 0`;
5. if `a − lastA[target] ≥ K`: return (target, probe);
6. `z ← 0`; `v ← min{w ∈ 𝒦 : a − lastA[w] ≥ K}`; return (v, filler).

Returns the updated state, the proposed arm and the proposal type. `C_a` uses the player's own
clock, counts and sums (observations through the previous round).

**Formalization Note.** The unique element of a one-element set is its minimum. The paper shows a
filler always exists and `C_a(Q) ≠ ∅` for `Q ≠ ∅`; the fallback arm `BUS` for the impossible empty
cases is never used. -/
noncomputable def workAction (I : Instance K ι) (st : PState K) : PState K × Fin K × PType :=
  if st.h < dL K then ({ st with z := 0 }, park I, .park)
  else
    match st.held with
    | some v => (st, v, .hold)
    | none =>
        let C := confSet st.a st.N st.U st.S
        if st.S.Nonempty ∧ st.h ≤ fL K ∧ C.card = 1 then
          let v : Fin K := if hC : C.Nonempty then C.min' hC else bus I
          ({ st with held := some v, target := none, z := 0 }, v, .hold)
        else
          let stT : PState K :=
            match st.target with
            | some _ => st
            | none =>
                let Q := if st.S.Nonempty then confSet st.a st.N st.U st.S
                  else confSet st.a st.N st.U Finset.univ
                { st with target := some (argminNV st.N Q (bus I)), z := 0 }
          let tg : Fin K := stT.target.getD (bus I)
          if Fresh K stT.a (stT.lastA tg) then (stT, tg, .probe)
          else
            let Fl := Finset.univ.filter (fun w => Fresh K stT.a (stT.lastA w))
            let v : Fin K := if hF : Fl.Nonempty then Fl.min' hF else bus I
            ({ stT with z := 0 }, v, .filler)

end DecDynMatch.Supplement


