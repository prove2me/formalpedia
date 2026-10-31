-- Prove2me | Definitions.Def_DworczakDACC_applies
-- name    : DworczakDACC_applies
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:53.147738+00:00
-- url     : https://prove2.me/theorems/15292453-e723-4142-9fba-bdef165e5917
-- title:
--   The procedure "$i$ applies" of DACC
-- statement:
--   When agent $i$ **applies** in a state:
--
--   1. let $j=\arg\max\{B_i\cup\{\emptyset\};\succ^i\}$;
--   2. if $i$ and $j$ are already matched, or $j=\emptyset$, nothing happens;
--   3. otherwise record the application: $A_j:=A_j\cup\{i\}$ and $B_j:=B_j\cup\{i\}$;
--   4. if $i\succ^j\mu(j)$ ($j$ accepts $i$):
--      - (a) if $i$ was matched to some $j'$: if $i\in A_{j'}$ ($i$ **deceives** $j'$), push $j'$ on the stack $CC$; remove $i$ from $B_{j'}$; divorce $i$ and $j'$;
--      - (b) if $j$ was matched to some $i'$: if $j\in A_{i'}$, push $i'$ on $CC$; remove $j$ from $B_{i'}$; divorce $j$ and $i'$;
--      - (c) match $i$ and $j$;
--   5. otherwise ($j$ rejects $i$) remove $j$ from $B_i$.
--
--   Footnote a of Algorithm 1 allows (a) and (b) to be executed in either order. The procedure returns the new state and the list of agents pushed on $CC$ during the application, top first.
--
--   **Formalization Note** A Boolean parameter chooses the order of (a) and (b); the block executed second pushes on top. Blocks (a) and (b) change disjoint agents, so the order only affects the order of the pushes. The deception tests read the applicant sets after step 3. Acceptance is strict ($\operatorname{rank}_j(i)<\operatorname{rank}_j(\mu(j))$).
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Algorithm 1, procedure "i applies", p. 8

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_bestM
import Definitions.Def_DworczakDACC_bestW

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **The procedure "i applies" of DACC.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
Algorithm 1, "Description of the procedure 'i applies'", p. 8:

1. `j := argmax{Bᵢ; ≻ⁱ}`;
2. if `{i, j} ∈ µ` or `j = ∅`, return;
3. `Aⱼ := Aⱼ ∪ {i}` and `Bⱼ := Bⱼ ∪ {i}`;
4. if `i ≻ʲ µ(j)` (i is accepted by j):
   (a) if `∃ j' ≠ j` with `{i, j'} ∈ µ`: if `i ∈ A_{j'}` add `j'` to the top of `CC`;
       `B_{j'} := B_{j'} \ {i}`; `µ := µ \ {i, j'}`;
   (b) if `∃ i' ≠ i` with `{j, i'} ∈ µ`: if `j ∈ A_{i'}` add `i'` to the top of `CC`;
       `B_{i'} := B_{i'} \ {j}`; `µ := µ \ {j, i'}`;
   (c) `µ := µ ∪ {{i, j}}`;
5. else `Bᵢ := Bᵢ \ {j}`.

Footnote a: "Items (a) and (b) can be executed in any order, even random".

`applies Mk ab i s = (s', P)`: `s'` is the state after `i` applies in state `s`, and `P` is the
list of agents added to `CC` during this application, top first (so the new stack is `P ++ CC`).
For `ab = true` block (a) is executed before (b), for `ab = false` after it; the block executed
second pushes on top. The stack and the round counter of `s` are not changed here.

**Formalization Note.** Men are `D`, women `H`; `none` is `∅`; "i ≻ʲ µ(j)" is
`rank j (some i) < rank j (µ j)` (strict, smaller rank is better). The deception tests read the
applicant sets after step 3. `Bⱼ` is `budW`/`budM` and `Aⱼ` is `appW`/`appM` of the receiving
side. Blocks (a) and (b) change disjoint agents, so `ab` only changes the order of the pushes. -/
def applies (Mk : Market D H) (ab : Bool) (i : D ⊕ H) (s : State D H) :
    State D H × List (D ⊕ H) :=
  match i with
  | Sum.inl d =>
    match bestM Mk d (s.budM d) with
    | none => (s, [])
    | some h =>
      if s.mateM d = some h then (s, []) else
      -- step 3: record the application of `d` to `h` and add `d` to `h`'s budget
      let s₁ : State D H :=
        { s with
          appW := Function.update s.appW h (insert d (s.appW h))
          budW := Function.update s.budW h (insert d (s.budW h)) }
      if Mk.hospRank h (some d) < Mk.hospRank h (s₁.mateW h) then
        -- (a): `d` leaves his partner `h'`; compensate `h'` if `d ∈ A_{h'}`
        let blockA : State D H → State D H × List (D ⊕ H) := fun t =>
          match t.mateM d with
          | none => (t, [])
          | some h' =>
            ({ t with
                budW := Function.update t.budW h' ((t.budW h').erase d)
                mateM := Function.update t.mateM d none
                mateW := Function.update t.mateW h' none },
              if d ∈ t.appW h' then [Sum.inr h'] else [])
        -- (b): `h` leaves her partner `d'`; compensate `d'` if `h ∈ A_{d'}`
        let blockB : State D H → State D H × List (D ⊕ H) := fun t =>
          match t.mateW h with
          | none => (t, [])
          | some d' =>
            ({ t with
                budM := Function.update t.budM d' ((t.budM d').erase h)
                mateM := Function.update t.mateM d' none
                mateW := Function.update t.mateW h none },
              if h ∈ t.appM d' then [Sum.inl d'] else [])
        let r₁ := if ab then blockA s₁ else blockB s₁
        let r₂ := if ab then blockB r₁.1 else blockA r₁.1
        -- (c): match `d` and `h`
        ({ r₂.1 with
            mateM := Function.update r₂.1.mateM d (some h)
            mateW := Function.update r₂.1.mateW h (some d) },
          r₂.2 ++ r₁.2)
      else
        -- step 5: `d` is rejected by `h`
        ({ s₁ with budM := Function.update s₁.budM d ((s₁.budM d).erase h) }, [])
  | Sum.inr h =>
    match bestW Mk h (s.budW h) with
    | none => (s, [])
    | some d =>
      if s.mateW h = some d then (s, []) else
      -- step 3: record the application of `h` to `d` and add `h` to `d`'s budget
      let s₁ : State D H :=
        { s with
          appM := Function.update s.appM d (insert h (s.appM d))
          budM := Function.update s.budM d (insert h (s.budM d)) }
      if Mk.docRank d (some h) < Mk.docRank d (s₁.mateM d) then
        -- (a): `h` leaves her partner `d'`; compensate `d'` if `h ∈ A_{d'}`
        let blockA : State D H → State D H × List (D ⊕ H) := fun t =>
          match t.mateW h with
          | none => (t, [])
          | some d' =>
            ({ t with
                budM := Function.update t.budM d' ((t.budM d').erase h)
                mateM := Function.update t.mateM d' none
                mateW := Function.update t.mateW h none },
              if h ∈ t.appM d' then [Sum.inl d'] else [])
        -- (b): `d` leaves his partner `h'`; compensate `h'` if `d ∈ A_{h'}`
        let blockB : State D H → State D H × List (D ⊕ H) := fun t =>
          match t.mateM d with
          | none => (t, [])
          | some h' =>
            ({ t with
                budW := Function.update t.budW h' ((t.budW h').erase d)
                mateM := Function.update t.mateM d none
                mateW := Function.update t.mateW h' none },
              if d ∈ t.appW h' then [Sum.inr h'] else [])
        let r₁ := if ab then blockA s₁ else blockB s₁
        let r₂ := if ab then blockB r₁.1 else blockA r₁.1
        -- (c): match `h` and `d`
        ({ r₂.1 with
            mateM := Function.update r₂.1.mateM d (some h)
            mateW := Function.update r₂.1.mateW h (some d) },
          r₂.2 ++ r₁.2)
      else
        -- step 5: `h` is rejected by `d`
        ({ s₁ with budW := Function.update s₁.budW h ((s₁.budW h).erase d) }, [])

end DworczakDACC


