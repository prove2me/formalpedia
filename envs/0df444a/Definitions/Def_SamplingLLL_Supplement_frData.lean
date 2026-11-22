-- Prove2me | Definitions.Def_SamplingLLL_Supplement_frData
-- name    : SamplingLLL_Supplement_frData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:49:47.141022+00:00
-- url     : https://prove2.me/theorems/1c5fdf6c-5a8b-420f-a5ee-aebb1977a6d3
-- title:
--   Finite-Range Theorem: the counter, the sampling attempt and the restart of Appendix D
-- statement:
--   The explicit procedures of the proof of Theorem 5.4, for an atomic product-space CSP, a rational $p_0$ and a cutoff $L$.
--
--   1. **Decision tree (D.1).** For the task of inserting $c$ into $A$: accept $c$, and repeatedly query the first unqueried constraint of $A$ that meets the variables of the accepted constraints and whose forbidden word agrees with theirs; constraints inside the current variable set are queried too. Stop when no query is eligible or upon accepting $L$ constraints. A record that accepted $L$ constraints is a **frontier** record. For a record $t$ with accepted family $Y_t$: $W_t=\mathrm{vbl}(Y_t)$, $R_t=\{a\in A:\mathrm{vbl}(a)\cap W_t=\emptyset\}$, the collar $D_t=A\setminus R_t$ in the constraint order, and the child tasks obtained by reinserting $D_t$ into $R_t$.
--   2. **Proposal (D.2–D.3).** Enumerate the records and draw the record $t$ with probability $\bar w_t/B$, where $\bar w_t=a_t s^{-\ell_t}$, $a_t=\lambda_{W_t}(f_t)$, $\ell_t=|D_t|$, $B=4p_0$, $s=1-B$; the remaining mass is the null outcome.
--   3. **One sampling attempt (D.3–D.4).** A draw from $\lambda$, then the sequential insertion of all $m$ constraints by the packet circuit of Lemma A.6 with these rows. A proposed frontier record **aborts**; an abort propagates through all callers and ends the attempt with a failure.
--   4. **Restart.** Repeat the whole attempt until it succeeds.
--   5. **Deterministic counter (D.5).** For each insertion task $i$ along the insertion order, compute the coefficients of degree $<L$ of the series
--   $$
--   f_i(z)=\sum_{t\ \mathrm{ordinary}}\epsilon_t\,a_t\,z^{|Y_t|}\prod_{j\ \mathrm{child\ of}\ t}\bigl(1-f_j(z)\bigr)^{-1},\qquad \epsilon_t=(-1)^{|Y_t|-1},
--   $$
--   sum them, clip the sum to $[0,2p_0]$ to get $\tilde r_i$, and output $\hat Z=\prod_{i=1}^m(1-\tilde r_i)$. The procedure draws no random bits.
--
--   The input length $N$ is the base input length of the instance, which includes the encoding of $\lambda$.
--
--   **Formalization Note** A failure is the output `none`. All arithmetic is charged by the actual bit lengths; each visited node of a decision tree is charged $(N+L+\ell(p_0))^3$. The module has no declaration named `frData`; its main declarations are `frCount`, `frAttempt`, `frRestart`.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 5.4, pp.16–17; Appendix D.1–D.5, pp.39–45; (47), p.44

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_Common

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-! # The Finite-Range Theorem: the procedures of Appendix D

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), Theorem 5.4, pp.16–17; Appendix D.1–D.5, pp.39–45.

An abort is the output `none` of a procedure of type `Proc (Option α)`; it propagates through all callers
and terminates the whole sampling attempt (D.4, p.42). -/

variable {n m : ℕ} (I : AtomicCSP n m)

/-- The decision tree of D.1, p.40, for the task `(A, c)` with cutoff `L`: query the first unqueried
constraint of `A` that meets the variables fixed by the accepted constraints and is compatible with their
forbidden word (constraints inside the current variable set are queried too); stop when none is eligible or
upon accepting `L` constraints. -/
def frNext (L : ℕ) (A : Finset (Fin m)) (_c : Fin m) : NextQuery m := fun Y N =>
  if L ≤ Y.card then none else
    (List.finRange m).find? fun b =>
      decide (b ∈ A ∧ b ∉ Y ∧ b ∉ N ∧ (∃ v ∈ I.vbl b, v ∈ Y.biUnion I.vbl) ∧
        ∀ v ∈ I.vbl b, v ∈ Y.biUnion I.vbl → I.word b v = I.pin Y v)

/-- A frontier record: `|Y_t| = L` (D.1, p.40). -/
def frontier (L : ℕ) (t : Leaf m) : Prop := L ≤ t.1.card

instance (L : ℕ) (t : Leaf m) : Decidable (frontier L t) := by unfold frontier; infer_instance

/-- `W_t = vbl(Y_t)`. -/
def frW (t : Leaf m) : Finset (Fin n) := t.1.biUnion I.vbl

/-- `R_t = {a ∈ A : vbl(a) ∩ W_t = ∅}` (D.1, p.40). -/
def frR (A : Finset (Fin m)) (t : Leaf m) : Finset (Fin m) :=
  A.filter fun a => Disjoint (I.vbl a) (frW I t)

/-- `D_t = A ∖ R_t` in the fixed constraint order (D.1, p.41). -/
def frD (A : Finset (Fin m)) (t : Leaf m) : List (Fin m) :=
  (List.finRange m).filter fun a => a ∈ A ∧ ¬ Disjoint (I.vbl a) (frW I t)

/-- The child tasks `j(t, h) = (A_{h−1}, d_h)`, `A_0 = R_t` (D.1, p.41). -/
def frChildren (A : Finset (Fin m)) (t : Leaf m) : List (Finset (Fin m) × Fin m) :=
  chain (frD I A t) (frR I A t)

/-- The records of the task `(A, c)`, by traversing the decision tree depth first (yes before no); each
visited node is charged `L'^3`. The fuel `m + 1` is never exhausted. -/
noncomputable def records (L L' : ℕ) (A : Finset (Fin m)) (c : Fin m) :
    ℕ → Leaf m → Proc (List (Leaf m))
  | 0, t => pure [t]
  | k + 1, t => do
    tick (L' ^ 3)
    match frNext I L A c t.1 t.2 with
    | none => pure [t]
    | some b => do
      let l₁ ← records L L' A c k (insert b t.1, t.2)
      let l₂ ← records L L' A c k (t.1, insert b t.2)
      pure (l₁ ++ l₂)

/-- `a_t = λ_{W_t}(f_t)` by charged multiplications. -/
noncomputable def frA (t : Leaf m) : Proc ℚ :=
  I.uProd t.1 ((List.finRange n).filter fun v => v ∈ frW I t) 1

/-- The proposal probability `q_i(t) = w̄_t/B`, with `w̄_t = a_t s^{−ℓ_t}`, `B = 4p`, `s = 1 − B` (D.2–D.3,
pp.41–42), charged. -/
noncomputable def frQ (p : ℚ) (A : Finset (Fin m)) (t : Leaf m) : Proc ℚ := do
  let a ← frA I t
  let B ← qmul 4 p
  let s ← qsub 1 B
  let sl ← charge (cpow (cq s) (frD I A t).length)
  let den ← qmul sl B
  qdiv a den

/-- Pair every record with its proposal probability. -/
noncomputable def withQ (p : ℚ) (A : Finset (Fin m)) : List (Leaf m) → Proc (List (Option (Leaf m) × ℚ))
  | [] => pure []
  | t :: l => do
    let q ← frQ I p A t
    let r ← withQ p A l
    pure ((some t, q) :: r)

/-- The proposal of D.3, p.42 (implementation, p.44): enumerate the records, compute their rational
probabilities `w̄_t/B`, and draw exactly from this distribution, the remaining mass being the null outcome
(`none`). -/
noncomputable def frPropose (p : ℚ) (L L' : ℕ) (A : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Leaf m)) := do
  let rs ← records I L L' A c (m + 1) ({c}, ∅)
  let l ← withQ I p A rs
  drawList l none 1

/-- The kernels of a level in the abort-propagating execution. -/
structure AK (I : AtomicCSP n m) where
  /-- Insertion kernel of the task `(A, c)`; `none` is an abort. -/
  insert : Finset (Fin m) → Fin m → I.toCSP.Config → Proc (Option I.toCSP.Config)
  /-- Deletion kernel of the task `(A, c)`; `none` is an abort. -/
  delete : Finset (Fin m) → Fin m → I.toCSP.Config → Proc (Option I.toCSP.Config)
  /-- Reciprocal coin of the task `(A, c)`; `none` is an abort. -/
  coin : Finset (Fin m) → Fin m → Proc (Option Bool)

/-- Request a coin for each occurrence in the list, all of them; an abort propagates. -/
noncomputable def allCoinsA (K : AK I) : List (Finset (Fin m) × Fin m) → Proc (Option Bool)
  | [] => pure (some true)
  | j :: l => do
    match ← K.coin j.1 j.2 with
    | none => pure none
    | some b =>
      match ← allCoinsA K l with
      | none => pure none
      | some b' => pure (some (b && b'))

/-- The signed experiment of the implemented scalar factory (D.3–D.4, pp.42–43): propose; a frontier
proposal aborts before its acceptance probability is evaluated; an ordinary record is accepted with
probability one (its thinning ratio `b_t/[B q_i(t) s^{ℓ_t}]` is `1`), and then all child coins are
requested. The result `some (some t)` has value `ε_t B`; `some none` is the null outcome. -/
noncomputable def frExperiment (p : ℚ) (L L' : ℕ) (K : AK I) (A : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Option (Leaf m))) := do
  match ← frPropose I p L L' A c with
  | none => pure (some none)
  | some t =>
    if frontier L t then pure none else do
      match ← allCoinsA I K (frChildren I A t) with
      | none => pure none
      | some ok => pure (some (if ok then some t else none))

/-- The reciprocal coin of the implemented factory (Lemma A.5, p.22; D.3, p.42), one counted invocation:
repeat "with probability `α = 2B/(1+B)` continue, else accept"; on continue run the signed experiment and
toss the coin of bias `(Y+B)/(2B)`; an abort propagates. -/
noncomputable def frCoinAt (p : ℚ) (L L' : ℕ) (K : AK I) (A : Finset (Fin m)) (c : Fin m) :
    Proc (Option Bool) := do
  countCall 1
  let B ← qmul 4 p
  let twoB ← qmul 2 B
  let oneB ← qadd 1 B
  let α ← qdiv twoB oneB
  loop (fun _ : Unit => do
    let go ← ratCoin α
    if go then do
      match ← frExperiment I p L L' K A c with
      | none => pure (Sum.inr none)
      | some none =>
        let b ← flip
        if b then pure (Sum.inl ()) else pure (Sum.inr (some false))
      | some (some t) =>
        if sign t = 1 then pure (Sum.inl ()) else pure (Sum.inr (some false))
    else pure (Sum.inr (some true))) ()

/-- The unnormalized packet generator: an independent `B`-coin, then the experiment. -/
noncomputable def frGenerator (p : ℚ) (L L' : ℕ) (K : AK I) (A : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Option (Leaf m))) := do
  let B ← qmul 4 p
  let b ← ratCoin B
  if b then frExperiment I p L L' K A c else pure (some none)

/-- Deletion chain along a list of tasks; an abort propagates. -/
noncomputable def delChainA (K : AK I) : List (Finset (Fin m) × Fin m) → I.toCSP.Config →
    Proc (Option I.toCSP.Config)
  | [], x => pure (some x)
  | (A, d) :: l, x => do
    match ← K.delete A d x with
    | none => pure none
    | some y => delChainA K l y

/-- Insertion chain along a list of tasks; an abort propagates. -/
noncomputable def insChainA (K : AK I) : List (Finset (Fin m) × Fin m) → I.toCSP.Config →
    Proc (Option I.toCSP.Config)
  | [], x => pure (some x)
  | (A, d) :: l, x => do
    match ← K.insert A d x with
    | none => pure none
    | some y => insChainA K l y

/-- The entry row of an ordinary packet (D.3, p.42): delete `D_t` in reverse order, overwrite `W_t` by
`f_t`. -/
noncomputable def frEnter (L' : ℕ) (K : AK I) (A : Finset (Fin m)) (t : Leaf m) (x : I.toCSP.Config) :
    Proc (Option I.toCSP.Config) := do
  match ← delChainA I K (frChildren I A t).reverse x with
  | none => pure none
  | some y =>
    tick L'
    pure (some fun v => if v ∈ frW I t then (I.pin t.1 v).getD 0 else y v)

/-- The exit row of an ordinary packet (D.3, p.42): redraw `W_t` from `λ_{W_t}`, reinsert `D_t` in order.
A frontier record aborts before it is exited (D.4, p.42). -/
noncomputable def frExit (L L' : ℕ) (K : AK I) (A : Finset (Fin m)) (t : Leaf m) (x : I.toCSP.Config) :
    Proc (Option I.toCSP.Config) := do
  if frontier L t then pure none else do
    tick L'
    let y ← I.toCSP.redraw ((List.finRange n).filter fun v => v ∈ frW I t) x
    insChainA I K (frChildren I A t) y

/-- The last-defect pairing of Lemma D.2, p.40: `none` is the residual label, when `c` is the only violated
constraint of `A ∪ {c}`. -/
noncomputable def frRoute (L L' : ℕ) (A : Finset (Fin m)) (c : Fin m) (t : Leaf m)
    (x : I.toCSP.Config) : Proc (Option (Leaf m)) := do
  tick ((m + 1) * (L' + 2 * L' ^ 3))
  let B := I.toCSP.badSet (insert c A) x
  if B = {c} then pure none else pure (some (routerLeaf (frNext I L A c) c B t))

/-- The forward kernel `μ_A → μ_{A∪{c}}` of Lemma A.6 (p.23) with the rows of D.3 and the aborts of D.4. -/
noncomputable def frForward (p : ℚ) (L L' : ℕ) (K : AK I) (A : Finset (Fin m)) (c : Fin m) :
    I.toCSP.Config → Proc (Option I.toCSP.Config) :=
  loop fun x => do
    let h ← flip
    if h then do
      tick L'
      if I.toCSP.bad c x = false then pure (Sum.inr (some x)) else do
        tick ((m + 1) * L' ^ 3)
        match ← frExit I L L' K A (leafOf (frNext I L A c) c {c}) x with
        | none => pure (Sum.inr none)
        | some y => pure (Sum.inl y)
    else do
      match ← frGenerator I p L L' K A c with
      | none => pure (Sum.inr none)
      | some none => pure (Sum.inl x)
      | some (some t) =>
        if sign t = -1 then do
          match ← frEnter I L' K A t x with
          | none => pure (Sum.inr none)
          | some y =>
            match ← frRoute I L L' A c t y with
            | none => pure (Sum.inl y)
            | some t' =>
              match ← frExit I L L' K A t' y with
              | none => pure (Sum.inr none)
              | some z => pure (Sum.inl z)
        else pure (Sum.inl x)

/-- The reverse kernel `μ_{A∪{c}} → μ_A` of Lemma A.6 (p.23) with the rows of D.3 and the aborts of D.4. -/
noncomputable def frBackward (p : ℚ) (L L' : ℕ) (K : AK I) (A : Finset (Fin m)) (c : Fin m) :
    I.toCSP.Config → Proc (Option I.toCSP.Config) :=
  loop fun x => do
    let h ← flip
    if h then pure (Sum.inl x) else do
      match ← frGenerator I p L L' K A c with
      | none => pure (Sum.inr none)
      | some none => pure (Sum.inr (some x))
      | some (some t) =>
        if sign t = -1 then pure (Sum.inr (some x)) else do
          match ← frEnter I L' K A t x with
          | none => pure (Sum.inr none)
          | some y =>
            match ← frRoute I L L' A c t y with
            | none => pure (Sum.inl y)
            | some t' =>
              match ← frExit I L L' K A t' y with
              | none => pure (Sum.inr none)
              | some z => pure (Sum.inr (some z))

/-- The kernels at target-size level `k`; each insertion, deletion and coin invocation counts once. -/
noncomputable def frLevel (p : ℚ) (L L' : ℕ) : ℕ → AK I
  | 0 => ⟨fun _ _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ => 0⟩
  | k + 1 =>
    { insert := fun A c x => do
        countCall 1
        frForward I p L L' (frLevel p L L' k) A c x
      delete := fun A c x => do
        countCall 1
        frBackward I p L L' (frLevel p L L' k) A c x
      coin := frCoinAt I p L L' (frLevel p L L' k) }

/-- Sequential insertion in index order; an abort propagates. -/
noncomputable def frInsertAll (K : AK I) : List (Fin m) → I.toCSP.Config →
    Proc (Option I.toCSP.Config)
  | [], x => pure (some x)
  | i :: l, x => do
    match ← K.insert (rootSet i) i x with
    | none => pure none
    | some y => frInsertAll K l y

/-- The input length `N` of Theorem 5.4: the base `inputSize` of the instance (with zero witnesses), which
includes the encoding of `λ`. -/
def frInputSize : ℕ := I.inputSize fun _ => 0

/-- One sampling attempt of Theorem 5.4 (p.43): a draw from `λ`, then the sequential insertion of all `m`
constraints by the implemented kernels; `none` is a failure (an abort anywhere). -/
noncomputable def frAttempt (p : ℚ) (L : ℕ) : Proc (Option I.toCSP.Config) := do
  let x ← I.toCSP.drawAll
  frInsertAll I (frLevel I p L (frInputSize I + L + bits p) m) (List.finRange m) x

/-- Restarting the whole attempt after failure (p.43). -/
noncomputable def frRestart (p : ℚ) (L : ℕ) : Proc I.toCSP.Config :=
  loop (fun _ : Unit => do
    match ← frAttempt I p L with
    | none => pure (Sum.inl ())
    | some x => pure (Sum.inr x)) ()

/-! ## The deterministic counter of D.5 -/

/-- Charged sum of two coefficient lists of the same length. -/
noncomputable def polyAdd : List ℚ → List ℚ → Proc (List ℚ)
  | a :: f, b :: g => do
    let c ← qadd a b
    let r ← polyAdd f g
    pure (c :: r)
  | _, _ => pure []

/-- Charged product truncated to the first `q` coefficients. -/
noncomputable def polyMul (q : ℕ) (f g : List ℚ) : Proc (List ℚ) :=
  (List.range q).mapM fun k =>
    (List.range (k + 1)).foldlM (fun acc i => do
      let t ← qmul (f.getD i 0) (g.getD (k - i) 0)
      qadd acc t) 0

/-- `1` as a coefficient list of length `q` (`q ≥ 1`). -/
def polyOne (q : ℕ) : List ℚ := (List.range q).map fun k => if k = 0 then 1 else 0

/-- `(1 − g)^{-1} = Σ_{k<q} g^k`, truncated to `q` coefficients, for `g` with zero constant term. -/
noncomputable def polyGeom (q : ℕ) (g : List ℚ) : Proc (List ℚ) := do
  let (res, _) ← (List.range (q - 1)).foldlM (fun (st : List ℚ × List ℚ) _ => do
    let pw ← polyMul q st.2 g
    let res ← polyAdd st.1 pw
    pure (res, pw)) (polyOne q, polyOne q)
  pure res

/-- `c z^u f(z)` truncated to `q` coefficients, `f` given by its first `q − u` coefficients. -/
noncomputable def polyShift (q u : ℕ) (c : ℚ) (f : List ℚ) : Proc (List ℚ) :=
  (List.range q).mapM fun k => if k < u then pure 0 else qmul c (f.getD (k - u) 0)

/-- The coefficients of degrees `< q` of the series `f_i` of (47), p.44, for the task `i = (A, c)`:
`f_i(z) = Σ_{t ordinary} ε_t a_t z^{|Y_t|} ∏_{h≤ℓ_t} (1 − f_{j(t,h)}(z))^{-1}`. A record of cost
`|Y_t| ≥ q` contributes only degrees `≥ q`, and the children are needed to degree `< q − |Y_t|`, so the
recursion has depth below `L`; this is the expansion into evaluation trees of Lemma D.6, p.45. -/
noncomputable def coef (p : ℚ) (L L' : ℕ) : ℕ → ℕ → Finset (Fin m) → Fin m → Proc (List ℚ)
  | 0, q, _, _ => pure (List.replicate q 0)
  | k + 1, q, A, c => do
    let rs ← records I L L' A c (m + 1) ({c}, ∅)
    rs.foldlM (fun acc t =>
      if frontier L t ∨ q ≤ t.1.card then pure acc else do
        let u := t.1.card
        let a ← frA I t
        let pr ← (frChildren I A t).foldlM (fun pr j => do
          let g ← coef p L L' k (q - u) j.1 j.2
          let h ← polyGeom (q - u) g
          polyMul (q - u) pr h) (polyOne (q - u))
        let term ← polyShift q u ((sign t : ℚ) * a) pr
        polyAdd acc term) (List.replicate q 0)

/-- `r̂_i`, the sum of the coefficients of degrees `< L` of `f_i`, clipped to `[0, 2p]` (p.45). -/
noncomputable def rClip (p : ℚ) (L L' : ℕ) (A : Finset (Fin m)) (c : Fin m) : Proc ℚ := do
  let cs ← coef I p L L' L L A c
  let r ← cs.foldlM (fun acc x => qadd acc x) 0
  let twoP ← qmul 2 p
  let low ← qle r 0
  if low then pure 0 else do
    let high ← qle twoP r
    if high then pure twoP else pure r

/-- The deterministic estimate `Ẑ = ∏_{i=1}^m (1 − r̃_i)` along the insertion order (p.45). The procedure
draws no random bits. -/
noncomputable def frCount (p : ℚ) (L : ℕ) : Proc ℚ :=
  (List.finRange m).foldlM (fun acc i => do
    let r ← rClip I p L (frInputSize I + L + bits p) (rootSet i) i
    let f ← qsub 1 r
    qmul acc f) 1

end SamplingLLL.Supplement


