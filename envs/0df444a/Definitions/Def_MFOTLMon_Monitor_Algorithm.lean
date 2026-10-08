-- Prove2me | Definitions.Def_MFOTLMon_Monitor_Algorithm
-- name    : MFOTLMon_Monitor_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:46.550232+00:00
-- url     : https://prove2.me/theorems/0090be15-54e4-4e89-a76c-fa472000f5af
-- title:
--   Fig. 2 and §3.6, pp. 15:15–15:16 — the monitor M_Φ as a state machine: waitfor, update, the list Q, the store of D̂ⱼ, lines 1–13 and its run
-- statement:
--   This file formalizes the monitoring algorithm $\mathsf M_\Phi$ of Fig. 2 as a state machine.
--
--   **Auxiliary functions** (p. 15:16). $\mathit{waitfor}(\alpha)$ is $\mathit{waitfor}(\beta)$ for $\alpha=\neg\beta,\exists x.\beta,\bullet_I\beta$; $\mathit{waitfor}(\beta)\cup\mathit{waitfor}(\gamma)$ for $\alpha=\beta\vee\gamma,\beta\,\mathsf S_I\,\gamma$; $\{\alpha\}$ for $\alpha=\circ_I\beta,\beta\,\mathsf U_I\,\gamma$; and $\emptyset$ otherwise. For a set $U$ of formulas and $t\in\mathbb N$,
--   $$
--   \mathit{update}(U,t)=\{\beta\mid\circ_I\beta\in U\}\cup\{\beta\,\mathsf U_{[\max\{0,b-t\},b'-t)}\,\gamma\mid\beta\,\mathsf U_{[b,b')}\,\gamma\in U,\ b'-t>0\}\cup\{\beta\mid\beta\,\mathsf U_{[b,b')}\,\gamma\in U\text{ or }\gamma\,\mathsf U_{[b,b')}\,\beta\in U,\ b'-t\le0\}.
--   $$
--
--   **State.** Counters $\ell$ and $i$; the list $Q$ of triples $(\alpha,j,S)$; a **store** holding the relations of the extended structures $\hat{\mathcal D}_j$ built so far and not discarded (the relations of $\mathcal D_j$ carried over, and $p_\alpha^{\hat{\mathcal D}_j}$, $r_\alpha^{\hat{\mathcal D}_j}$, $s_\alpha^{\hat{\mathcal D}_j}$); and the log of outputs $(i,O,\tau_i)$.
--
--   **One loop iteration** (lines 5–13). (5) Carry over the relations of $\mathcal D_\ell$ to $\hat{\mathcal D}_\ell$. (6–7) For every $(\alpha,j,\emptyset)\in Q$, in order of increasing size of $\alpha$ and then increasing $j$ (footnote 1), build $p_\alpha^{\hat{\mathcal D}_j}$ (and $r_\alpha^{\hat{\mathcal D}_j}$, $s_\alpha^{\hat{\mathcal D}_j}$) by the construction of §3.4 for $\alpha$'s main connective, applied to relations read from the store; if an input relation is not in the store, nothing is built. (8–11) While $\hat{\mathcal D}_i$ is complete (all relations needed to evaluate $\hat\Phi$ at $i$ are stored), output $(\neg\hat\Phi)^{\hat{\mathcal D}_i}$, computed from the store, together with $\tau_i$; if $i>0$ discard $\hat{\mathcal D}_{i-1}$; increment $i$. (12) Replace $Q$ by
--   $$
--   \{(\alpha,\ell+1,\mathit{waitfor}(\alpha))\mid\alpha\text{ temporal subformula of }\Phi\}\cup\{(\alpha,j,\textstyle\bigcup_{\alpha'\in\mathit{update}(S,\tau_{\ell+1}-\tau_\ell)}\mathit{waitfor}(\alpha'))\mid(\alpha,j,S)\in Q,\ S\ne\emptyset\}.
--   $$
--   (13) Increment $\ell$. Initially (lines 1–3) $\ell=i=0$, $Q=\{(\alpha,0,\mathit{waitfor}(\alpha))\}$, and nothing is stored or output.
--
--   `run D Φ k` is the state when entering the $(k+1)$st loop iteration, so its $Q$, $i$ and $\ell$ are the $Q_k$, $i_k$, $\ell_k=k$ of the proof of Theorem 3.9.
--
--   **Formalization Note.** The monitor never refers to the semantics $\models$ or to satisfying sets: its outputs and builds are computed from the store with the first-order evaluation of $\hat\varphi$ and the §3.4 construction functions. It reads the input $(\mathcal D_\ell,\tau_\ell)$ through the structure: relations only at line 5, constants (rigid) directly, and time stamps as a function (line 12 uses $\tau_{\ell+1}$; the until construction at $j$ uses the lookahead $\ell_j$, which depends on $\tau$ up to $\tau_{j+\ell_j+1}$, already read when the build happens). Sets of formulas are lists, as in footnote 1; line 6's order is a linear extension of the footnote's partial order. The while loop is run with fuel $\ell+2$, which is never exhausted: completeness of $\hat{\mathcal D}_i$ requires the relations of $\mathcal D_i$, which are stored only for $i\le\ell$ (the predicate set is nonempty under the hypothesis that $\prec\in R$). "Discard $\hat{\mathcal D}_{i-1}$" removes every stored relation at time point $i-1$. The algorithm's output relations are represented as sets; the automata that represent them are not modelled.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), pp. 15:15–15:16, Fig. 2 (monitoring algorithm M_Φ), §3.6, waitfor and update, footnote 1

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Constructions

namespace MFOTLMon.Monitor

noncomputable section

open Classical

variable {S : Signature}

/-- The shifted interval `[max{0, b − t}, b′ − t)` of `update` (p. 15:16), defined when
`b′ − t > 0`, i.e. `t < b′`. -/
def Interval.shift (I : Interval) (t : ℕ) (h : (t : ℕ∞) < I.hi) : Interval where
  lo := I.lo - t
  hi := I.hi - t
  lo_lt_hi := by
    obtain ⟨lo, hi, hlt⟩ := I
    induction hi using ENat.recTopCoe with
    | top =>
      show ((lo - t : ℕ) : ℕ∞) < ⊤ - (t : ℕ∞)
      rw [ENat.top_sub_natCast]
      exact ENat.natCast_lt_top _
    | coe n =>
      show ((lo - t : ℕ) : ℕ∞) < (n : ℕ∞) - (t : ℕ∞)
      simp only [Nat.cast_lt] at h hlt
      rw [← ENat.natCast_sub, Nat.cast_lt]
      omega

/-- `waitfor(α)` (p. 15:16): the future subformulas that delay the evaluation of `α`. -/
def waitfor : Formula S → List (Formula S)
  | .neg β => waitfor β
  | .ex _ β => waitfor β
  | .prev _ β => waitfor β
  | .or β γ => waitfor β ++ waitfor γ
  | .since _ β γ => waitfor β ++ waitfor γ
  | .next I β => [.next I β]
  | .until I β γ => [.until I β γ]
  | .eq _ _ => []
  | .pred _ _ => []

/-- `update(U, t)` (p. 15:16): `{β | ○_I β ∈ U} ∪ {β U_{[max{0,b−t}, b′−t)} γ | β U_{[b,b′)} γ ∈ U,
b′ − t > 0} ∪ {β | β U_{[b,b′)} γ ∈ U or γ U_{[b,b′)} β ∈ U, with b′ − t ≤ 0}` (sets as lists). -/
def update (U : List (Formula S)) (t : ℕ) : List (Formula S) :=
  U.flatMap fun φ => match φ with
    | .next _ β => [β]
    | .until I β γ => if h : (t : ℕ∞) < I.hi then [.until (I.shift t h) β γ] else [β, γ]
    | _ => []

/-- Keys of the monitor's store: the relation `r^{D̂ⱼ}` of a predicate `r ∈ R` carried over from
`Dⱼ`, and the auxiliary relations `p_α^{D̂ⱼ}`, `r_α^{D̂ⱼ}`, `s_α^{D̂ⱼ}`. -/
inductive Key (S : Signature) where
  | base : S.R → Key S
  | p : Formula S → Key S
  | r : Formula S → Key S
  | s : Formula S → Key S

/-- The monitor's store of built relations: `store k j = some X` iff the relation `k` of `D̂ⱼ` has
been built (or carried over), with value `X`, and not discarded. -/
abbrev Store (S : Signature) := Key S → ℕ → Option (Set (List ℕ))

/-- Write the relation `k` of `D̂ⱼ`. -/
def Store.set (st : Store S) (k : Key S) (j : ℕ) (X : Set (List ℕ)) : Store S :=
  fun k' j' => if k' = k ∧ j' = j then some X else st k' j'

/-- Discard `D̂ⱼ`: every relation at time point `j`. -/
def Store.discard (st : Store S) (j : ℕ) : Store S :=
  fun k j' => if j' = j then none else st k j'

/-- The state of `M_Φ` (Fig. 2, p. 15:15) on entering a loop iteration: the counters `ℓ` and `i`,
the list `Q` of triples `(α, j, S)`, the store of the extended structures `D̂ⱼ` built so far and not
discarded, and the log `out` of every `(i, (¬Φ̂)^{D̂ᵢ}, τᵢ)` output by line 9 so far. -/
structure State (S : Signature) where
  ell : ℕ
  i : ℕ
  Q : List (Formula S × ℕ × List (Formula S))
  store : Store S
  out : List (ℕ × Set (List ℕ) × ℕ)

/-- `φ̂^{D̂ⱼ}` computed from the store alone: defined (`some`) only if the relations of `Dⱼ` carried
over to `D̂ⱼ` and the auxiliary relations `p_ψ^{D̂ⱼ}`, `ψ ∈ tsub(φ)`, are all present. -/
def hatAt (D : TempStruct S) (st : Store S) (j : ℕ) (φ : Formula S) : Option (Set (List ℕ)) :=
  if (∀ r, (st (.base r) j).isSome) ∧ (∀ ψ ∈ tsub φ, (st (.p ψ) j).isSome) then
    some (hatSet (fun r => (st (.base r) j).getD ∅) D.const (fun ψ => (st (.p ψ) j).getD ∅) φ)
  else none

/-- Line 7 of `M_Φ` for the triple `(α, j, ∅)`: build `p_α^{D̂ⱼ}` (and `r_α^{D̂ⱼ}`, `s_α^{D̂ⱼ}`)
by the constructions of §3.4, applied to relations read from the store. If an input is missing the
store is left unchanged (nothing is built). -/
def build (D : TempStruct S) (st : Store S) (e : Formula S × ℕ) : Store S :=
  let α := e.1
  let j := e.2
  match α with
  | .prev I β =>
      if j = 0 then st.set (.p α) j (prevP D.τ I j ∅) else
      match hatAt D st (j - 1) β with
      | some B => st.set (.p α) j (prevP D.τ I j B)
      | none => st
  | .next I β =>
      match hatAt D st (j + 1) β with
      | some B => st.set (.p α) j (nextP D.τ I j B)
      | none => st
  | .since I β γ =>
      match hatAt D st j β, hatAt D st j γ, (if j = 0 then some ∅ else st (.r α) (j - 1)) with
      | some B, some G, some R =>
          let r := sinceStep D.τ I j B G R
          (st.set (.r α) j r).set (.p α) j (sinceP I r)
      | _, _, _ => st
  | .until I β γ =>
      let ℓ := lookahead D I.hi.toNat j
      let ℓp := prevLookahead D I.hi.toNat j
      if (∀ k, ℓp ≤ k → k ≤ ℓ →
            (hatAt D st (j + k) β).isSome ∧ (hatAt D st (j + k) γ).isSome) ∧
          (j = 0 ∨ ((st (.r α) (j - 1)).isSome ∧ (st (.s α) (j - 1)).isSome)) then
        let rs := untilStep D I j (fun m => (hatAt D st m β).getD ∅)
          (fun m => (hatAt D st m γ).getD ∅) ((st (.r α) (j - 1)).getD ∅)
          ((st (.s α) (j - 1)).getD ∅)
        ((st.set (.r α) j rs.1).set (.s α) j rs.2).set (.p α) j (untilP rs.2)
      else st
  | _ => st

/-- Lines 5–7: carry over the relations of `D_ℓ` to `D̂_ℓ` (constants are rigid and read from `D`),
then build, for every `(α, j, ∅) ∈ Q`, the auxiliary relations of `α` at `j`, processing the triples
by increasing size of `α` and then increasing `j` (footnote 1, p. 15:16). -/
def afterBuild (D : TempStruct S) (s : State S) : State S :=
  let st1 : Store S := fun k j => match k with
    | .base r => if j = s.ell then some (D.rel s.ell r) else s.store (.base r) j
    | k => s.store k j
  let ready : List (Formula S × ℕ) :=
    ((s.Q.filter fun e => e.2.2.isEmpty).map fun e => (e.1, e.2.1)).mergeSort
      fun a b => decide (a.1.size < b.1.size ∨ (a.1.size = b.1.size ∧ a.2 ≤ b.2))
  { s with store := ready.foldl (build D) st1 }

/-- `D̂ᵢ` is complete: all relations of `D̂ᵢ` needed to evaluate `Φ̂` are present in the store. -/
def Complete (Φ : Formula S) (st : Store S) (i : ℕ) : Prop :=
  (∀ r, (st (.base r) i).isSome) ∧ ∀ α ∈ tempSubs Φ, (st (.p α) i).isSome

/-- Lines 8–11, the while loop, with `fuel` bounding the number of passes: while `D̂ᵢ` is complete,
output `((¬Φ̂)^{D̂ᵢ}, τᵢ)` (computed from the store), discard `D̂_{i−1}` if `i > 0`, and increment `i`.
The monitor calls it with fuel `ℓ + 2`, which is never exhausted: completeness of `D̂ᵢ` needs the
carried-over relations of `Dᵢ`, which exist only for `i ≤ ℓ`. -/
def evalLoop (D : TempStruct S) (Φ : Formula S) : ℕ → State S → State S
  | 0, s => s
  | n + 1, s =>
      if Complete Φ s.store s.i then
        let O := hatSet (fun r => (s.store (.base r) s.i).getD ∅) D.const
          (fun α => (s.store (.p α) s.i).getD ∅) (.neg Φ)
        let st' := if 0 < s.i then s.store.discard (s.i - 1) else s.store
        evalLoop D Φ n { s with out := s.out ++ [(s.i, O, D.τ s.i)], store := st', i := s.i + 1 }
      else s

/-- Line 12: `Q ← {(α, ℓ + 1, waitfor(α)) | α temporal subformula of Φ} ∪
{(α, j, ⋃_{α′ ∈ update(S, τ_{ℓ+1} − τ_ℓ)} waitfor(α′)) | (α, j, S) ∈ Q, S ≠ ∅}`. -/
def updateQ (D : TempStruct S) (Φ : Formula S) (s : State S) :
    List (Formula S × ℕ × List (Formula S)) :=
  s.Q.filterMap (fun e => if e.2.2.isEmpty then none else
      some (e.1, e.2.1, (update e.2.2 (D.τ (s.ell + 1) - D.τ s.ell)).flatMap waitfor)) ++
    (tempSubs Φ).map fun α => (α, s.ell + 1, waitfor α)

/-- One iteration of the loop of `M_Φ` (lines 5–13 of Fig. 2, p. 15:15). -/
def iteration (D : TempStruct S) (Φ : Formula S) (s : State S) : State S :=
  let s1 := evalLoop D Φ (s.ell + 2) (afterBuild D s)
  { s1 with Q := updateQ D Φ s1, ell := s1.ell + 1 }

/-- The initial state (lines 1–3): `ℓ = 0`, `i = 0`, `Q = {(α, 0, waitfor(α)) | α temporal
subformula of Φ}`, empty store, nothing output. -/
def init (Φ : Formula S) : State S :=
  { ell := 0, i := 0, Q := (tempSubs Φ).map fun α => (α, 0, waitfor α),
    store := fun _ _ => none, out := [] }

/-- `run D Φ k`: the state of `M_Φ` on input `(D₀, τ₀), (D₁, τ₁), …` when entering the `(k+1)`st loop
iteration (so `Q_k = (run D Φ k).Q`, `i_k = (run D Φ k).i`, `ℓ_k = (run D Φ k).ell = k`, as in the
proof of Theorem 3.9, p. 15:16). -/
def run (D : TempStruct S) (Φ : Formula S) (k : ℕ) : State S :=
  (iteration D Φ)^[k] (init Φ)

end

end MFOTLMon.Monitor


