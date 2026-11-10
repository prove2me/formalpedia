-- Prove2me | Definitions.Def_CharonChurn_Main_Decision
-- name    : CharonChurn_Main_Decision
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:55:14.707329+00:00
-- url     : https://prove2.me/theorems/5ee2a3d7-0700-4e9b-9c9d-0f89e2d7a13a
-- title:
--   The Charon decision procedure on retained evidence (Eqs. (2)–(14), Algorithm 1)
-- statement:
--   The decision input is $n,D,t$, the active session, the target window $[s,e]$, an eligibility bit supplied by the execution model, and the validated retained cache. From it:
--   $R_i(q)$ = distinct signers of cached session-matching round-$q$ records (malformed included); $Q_i(u,q)$ = distinct well-formed round-$q$ payloads of $u$; $R^{\mathrm{uniq}}_i(q)$ = signers with $|Q_i(u,q)|=1$; $\chi^q_{u\to v}$ holds iff $u$ has a unique well-formed round-$q$ payload and it lists $v$; $w^q_i(v)=|\{u\in R^{\mathrm{uniq}}_i(q):\chi^q_{u\to v}\}|$; $W_i(q)=\{v:w^q_i(v)\ge t+1\}$; coverage is $|R_i(q)|\ge n-t$ for all $q\in[s,e]$; $\hat V=\bigcap_{q}W_i(q)$.
--   The initial forced suspects are $u\in\hat V$ having a target round with no unique well-formed report, an equivocation, a signature-verified malformed payload, or a unique report listing an identifier outside $W_i(q)$. Distinct $u,v$ conflict if in some target round $\chi^q_{u\to v}\ne\chi^q_{v\to u}$; the residual conflict graph lives on $\hat V\setminus S$. Closure repeatedly adds the least identity whose residual conflict degree exceeds $t-|S|$ (at most $|\hat V|$ steps, stopping immediately if $|S|>t$); $\mu_i=|S|$ after closure. The matching $M_i$ scans the residual conflict edges $(u,v)$, $u<v$, in lexicographic order and greedily keeps each edge with both endpoints unmatched; $q_i=|M_i|$; $F=S\cup V(M)$; $U=\hat V\setminus F$; $J$ joins distinct $u,v$ iff in every target round $\chi_{u\to v}\lor\chi_{v\to u}$ (its vertex set is $U$); $d^{\mathrm{out}}_F(f)=|\{u\in U:\chi^q_{u\to f}\ \forall q\}|$; $\alpha_i=t-\mu_i-q_i$, $\ell_i=t+\alpha_i$.
--   The verdict is Not Partitionable iff the eligibility bit is true, coverage holds, the initial and closed suspect sets have at most $t$ elements, $\mu_i+q_i\le t$, $\kappa(J[U])>\ell_i$ and $d^{\mathrm{out}}_F(f)>\ell_i$ for all $f\in F$; otherwise Partitionable. The same objects are also defined for an arbitrary set $F$, and a predicate states that a set of pairs is a maximal matching of a graph (pairs are edges, pairwise vertex-disjoint, every edge has a matched endpoint), for the analysis lemmas that speak of any maximal matching.
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), §§3.3–3.6, pp. 13–16, Eqs. (2)–(14); Algorithm 1, p. 17; §4.4, p. 27

import Mathlib
import Definitions.Def_CharonChurn_Main_Connectivity
import Definitions.Def_CharonChurn_Main_Reports

namespace CharonChurn.Main

/-! # The Charon decision procedure on a retained evidence cache
(Sengupta–Perrin 2026, §§3.3–3.6, pp. 13–16, Eqs. (2)–(14); Algorithm 1 lines 4–27, p. 17) -/

/-- The two possible outputs. -/
inductive Verdict where
  | partitionable
  | notPartitionable
  deriving DecidableEq

/-- Everything the decision procedure reads: public parameters `n, D, t`, the authenticated
execution context (active session `sid` and target window `[s, e]`), the eligibility bit
supplied by the execution model, and the validated retained evidence cache. -/
structure DecisionInput where
  n : ℕ
  D : ℕ
  t : ℕ
  sid : ℕ
  s : ℕ
  e : ℕ
  eligible : Bool
  cache : Finset Record

namespace DecisionInput

variable (I : DecisionInput)

/-- Target rounds `[s, e]`. -/
def window : Finset ℕ := Finset.Icc I.s I.e

/-- Cached records bound to the active session and original round `q`. -/
noncomputable def recs (q : ℕ) : Finset Record := by
  classical
  exact I.cache.filter (fun x => x.payload.sid = I.sid ∧ x.payload.round = q)

/-- `R_i(q)`: distinct signers with authenticated context-matching round-`q` evidence
(malformed payloads included). -/
noncomputable def R (q : ℕ) : Finset ℕ := by
  classical
  exact (I.recs q).image (fun x => x.payload.signer)

/-- `Q_i(u, q)`: distinct well-formed payloads of signer `u` for round `q`. -/
noncomputable def Q (u q : ℕ) : Finset Payload := by
  classical
  exact ((I.recs q).filter (fun x => x.payload.signer = u ∧ WellFormed I.D x.payload)).image
    (fun x => x.payload)

/-- A signature-verified malformed round-`q` payload of `u` is available. -/
def Malformed (u q : ℕ) : Prop :=
  ∃ x ∈ I.recs q, x.payload.signer = u ∧ ¬ WellFormed I.D x.payload

/-- `χ^q_{u→v}`: `u` has a unique well-formed round-`q` report and it lists `v`. -/
def chi (u v q : ℕ) : Prop :=
  (I.Q u q).card = 1 ∧ ∃ p ∈ I.Q u q, v ∈ p.nbrs

/-- `R^uniq_i(q)`: signers with exactly one distinct well-formed round-`q` payload. -/
noncomputable def Runiq (q : ℕ) : Finset ℕ := by
  classical
  exact (I.R q).filter (fun u => (I.Q u q).card = 1)

/-- Support `w^q_i(v)`, Eq. (2): unique-report signers listing `v`, one per identity. -/
noncomputable def w (q v : ℕ) : ℕ := by
  classical
  exact ((I.Runiq q).filter (fun u => I.chi u v q)).card

/-- `W_i(q) = {v : w^q_i(v) ≥ t + 1}`, Eq. (3) (a vertex of positive support is listed in some
cached payload, so the filter ranges over all candidates). -/
noncomputable def W (q : ℕ) : Finset ℕ := by
  classical
  exact ((I.recs q).biUnion (fun x => x.payload.nbrs.toFinset)).filter
    (fun v => I.t + 1 ≤ I.w q v)

/-- Evidence coverage, Eq. (4): `|R_i(q)| ≥ n − t` for every target round. -/
def Coverage : Prop := ∀ q ∈ I.window, (I.n : ℤ) - I.t ≤ ((I.R q).card : ℤ)

/-- Reconstructed persistent vertex set `V̂ = ⋂_{q ∈ [s,e]} W_i(q)`, Eq. (5). -/
noncomputable def Vhat : Finset ℕ := by
  classical
  exact (I.W I.s).filter (fun v => ∀ q ∈ I.window, v ∈ I.W q)

/-- Initial forced suspects (§3.4, rules 1–4): some target round has no unique well-formed
report, an equivocation, a signature-verified malformed report, or a unique report listing an
identifier outside `W_i(q)`. -/
noncomputable def S0 : Finset ℕ := by
  classical
  exact I.Vhat.filter (fun u => ∃ q ∈ I.window,
    (I.Q u q).card ≠ 1 ∨ I.Malformed u q ∨ ((I.Q u q).card = 1 ∧ ∃ x, I.chi u x q ∧ x ∉ I.W q))

/-- Report conflict, Eq. (6): in some target round the unique reports of `u` and `v` disagree
about their adjacency. -/
def Conflict (u v : ℕ) : Prop :=
  u ≠ v ∧ ∃ q ∈ I.window, ¬ (I.chi u v q ↔ I.chi v u q)

/-- Residual conflict graph `C[V̂ \ S]`. -/
def conflictGraph (S : Finset ℕ) : SimpleGraph ℕ where
  Adj u v := u ∈ I.Vhat \ S ∧ v ∈ I.Vhat \ S ∧ I.Conflict u v
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm, by
    obtain ⟨q, hq, hne⟩ := h.2.2.2
    exact ⟨q, hq, fun hiff => hne hiff.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- One step of the degree-based closure, Eq. (7): add the least residual identity whose residual
conflict degree exceeds `t − |S|` (if any), stopping immediately when `|S| > t`. -/
noncomputable def closureStep (S : Finset ℕ) : Finset ℕ := by
  classical
  let cand := (I.Vhat \ S).filter (fun u =>
    (I.t : ℤ) - S.card < (((I.Vhat \ S).filter (fun v => I.Conflict u v)).card : ℤ))
  exact if I.t < S.card then S else
    if h : cand.Nonempty then insert (cand.min' h) S else S

/-- Final forced-suspect set `S` after closure (at most `|V̂|` productive steps). -/
noncomputable def S : Finset ℕ := (I.closureStep)^[I.Vhat.card] I.S0

/-- `μ_i = |S|` after closure. -/
noncomputable def mu : ℕ := I.S.card

/-- Edges of the residual conflict graph as ordered pairs `(u, v)` with `u < v`, in
lexicographic order. -/
noncomputable def conflictEdges : List (ℕ × ℕ) := by
  classical
  exact ((((I.Vhat \ I.S) ×ˢ (I.Vhat \ I.S)).filter
      (fun p => p.1 < p.2 ∧ I.Conflict p.1 p.2)).toList).mergeSort
    (fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)))

/-- Deterministic maximal matching: scan the edges lexicographically and greedily keep each edge
whose endpoints are both unmatched. -/
noncomputable def matchingList : List (ℕ × ℕ) :=
  I.conflictEdges.foldl (fun M p =>
    if (M.all (fun x => x.1 ≠ p.1 && x.1 ≠ p.2 && x.2 ≠ p.1 && x.2 ≠ p.2)) then M ++ [p] else M) []

/-- The matching `M_i` as a finite set of pairs. -/
noncomputable def M : Finset (ℕ × ℕ) := by
  classical
  exact I.matchingList.toFinset

/-- `q_i = |M_i|`. -/
noncomputable def qM : ℕ := I.matchingList.length

/-- Endpoints `V(M)` of a set of pairs. -/
noncomputable def endpoints (M : Finset (ℕ × ℕ)) : Finset ℕ := by
  classical
  exact M.biUnion (fun p => {p.1, p.2})

/-- Relaxed suspect set `F = S ∪ V(M)` for a matching `M`, Eq. (8). -/
noncomputable def Fof (M : Finset (ℕ × ℕ)) : Finset ℕ := by
  classical
  exact I.S ∪ endpoints M

/-- Charon's relaxed cover `F_i`. -/
noncomputable def F : Finset ℕ := I.Fof I.M

/-- Unflagged core `U = V̂ \ F`. -/
noncomputable def U (F : Finset ℕ) : Finset ℕ := by
  classical
  exact I.Vhat \ F

/-- Core graph `J`, Eqs. (11)–(12): distinct `u, v` adjacent iff in every target round at least
one of them reports the other. Its vertex set is `U`. -/
def J : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ∀ q ∈ I.window, I.chi u v q ∨ I.chi v u q
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun q hq => (h.2 q hq).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Reported persistent external degree into the core, Eq. (13): core vertices whose reports
list `f` in every target round. -/
noncomputable def dout (F : Finset ℕ) (f : ℕ) : ℕ := by
  classical
  exact ((I.U F).filter (fun u => ∀ q ∈ I.window, I.chi u f q)).card

/-- Slack `α_i = t − μ_i − q_i` (natural subtraction, used only after the budget guard). -/
noncomputable def alpha : ℕ := I.t - I.mu - I.qM

/-- Core threshold `ℓ_i = t + α_i`. -/
noncomputable def ell : ℕ := I.t + I.alpha

/-- All guards pass: eligibility, coverage, forced-suspect guard before and after closure, and
the matching-budget guard `μ + q ≤ t`. -/
def GuardsPass : Prop :=
  I.eligible = true ∧ I.Coverage ∧ I.S0.card ≤ I.t ∧ I.S.card ≤ I.t ∧ I.mu + I.qM ≤ I.t

/-- Structural test, Eq. (14): `κ(J) > ℓ` and `d_out_F(f) > ℓ` for every `f ∈ F`. -/
def StructuralPass : Prop :=
  I.ell < kappa I.J (I.U I.F) ∧ ∀ f ∈ I.F, I.ell < I.dout I.F f

/-- Charon's decision: `Not Partitionable` iff all guards and both structural tests pass;
otherwise (fallback or structural failure) `Partitionable`. -/
noncomputable def verdict : Verdict := by
  classical
  exact if I.GuardsPass ∧ I.StructuralPass then Verdict.notPartitionable else Verdict.partitionable

end DecisionInput

/-- `M` is a maximal matching of the graph `C` (pairs are edges of `C`, pairwise vertex-disjoint,
and every edge of `C` has a matched endpoint). -/
def IsMaximalMatching (C : SimpleGraph ℕ) (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ M, C.Adj p.1 p.2) ∧
  (∀ p ∈ M, ∀ p' ∈ M, p ≠ p' →
    p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2) ∧
  (∀ u v, C.Adj u v → ∃ p ∈ M, u = p.1 ∨ u = p.2 ∨ v = p.1 ∨ v = p.2)

end CharonChurn.Main


