-- Prove2me | Definitions.Def_DIObliviousTransfer_IsExtractableStringCommitment
-- name    : DIObliviousTransfer_IsExtractableStringCommitment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:08:01.745547+00:00
-- url     : https://prove2.me/theorems/e7ff780b-abf4-45ab-a3fc-cf4fd4679ccc
-- title:
--   Extractable string commitment (Definition 9)
-- statement:
--   A **string commitment** to $u\in\mathbb F_2^q$ uses declared device batches. Its committer returns a public transcript $\tau$ and a polynomial-length native witness $w$; its receiver returns $\tau$; and it has a polynomial-time native-opening predicate $\mathrm{OpenVer}_{\mathrm{str}}(\tau,u,w)$. In either role assignment, uniformly over admissible auxiliary and reference states, it is **extractable** when:
--   1. *State-preserving extraction:* for every QPT committer, one QPT simulator outputs $u^*\in\mathbb F_2^q\cup\{\perp\}$ at completion, and without $u^*$ the joint state is indistinguishable from the real one.
--   2. *Agreement:* for the same simulator, $\Pr[\exists u,w:\mathrm{OpenVer}_{\mathrm{str}}(\tau,u,w)=1\wedge u\ne u^*]$ is negligible.
--   3. *Joint hiding:* commitments to any $u_0,u_1$ (with the label $(u_0,u_1)$) give indistinguishable receiver–reference views.
--   4. *Honest native witnesses:* against every receiver, on every continuing branch the honest committer's saved $w$ satisfies $\mathrm{OpenVer}_{\mathrm{str}}(\tau,u,w)=1$.
--
--   **CorrectAt** is honest correctness with negligible error at a given device noise.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), §2.7.1 and Definition 9, p.21

import Mathlib
import Definitions.Def_DIObliviousTransfer_Realizes

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §2.7.1 and
Definition 9, p.21.

"Fix a public length `1 ≤ q ≤ poly(λ)`. A string commitment to `u ∈ F₂^q` has a
completed-commitment public transcript `τ` and a polynomial-time native-opening predicate
`OpenVer_str(τ, u, w)`. … Definition 9 (Extractable string commitment). A correct string
commitment satisfies the following properties in either role assignment, uniformly over the
admissible auxiliary and reference states of Definition 5. (i) State-preserving extraction. For
every QPT committer, one QPT simulator returns `u∗ ∈ F₂^q ∪ {⊥}` at commitment completion.
Omitting this private output, its joint corrupt state, public transcript, honest retained
verification state, and untouched reference are computationally indistinguishable from the real
ones. (ii) Agreement with all native openings. For that same simulator,
`Pr_sim[∃u, w : OpenVer_str(τ, u, w) = 1 ∧ u ≠ u∗] ≤ ε_ao(λ) = negl(λ)`. (2) Every string
differs from `⊥`. (iii) Joint hiding. For every QPT receiver, commitments to any prescribed
`u₀, u₁ ∈ F₂^q` give computationally indistinguishable receiver–reference views through
commitment completion. The bound is uniform over these messages and admissible auxiliary states.
The comparison may retain a common classical label specifying both candidate messages … (iv)
Honest native witnesses. Against every receiver, on each continuing branch an honest committer
can compute `w` from its saved classical state with `OpenVer_str(τ, u, w) = 1`, without a further
device operation."

**Formalization Note** (decisions D4–D9). A string commitment declares its device batches and
gives the committer's controller (input `u`, a string of `q λ` bits; returns `pack [τ, w]`, its
saved transcript and native witness), the receiver's controller (returns its verification record
`τ`) and `OpenVer_λ`. Either party may be the committer. (i) is realization, against a corrupt
committer, of the extraction functionality, which takes `pack [τ, u∗]` from the simulator, keeps
`u∗` private (`none` is `⊥`) and delivers `τ` to the honest receiver; (ii) bounds, for the same
simulator, the probability that the functionality's final state has a transcript admitting a
native opening to some `u ≠ u∗`; (iii) compares the real experiments committing to `u₀` and `u₁`
with the common label `pack [u₀, u₁]` as honest input; (iv) is exact on every branch where the
honest committer continues. Honest correctness is stated separately (Theorem 15).
-/

/-- A string commitment with declared device batches. -/
structure StrCom where
  /-- The committer: input `u`; returns `pack [τ, w]`. -/
  commit : ℕ → Bits → Code (Option Bits)
  /-- The receiver: returns its verification record `τ`. -/
  receive : ℕ → Code (Option Bits)
  /-- The public native-opening predicate `OpenVer_str,λ(τ, u, w)`. -/
  OpenVer : ℕ → Bits → Bits → Bits → Bool
  nb : ℕ → ℕ
  ng : ℕ → ℕ
  group : ℕ → ℕ → ℕ
  coords : ℕ → ℕ → ℕ
  /-- Whether the committer's device answers rows in each batch. -/
  committerRows : ℕ → ℕ → Bool
  steps : ℕ → ℕ
  /-- A declared bound on the length of the native witness. -/
  wbound : ℕ → ℕ

namespace StrCom

/-- The commitment phase as a protocol, with Alice the committer (`cA = true`) or Bob. -/
def proto (S : StrCom) (cA : Bool) : Protocol where
  codeA := fun lam x => if cA then S.commit lam x else S.receive lam
  codeB := fun lam x => if cA then S.receive lam else S.commit lam x
  nb := S.nb
  ng := S.ng
  group := S.group
  coords := S.coords
  rowsA := fun lam b => if cA then S.committerRows lam b else !S.committerRows lam b
  steps := S.steps

/-- The hiding experiment: the committer's input is the label `pack [u₀, u₁]`; it commits to
`u_b` and outputs `∅`. -/
def hideProto (S : StrCom) (cA b : Bool) : Protocol :=
  let c : ℕ → Bits → Code (Option Bits) := fun lam x =>
    match unpack x with
    | [u0, u1] => Code.bind (S.commit lam (if b then u1 else u0)) fun
        | none => Code.ret none
        | some _ => Code.ret (some [])
    | _ => Code.ret none
  { S.proto cA with
    codeA := fun lam x => if cA then c lam x else S.receive lam
    codeB := fun lam x => if cA then S.receive lam else c lam x }

end StrCom

/-- The state of the extraction functionality. -/
structure ExtSt where
  lam : ℕ
  tau : Option Bits
  ustar : Option (Option Bits)
  done : Bool

/-- The extraction functionality of Definition 9 (i): the simulator submits
`pack [τ, encOpt u∗]`; `u∗` stays private; the receiver gets `τ`; `[true]` aborts. -/
def idealExt (cA : Bool) : Func where
  St := ExtSt
  init := fun lam _ => ⟨lam, none, none, false⟩
  step := fun st e =>
    if st.done then (st, []) else
    match e with
    | .adv m =>
      if m = [true] then ({ st with done := true }, [.party (!cA) none])
      else match unpack m with
        | [τ, us] =>
          let ust : Option (Option Bits) := some (if us.headD false then some us.tail else none)
          ({ st with tau := some τ, done := true, ustar := ust }, [.party (!cA) (some τ)])
        | _ => (st, [])
    | .party _ _ => (st, [])
  validA := fun _ => Set.univ
  validB := fun _ => Set.univ

/-- The bad event of (2) in the final state of the extraction functionality: the extracted
transcript admits a native opening to a string other than `u∗` (every string differs from `⊥`). -/
def extBad (S : StrCom) (st : ExtSt) : Prop :=
  ∃ τ us, st.tau = some τ ∧ st.ustar = some us ∧
    ∃ u w, S.OpenVer st.lam τ u w = true ∧ us ≠ some u

/-- **Definition 9** (extractable string commitment) for capacity `q λ` and window budgets `B`. -/
def IsExtractableStringCommitment (S : StrCom) (q : ℕ → ℕ) (B : ℕ → ℕ → ℕ) : Prop :=
  -- a polynomial-time native-opening predicate and polynomial-length witnesses (p.21)
  PolyTimeBits (fun x => match unpack x with
    | [l, τ, u, w] => [S.OpenVer l.length τ u w]
    | _ => []) ∧ PolyBound S.wbound ∧
  ∀ cA : Bool,
    -- (i) and (ii): state-preserving extraction, agreement with all native openings
    (∃ sim : (A : Adversary (S.proto cA)) → Simulator A,
      EmulatesWith (S.proto cA) trivialFunc idealProtocol (idealExt cA) (fun _ _ => true)
        (fun _ _ => Set.univ) (fun c => c = cA) B sim ∧
      ∀ A : Adversary (S.proto cA), A.corruptA = cA → A.IsQPT →
        ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ lam r η, IsState η → ∀ inp,
          idealStateProb (S.proto cA) idealProtocol (idealExt cA) (fun _ _ => true) B A (sim A)
            lam r η inp (extBad S) ≤ ε lam) ∧
    -- (iii) joint hiding against QPT receivers
    (∀ A : Adversary (S.hideProto cA false), A.corruptA = !cA → A.IsQPT →
      ∀ nR : ℕ → ℕ, PolyBound nR → ∀ D : TestFam A nR, D.IsQPT → ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ lam η, IsState η → ∀ u0 u1 : Bits, u0.length = q lam → u1.length = q lam →
          |testProb (D.D lam) (realExp (S.hideProto cA false) trivialFunc B A lam (nR lam) η
              (pack [u0, u1])) -
            testProb (D.D lam) (realExp (S.hideProto cA true) trivialFunc B
              ⟨A.corruptA, A.P, A.wM, A.M, A.d, A.dev, A.T, A.sched⟩ lam (nR lam) η
              (pack [u0, u1]))| ≤ ε lam) ∧
    -- (iv) honest native witnesses, against every receiver
    (∀ A : Adversary (S.proto cA), A.corruptA = !cA → ∀ lam r η, IsState η →
      ∀ u : Bits, u.length = q lam →
        realOutProb (S.proto cA) trivialFunc B A lam r η u
          (fun o => ∃ z, o = some z ∧ ¬ ∃ τ w, unpack z = [τ, w] ∧ S.OpenVer lam τ u w = true ∧
            w.length ≤ S.wbound lam) = 0)

open Classical in
/-- Honest correctness of a string commitment (the "correct string commitment" of Definition 9),
with honest devices of loss at most `q_dev` (3): in either role assignment and for every
`u ∈ F₂^q`, with probability at least `1 − ε(λ)` the committer outputs `pack [τ, w]`, the receiver
outputs the same `τ`, and `OpenVer_str(τ, u, w)` holds. -/
def StrCom.CorrectAt (S : StrCom) (q : ℕ → ℕ) (qd : ℝ) (ε : ℕ → ℝ) : Prop :=
  ∀ (cA : Bool) (Dv : HonestDevices), Dv.FaultLE qd → ∀ lam (u : Bits), u.length = q lam →
    1 - ε lam ≤ honestEventProb (S.proto cA) trivialFunc Dv lam (if cA then u else [])
      (if cA then [] else u) (fun o =>
        ∃ z τ w, (if cA then o.1 else o.2) = some z ∧ unpack z = [τ, w] ∧
          (if cA then o.2 else o.1) = some τ ∧ S.OpenVer lam τ u w = true)

end DIObliviousTransfer


