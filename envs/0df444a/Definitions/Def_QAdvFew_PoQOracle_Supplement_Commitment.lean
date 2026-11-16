-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_Commitment
-- name    : QAdvFew_PoQOracle_Supplement_Commitment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:21:59.025538+00:00
-- url     : https://prove2.me/theorems/1440becf-8a6c-4a7e-a517-c6e04fe897e3
-- title:
--   Commitments with a classical committer and a quantum receiver
-- statement:
--   A **statistically sum-binding, computationally hiding commitment with a classical committer and a quantum receiver** (Definition B.1) consists of four algorithms $(\mathrm{Com},\mathrm{Rec},\mathrm{Open},\mathrm{Ver})$. In the commit phase $(\mathrm{st},\rho)\leftarrow\langle\mathrm{Com}(1^n,b),\mathrm{Rec}(1^n)\rangle$ with $\mathrm{Com}$ PPT, $\mathrm{Rec}$ QPT and classical communication; $\mathrm{st}$ is classical and $\rho$ may be quantum. In the opening phase the PPT algorithm $\mathrm{Open}(\mathrm{st})$ outputs $(b,d)$ and the QPT algorithm $\mathrm{Ver}(\rho,b,d)$ accepts or rejects. It requires:
--
--   1. **Correctness.** For each $b$, an honest opening to $b$ is accepted with probability at least $1-\mathrm{negl}(n)$.
--   2. **Computational hiding.** The final views of every nonuniform QPT receiver interacting with $\mathrm{Com}(1^n,0)$ and with $\mathrm{Com}(1^n,1)$ are computationally indistinguishable.
--   3. **Statistical sum-binding.** For every computationally unbounded committer $C$ that interacts with the honest receiver, then receives an independent uniform bit $b'$ and outputs an opening $d$, there is a negligible $\eta_C$ with
--   $$
--   \Pr[\mathrm{Ver}(\rho,b',d)=1]\le\tfrac12+\eta_C(n) ;
--   $$
--   if no opening string is provided, the receiver rejects.
--
--   **Formalization Note** PPT algorithms are polynomial-time functions of their input and polynomially many random coins. An unbounded committer is described by the conditional laws of its messages and of its opening, which is all the receiver can observe through classical communication. The distinguisher of the hiding experiment is part of the receiver, which outputs a bit. The opening has a fixed polynomial length.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition B.1, pp. 52–53 (PDF pp. 54–55)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_PlainQ
import Definitions.Def_QAdvFew_PoQOracle_Supplement_IParty
import Definitions.Def_QAdvFew_PoQOracle_Negligible

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- A candidate **commitment with a classical committer and a quantum receiver**, in the plain model
(Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definition B.1, pp. 52–53 (PDF pp. 54–55): "four algorithms `(Com, Rec, Open, Ver)` … In the
commit phase, the parties interact as follows: `(st, ρ) ← ⟨Com(1^n, b), Rec(1^n)⟩`, where Com is
PPT, Rec is QPT, and all communication is classical. The committer's output `st` is classical,
whereas the receiver's output `ρ` may be quantum. In the opening phase, the PPT algorithm `Open(st)`
outputs a single classical message `(b, d)`, where `b` is the original input bit. The QPT algorithm
`Ver(ρ, b, d)` accepts or rejects"):

* the commit phase has `M(n)` messages of length `ℓ(n)`, the committer sending message `0` iff
  `comFirst`;
* `Com` draws `ρ(n)` coins `r`; its message is `com (tup [1^n, b, r, earlier messages])` (zero-padded
  or cut to `ℓ(n)` bits) and `st = st (tup [1^n, b, r, all messages])`;
* `Open(st)` draws `ρo(n)` coins `r'` and outputs `d = opn (tup [st, r'])` (cut or padded to
  `ℓd(n)` bits) together with `b`;
* `Rec` is a QPT party (`IParty`) and `Ver` a circuit family acting on the receiver's final register,
  the bit `b`, the opening `d` and `vanc n` ancillas, with output wire `vout n`.

**Formalization Note** PPT algorithms are polynomial-time computable functions of their input and a
polynomial number of uniformly random coins. The opening string has a fixed polynomial length
`ℓd(n)`: a polynomial-time `Ver` reads at most polynomially many of its bits. -/
structure Commitment where
  M : Polynomial ℕ
  ℓ : Polynomial ℕ
  comFirst : Bool
  ρ : Polynomial ℕ
  com : Str → Str
  st : Str → Str
  ρo : Polynomial ℕ
  ℓd : Polynomial ℕ
  opn : Str → Str
  recv : IParty ar0 (fun n => ℓ.eval n)
  vanc : ℕ → ℕ
  ver : (n : ℕ) → UCirc ar0 ((2 * ℓ.eval n + 1 + recv.W n) + 1 + ℓd.eval n + vanc n + 1)
  vout : (n : ℕ) → Fin ((2 * ℓ.eval n + 1 + recv.W n) + 1 + ℓd.eval n + vanc n + 1)

/-- An **unbounded committer** (Definition B.1, statistical sum-binding: "any computationally
unbounded adversarial committer `C` that interacts with the honest receiver in the commit phase
and retains a private state `σ`. After this phase, sample an independent uniform bit `b'`, and let
`C`, given `σ` and `b'`, output an opening string `d`"), described by what the receiver can see: the
law of its message `j` given the earlier messages, and the law of its opening (`none`: no opening
string) given the transcript and `b'`.

**Formalization Note** Communication is classical, so a quantum unbounded committer's private
state is never entangled with the receiver; every such committer induces exactly such kernels and
every family of kernels is realized by one. -/
structure UnbCommitter (Cm : Commitment) where
  next : (n j : ℕ) → List Str → PMF (Msg (Cm.ℓ.eval n))
  opening : (n : ℕ) → ITranscript (Cm.M.eval n) (Cm.ℓ.eval n) → Bool →
    PMF (Option (Msg (Cm.ℓd.eval n)))

namespace Commitment

variable (Cm : Commitment)

/-- The committer sends message `j`. -/
def comSends (j : ℕ) : Bool := decide (j % 2 = 0) == Cm.comFirst

/-- The messages of `τ` before message `j`, as strings. -/
def before {n : ℕ} (τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n)) (j : ℕ) : List Str :=
  ((List.finRange (Cm.M.eval n)).filter (fun i : Fin (Cm.M.eval n) => (i : ℕ) < j)).map (fun i => toStr (τ i))

/-- The honest committer with input bit `b` and coins `r` sends exactly its messages of `τ`. -/
def Consistent (n : ℕ) (b : Bool) (r : Bits (Cm.ρ.eval n))
    (τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n)) : Prop :=
  ∀ j : Fin (Cm.M.eval n), Cm.comSends j = true →
    τ j = padTo (Cm.ℓ.eval n) (Cm.com (tup ([unary n, [b], toStr r] ++ Cm.before τ j)))

/-- The committer's classical output `st`. -/
def stOf (n : ℕ) (b : Bool) (r : Bits (Cm.ρ.eval n))
    (τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n)) : Str :=
  Cm.st (tup ([unary n, [b], toStr r] ++ Cm.before τ (Cm.M.eval n)))

/-- The honest opening `d` from `st` and the coins `r'` of `Open`. -/
def openOf (n : ℕ) (b : Bool) (r : Bits (Cm.ρ.eval n))
    (τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n)) (r' : Bits (Cm.ρo.eval n)) :
    Msg (Cm.ℓd.eval n) :=
  padTo (Cm.ℓd.eval n) (Cm.opn (tup [Cm.stOf n b r τ, toStr r']))

/-- The honest receiver's unnormalized final state after the transcript `τ` (its squared norm is the
receiver's likelihood of `τ`). -/
noncomputable def recState (n : ℕ) (τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n)) :
    QState (2 * Cm.ℓ.eval n + 1 + Cm.recv.W n) :=
  Cm.recv.finalState O0 C0 n (!Cm.comFirst) τ false

/-- `Ver(ρ, b, d)` accepts, for the receiver's unnormalized state `ψ`: the probability (times
`‖ψ‖²`) that the output wire reads `1` on `ψ ⊗ |b⟩ ⊗ |d⟩ ⊗ |0…0⟩`. -/
noncomputable def verAcc (n : ℕ) (ψ : QState (2 * Cm.ℓ.eval n + 1 + Cm.recv.W n)) (b : Bool)
    (d : Msg (Cm.ℓd.eval n)) : ℝ :=
  probOne ((Cm.ver n).run O0 C0
    (tensorState (tensorState (tensorState (tensorState ψ (basisState fun _ => b)) (basisState d))
      (basisState fun _ => false)) (basisState fun _ => false))) (Cm.vout n)

open Classical in
/-- Correctness: the probability that an honest opening to `b` is accepted. -/
noncomputable def honestProb (n : ℕ) (b : Bool) : ℝ :=
  ∑ τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n), ∑ r : Bits (Cm.ρ.eval n),
    ∑ r' : Bits (Cm.ρo.eval n),
      ((2 : ℝ) ^ (Cm.ρ.eval n))⁻¹ * ((2 : ℝ) ^ (Cm.ρo.eval n))⁻¹ *
        (if Cm.Consistent n b r τ then 1 else 0) * Cm.verAcc n (Cm.recState n τ) b (Cm.openOf n b r τ r')

open Classical in
/-- Hiding: the probability that a receiver `R*` outputs `1` (its input/output wire) after the commit
phase with `Com(1^n, b)`. -/
noncomputable def hideProb (R : IParty ar0 (fun n => Cm.ℓ.eval n)) (n : ℕ) (b : Bool) : ℝ :=
  ∑ τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n), ∑ r : Bits (Cm.ρ.eval n),
    ((2 : ℝ) ^ (Cm.ρ.eval n))⁻¹ * (if Cm.Consistent n b r τ then 1 else 0) *
      R.lik O0 C0 n (!Cm.comFirst) τ false false true

/-- Sum-binding: `Pr[Ver(ρ, b', d) = 1]` for an unbounded committer, with `b'` uniform and
independent of the commit phase; no opening string means rejection. -/
noncomputable def bindProb (A : UnbCommitter Cm) (n : ℕ) : ℝ :=
  ∑ τ : ITranscript (Cm.M.eval n) (Cm.ℓ.eval n),
    (∏ j : Fin (Cm.M.eval n),
      if Cm.comSends j = true then ((A.next n j (Cm.before τ j)) (τ j)).toReal else 1) *
    ∑ b' : Bool, (1 / 2 : ℝ) * ∑ od : Option (Msg (Cm.ℓd.eval n)),
      ((A.opening n τ b') od).toReal *
        (match od with
          | none => 0
          | some d => Cm.verAcc n (Cm.recState n τ) b' d)

/-- `Cm` is a **statistically sum-binding, computationally hiding commitment with a classical
committer and a quantum receiver** (Definition B.1): `Com`, `st`, `Open` are polynomial-time; `Rec`
and `Ver` are uniform QPT; "Correctness. For each `b ∈ {0,1}`, an honest opening to `b` is accepted
with probability at least `1 − negl(n)`"; "Computational hiding. The final views of every nonuniform
QPT receiver interacting with `Com(1^n, 0)` and `Com(1^n, 1)` are computationally
indistinguishable" (the distinguisher is part of the receiver, which outputs a bit); "Statistical
sum-binding … For every such `C`, there is a negligible function `η_C` such that
`Pr[Ver(ρ, b', d) = 1] ≤ 1/2 + η_C(n)`. (9)". -/
def IsCommitment : Prop :=
  PolyTimeComputable Cm.com ∧ PolyTimeComputable Cm.st ∧ PolyTimeComputable Cm.opn ∧
  Cm.recv.Uniform ∧ Cm.recv.PolyBounded ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ n : ℕ, f (unary n) = bnat (Cm.vanc n) ++ bnat (Cm.vout n : ℕ) ++ (Cm.ver n).desc) ∧
  (∃ q : Polynomial ℕ, ∀ n : ℕ, (Cm.ver n).size ≤ q.eval n ∧ Cm.vanc n ≤ q.eval n) ∧
  (∀ b : Bool, Negligible (fun n => 1 - Cm.honestProb n b)) ∧
  (∀ R : IParty ar0 (fun n => Cm.ℓ.eval n), R.PolyBounded →
    Negligible (fun n => |Cm.hideProb R n false - Cm.hideProb R n true|)) ∧
  ∀ A : UnbCommitter Cm, ∃ η : ℕ → ℝ, Negligible η ∧ ∀ n : ℕ, Cm.bindProb A n ≤ 1 / 2 + η n

end Commitment

end QAdvFew.PoQOracle.Supplement


