-- Prove2me | Definitions.Def_QuantumBA_PackedShares_Supplement_Physical
-- name    : QuantumBA_PackedShares_Supplement_Physical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:37:42.099402+00:00
-- url     : https://prove2.me/theorems/2b431579-6e61-467d-9db7-2876f9e160bf
-- title:
--   Physical binary protocols and the universal Byzantine-agreement premise
-- statement:
--   A physical algorithm $P$ runs on $n$ processes with binary inputs, qubit registers and the published synchronous adaptive-adversary network. Its local gates are unitary, may allocate arbitrarily many fresh zero ancillas, and may be followed by computational-basis measurements. This represents arbitrary finite quantum instruments by dilation. Its classical messages and quantum headers have injective binary encodings with their actual lengths; an outgoing qubit is used at most once. Register identifiers are opaque handles: injective renaming commutes with every local operation and leaves decisions and halting unchanged. Neither global allocation addresses nor their arithmetic are a free side channel.
--
--   The correctness abbreviation is
--   $$
--    \operatorname{SolvesBinaryBA}(P,t)\iff\forall x,A,\;\operatorname{Agreement}(P,x,A,t)\land\operatorname{Validity}(P,x,A,t)\land\operatorname{Termination}(P,x,A,t).
--   $$
--   Here $x$ ranges over all binary input vectors and $A$ over the published adversaries, with the semantics enforcing at most $t$ corruptions. These predicates retain every-execution safety and almost-sure decision and halt of every never-corrupted process. The physical interface contains none of these correctness properties, no no-signalling axiom and no communication bound. It imposes no bound on computation, memory growth, bandwidth or running time.
--
--   This interface separates a general physical algorithm from the QBA-specific implementation used for the upper bound.
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), pp. 1–2, Section 1.1 and Theorem 2; physical states/instruments also Appendix A, p. 36 (PDF 2–3, 37)

import Definitions.Def_QuantumBA_PackedShares_Model

set_option autoImplicit false

open scoped Matrix

namespace QuantumBA.PackedShares.Supplement

abbrev Qubit := ZMod 2

/-- Rename physical wire handles; amplitudes and the order of slots are unchanged. -/
def renameOp (f : ℕ → ℕ) (o : HOp Qubit) : HOp Qubit where
  slots := o.slots.map (Option.map f)
  op := fun a b =>
    o.op (fun i => a ⟨i.val, by simp⟩)
      (fun i => b ⟨i.val, by simp⟩)

def renamePacket {H : Type} (f : ℕ → ℕ) (es : List (H × ℕ)) : List (H × ℕ) :=
  es.map (fun e => (e.1, f e.2))

def renameQ {n : ℕ} {H : Type} (f : ℕ → ℕ)
    (qs : List (Fin n × List (H × ℕ))) : List (Fin n × List (H × ℕ)) :=
  qs.map (fun m => (m.1, renamePacket f m.2))

/-- Register numbers are opaque handles, not a public communication channel. Every injective
renaming commutes with local computation. In particular the shared allocator's numerical
counter cannot be inspected to learn another process's input or allocation history. -/
structure RegisterLocal {n : ℕ} (P : Protocol n Qubit) where
  rename : (ℕ → ℕ) → P.St → P.St
  identity : ∀ s, rename id s = s
  compose : ∀ f g, Function.Injective f → Function.Injective g →
    ∀ s, rename (f ∘ g) s = rename f (rename g s)
  init : ∀ f, Function.Injective f → ∀ p b, rename f (P.init p b) = P.init p b
  ops : ∀ f, Function.Injective f → ∀ p s,
    P.ops p (rename f s) = (P.ops p s).map (renameOp f)
  meas : ∀ f, Function.Injective f → ∀ p s,
    P.meas p (rename f s) = (P.meas p s).map f
  out : ∀ f, Function.Injective f → ∀ p s rs vs,
    P.out p (rename f s) (rs.map (List.map f)) (vs.map (fun v => (f v.1, v.2))) =
      let res := P.out p s rs vs
      (rename f res.1, res.2.1, renameQ f res.2.2)
  recv : ∀ f, Function.Injective f → ∀ p s cs qs,
    P.recv p (rename f s) cs (renameQ f qs) = rename f (P.recv p s cs qs)
  decision : ∀ f, Function.Injective f → ∀ s, P.decision (rename f s) = P.decision s
  halted : ∀ f, Function.Injective f → ∀ s, P.halted (rename f s) = P.halted s

/-- Physical local algorithms in §1.1, expressed on the published network. Gates are unitary
on existing qubits and fresh zero ancillas; computational-basis measurements and retention of
ancillas implement arbitrary finite instruments. There is no limit on local computation,
state space, fresh ancillas, running time or accumulated memory. Message encodings are
injective bit strings with their actual length. Wire handles convey no additional data.
No agreement, validity, termination, no-signalling or resource claim occurs in this interface. -/
structure Physical {n : ℕ} (P : Protocol n Qubit) where
  localWires : RegisterLocal P
  encodeC : P.M → List Bool
  encodeC_injective : Function.Injective encodeC
  bitsC : ∀ m, P.mbits m = (encodeC m).length
  encodeH : P.Hd → List Bool
  encodeH_injective : Function.Injective encodeH
  bitsH : ∀ h, P.hbits h = (encodeH h).length
  unitary : ∀ p s o, o ∈ P.ops p s → o.opᴴ * o.op = 1
  /-- A qubit can be sent to only one recipient at a time, once. -/
  distinctSends : ∀ p s rs vs,
    (((P.out p s rs vs).2.2.flatMap (fun m => m.2)).map Prod.snd).Nodup

/-- The source correctness premise, for every input and every budget-limited adversary.
The imported semantics enforces the budget on each corruption request. -/
def SolvesBinaryBA {n : ℕ} (P : Protocol n Qubit) (t : ℕ) : Prop :=
  ∀ (x : Fin n → Bool) (A : Adversary n Qubit P.M P.Hd),
    Agreement P x A t ∧ Validity P x A t ∧ Termination P x A t

end QuantumBA.PackedShares.Supplement


