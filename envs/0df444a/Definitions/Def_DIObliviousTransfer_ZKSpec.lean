-- Prove2me | Definitions.Def_DIObliviousTransfer_ZKSpec
-- name    : DIObliviousTransfer_ZKSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:08:18.576014+00:00
-- url     : https://prove2.me/theorems/f2b51897-c761-44fc-ac71-789afa354d1d
-- title:
--   Zero-knowledge proofs for NP (conclusion of Lemma 16) and quantum one-way functions
-- statement:
--   An **NP relation** is a polynomial-time decidable relation $R(x,w)$ with polynomially bounded witnesses. A proof system assigns to each relation a two-party protocol without devices: the prover has $(x,w)$, the verifier has $x$ and outputs acceptance. **ZKSpec** requires, for every NP relation:
--   1. perfect completeness;
--   2. negligible statistical soundness against every prover strategy and auxiliary state, uniformly over false instances;
--   3. zero knowledge: realization, against every QPT verifier, of the functionality that releases the true statement to the simulator, with one QPT simulator fixed from the verifier and uniform over quantum auxiliary inputs entangled with a reference;
--   4. preservation of zero knowledge under polynomially many sequential invocations.
--
--   A **quantum-secure one-way function** is polynomial-time and is inverted with negligible probability, on uniform inputs of length $\lambda$, by every nonuniform QPT inverter with arbitrary quantum advice.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 16, p.42; §5.1, p.42

import Mathlib
import Definitions.Def_DIObliviousTransfer_Realizes

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §5.1, p.42: post-
quantum one-way functions and the zero-knowledge proofs of Lemma 16.

"Under qOWFs, every NP relation has a classical-message sequential proof with perfect
completeness, negligible statistical soundness, and quantum-computational zero knowledge. For
every nonuniform QPT verifier there is one QPT simulator, fixed from the verifier independently of
its auxiliary state, whose output channel is computationally indistinguishable from the real
verifier channel uniformly on arbitrary quantum auxiliary inputs entangled with an inaccessible
reference. Polynomially many sequential invocations preserve this guarantee." (Lemma 16) "All
assumptions use the auxiliary-input convention of Definition 5: the qOWF and resulting PRG resist
the allowed nonuniform quantum advice." (p.42)

**Formalization Note** (decisions D3, D4, D14). An NP relation is a polynomial-time decidable
relation `R(x, w)` with witnesses of polynomially bounded length. A proof system assigns to every
relation a two-party protocol without devices: the prover (Alice) has input `pack [x, w]`, the
verifier (Bob) input `x`, and the verifier outputs `[true]` on acceptance. Zero knowledge is
realization, against a corrupt verifier, of the functionality that releases the true statement
`x` to the simulator and lets it decide delivery; it is required for true instances (the valid
prover inputs). Soundness is against every prover strategy (any machine, not only QPT) and every
auxiliary state, uniformly over false instances. Sequential invocations are composition in the
sense of `ComposesSequentially`. A qOWF is a polynomial-time function that every nonuniform QPT
inverter with arbitrary quantum advice inverts with negligible probability on uniform inputs of
length `λ`.
-/

/-- An NP relation with witness-length bound `pw`. -/
def IsNPRel (R : Bits → Bits → Bool) (pw : ℕ → ℕ) : Prop :=
  PolyBound pw ∧ PolyTimeBits fun z => match unpack z with
    | [x, w] => [R x w && decide (w.length ≤ pw x.length)]
    | _ => []

/-- `x` is a true instance of `R`. -/
def NPTrue (R : Bits → Bits → Bool) (pw : ℕ → ℕ) (x : Bits) : Prop :=
  ∃ w, R x w = true ∧ w.length ≤ pw x.length

/-- The state of the zero-knowledge functionality: stage (`0` waiting, `1` released, `2` done). -/
structure ZKSt where
  stage : ℕ

/-- The zero-knowledge functionality of `R`: the prover's valid input `pack [x, w]` releases `x`
to the simulator; the empty adversary message delivers (prover `∅`, verifier accept), `[true]`
aborts. -/
def idealZK (R : Bits → Bits → Bool) (pw : ℕ → ℕ) : Func where
  St := ZKSt
  init := fun _ _ => ⟨0⟩
  step := fun st e =>
    match e with
    | .party true z =>
      match unpack z, st.stage with
      | [x, w], 0 => if R x w = true ∧ w.length ≤ pw x.length then (⟨1⟩, [.adv x]) else (st, [])
      | _, _ => (st, [])
    | .party false _ => (st, [])
    | .adv m =>
      if st.stage = 1 ∧ m = [] then (⟨2⟩, [.party true (some []), .party false (some [true])])
      else if st.stage < 2 ∧ m = [true] then (⟨2⟩, [.party true none, .party false none])
      else (st, [])
  validA := fun _ => {z | ∃ x w, z = pack [x, w] ∧ R x w = true ∧ w.length ≤ pw x.length}
  validB := fun _ => Set.univ

/-- The conclusion of **Lemma 16** for a proof system `ZK` (decision D14): for every NP relation,
no devices, polynomial-time honest parties,
perfect completeness, negligible statistical soundness, quantum-computational zero
knowledge against QPT verifiers, preserved by polynomially many sequential invocations. -/
def ZKSpec (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) : Prop :=
  ∀ R pw, IsNPRel R pw →
    (∀ lam, (ZK R pw).nb lam = 0) ∧
    -- efficient honest prover and verifier
    (∃ p : ℕ → ℕ, ResourceBound (ZK R pw) p) ∧
    -- perfect completeness
    (∀ (Dv : HonestDevices) lam x w, R x w = true → w.length ≤ pw x.length →
      honestEventProb (ZK R pw) trivialFunc Dv lam (pack [x, w]) x (fun o => o.2 = some [true]) = 1) ∧
    -- statistical soundness against every prover
    (∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ A : Adversary (ZK R pw), A.corruptA = true →
      ∀ lam r η, IsState η → ∀ x, ¬ NPTrue R pw x →
        realOutProb (ZK R pw) trivialFunc (fun _ _ => 0) A lam r η x (· = some [true]) ≤ ε lam) ∧
    -- zero knowledge against QPT verifiers, and its sequential composition
    Realizes (ZK R pw) trivialFunc (idealZK R pw) (fun c => c = false) (fun _ _ => 0) ∧
    ComposesSequentially (ZK R pw) trivialFunc (idealZK R pw) (fun c => c = false)
      (fun _ _ => 0) 0 (fun _ => 0)

/-- A quantum-secure one-way function (pp.2, 42): polynomial-time, and for every QPT inverter
family with arbitrary quantum advice `ω` on its register, the inversion probability on uniform
`x ∈ {0,1}^λ` is bounded by one negligible function. -/
def QOWF (f : Bits → Bits) : Prop :=
  PolyTimeBits f ∧ ∀ (w : ℕ → ℕ) (Inv : (lam : ℕ) → QMachine 0 (w lam)), IsQPTFam Inv →
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ lam (ω : Matrix (MReg 0 (w lam)) (MReg 0 (w lam)) ℂ),
      IsState ω →
      (1 / 2 ^ lam : ℝ) * ∑ x : Fin lam → Bool,
        ∑ o ∈ ((Inv lam).act 0 (pack [List.replicate lam true, f (List.ofFn x)])).outs,
          (if f o = f (List.ofFn x) then
            (((Inv lam).act 0 (pack [List.replicate lam true, f (List.ofFn x)])).apply o ω).trace.re
          else 0) ≤ ε lam

end DIObliviousTransfer


