-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Stream
-- name    : RandomStreamCI_CodeIntersection_Stream
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:35.533438+00:00
-- url     : https://prove2.me/theorems/d83d52fe-1d85-4886-bb55-4ba1ae36ebec
-- title:
--   Complete oracle-table streams, success and total-list recovery
-- statement:
--   Let $U=[n]\times\Sigma$ and $M=|U|$. A sample is a Boolean function on $U$ together with a bijection from $[M]$ to $U$, sampled independently and uniformly. The stream item at position $t$ is $(\pi(t),H(\pi(t)))$. Prefix sets, word graphs $T_c$, observed counts and satisfied counts are computed from this sample.
--
--   $$\operatorname{Success}(H,c)\iff c\in C\ \land\ \forall i,\ H(i,c_i)=1.$$
--
--   Failure is an explicit output. Total-list recovery bounds the number of codewords agreeing with input lists in at least $\rho n$ coordinates whenever the sum of all list sizes is at most $\ell$. This interface separates the stream law from the algorithms receiving it.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Problem 1, p. 6; Definition 6, p. 8; (9)–(11), pp. 7–8

import Definitions.Def_RandomStreamCI_CodeIntersection_Probability

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Address (n : ℕ) (Alphabet : Type*) := Fin n × Alphabet
abbrev Word (n : ℕ) (Alphabet : Type*) := Fin n → Alphabet
abbrev Oracle (n : ℕ) (Alphabet : Type*) := Address n Alphabet → Bool
abbrev Order (n : ℕ) (Alphabet : Type*) [Fintype Alphabet] :=
  Fin (Fintype.card (Address n Alphabet)) ≃ Address n Alphabet
abbrev Input (n : ℕ) (Alphabet : Type*) := Address n Alphabet × Bool
abbrev Sample (n : ℕ) (Alphabet : Type*) [Fintype Alphabet] := Oracle n Alphabet × Order n Alphabet

def streamItem {n : ℕ} {Alphabet : Type*} [Fintype Alphabet] (ω : Sample n Alphabet)
    (t : Fin (Fintype.card (Address n Alphabet))) : Input n Alphabet := (ω.2 t, ω.1 (ω.2 t))

/-- Uniform joint oracle/permutation law, §§2.2–2.3; the product is independent. -/
def streamProbability {n : ℕ} {Alphabet : Type*} [Fintype Alphabet] (E : Sample n Alphabet → Prop) : ℝ :=
  uniformProbability E

/-- Analysis-only prefix set; never available to a machine transition. -/
def seen {n : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (π : Order n Alphabet) (t : ℕ) : Finset (Address n Alphabet) :=
  Finset.univ.filter (fun u => (π.symm u).val < t)

/-- The graph of a word, §2.3 p. 8. -/
def wordAddresses {n : ℕ} {Alphabet : Type*} (c : Word n Alphabet) : Finset (Address n Alphabet) :=
  Finset.univ.map ⟨fun i => (i, c i), fun _ _ h => congrArg Prod.fst h⟩

def observedCount {n : ℕ} {Alphabet : Type*} [DecidableEq Alphabet]
    (c : Word n Alphabet) (A : Finset (Address n Alphabet)) : ℕ := (wordAddresses c ∩ A).card

def value {n : ℕ} {Alphabet : Type*} [DecidableEq Alphabet] (H : Oracle n Alphabet)
    (c : Word n Alphabet) (A : Finset (Address n Alphabet)) : ℕ :=
  ((wordAddresses c ∩ A).filter (fun u => H u = true)).card

/-- Problem 1: invalid words and the explicit failure outcome do not succeed. -/
def ValidOutput {n : ℕ} {Alphabet : Type*} (C : Finset (Word n Alphabet))
    (H : Oracle n Alphabet) : Option (Word n Alphabet) → Prop
  | none => False
  | some c => c ∈ C ∧ ∀ i, H (i, c i) = true

/-- Definition 6 (p. 8) uses a TOTAL list budget, not a per-coordinate budget.
The parameters ℓ and L are real, as on the page (no integrality is stated). -/
def ListRecoverable {n : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (C : Finset (Word n Alphabet)) (ρ ℓ L : ℝ) : Prop :=
  ∀ lists : Fin n → Finset Alphabet, ((∑ i, (lists i).card : ℕ) : ℝ) ≤ ℓ →
    (((C.filter (fun c => ρ * n ≤
      ((Finset.univ.filter (fun i => c i ∈ lists i)).card : ℝ))).card : ℕ) : ℝ) ≤ L

end RandomStreamCI.CodeIntersection


