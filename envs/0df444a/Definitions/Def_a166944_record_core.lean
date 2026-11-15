-- Prove2me | Definitions.Def_a166944_record_core
-- name    : a166944_record_core
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-14T23:09:07.506081+00:00
-- url     : https://prove2.me/theorems/7e87eea0-8810-4d78-ab19-cdb7a9009bc2
-- title:
--   OEIS A166944 — Rowland-type recurrence, first differences, difference records, and the record/twin-prime target
-- statement:
--   This bundle fixes the object of study of OEIS A166944 and the exact sense in which its difference records are conjectured to be twin primes.
--
--   The sequence is the Rowland-type recursion
--
--   $$
--   a_0=0,\qquad a_1=2,\qquad a_{n+2}=\begin{cases} a_{n+1}+\gcd(n+2,\,a_{n+1}), & n+2 \text{ even},\\[2pt] a_{n+1}+\gcd(n,\,a_{n+1}), & n+2 \text{ odd},\end{cases}
--   $$
--
--   so that the gcd argument is the even index itself in the even branch and the index two below it in the odd branch. Write $d_n=a_n-a_{n-1}$ for the first differences and $D_n=a_n-n$ for the offset of the sequence from the identity.
--
--   A natural number $R$ is a **difference record** when $d_n=R$ at some index $n\ge 2$ and $d_k<R$ for every $2\le k<n$; that is, $R$ is a strict running maximum of the difference sequence and the record is attained. A number $p$ is the **greater member of a twin-prime pair** when $p$ and $p-2$ are both prime.
--
--   The **target** of the A166944 investigation is then
--
--   $$
--   \text{Target}:\quad \forall R\in\mathbb{N},\; 5<R \Rightarrow \bigl(R \text{ is a difference record}\bigr) \Rightarrow \bigl(R \text{ is the greater member of a twin-prime pair}\bigr).
--   $$
--
--   In words: every difference record above $5$ is the larger half of a twin-prime pair. This is the A166944 conjecture, and it is **open**; the present bundle only fixes its vocabulary, so that the partial results already proved about it — and any future proof of the whole statement — are stated against one shared interface. Publishing these declarations separately also keeps every later theorem free of local `def`s, so that downstream work can import them by name.
--
--   **Formalization Note** The recurrence is indexed so that the even/odd branch is selected by the index of the new term, matching the OEIS definition. `d` is truncated subtraction on `Nat`, so `d 0 = 0` and `d 1 = 2`; every record statement in this development considers only indices $\ge 2$, where the subtraction is known not to truncate. `Target` is deliberately a bare `Prop` so that it can be assumed as a hypothesis rather than asserted.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (recurrence and data). Formalization pinned to google-deepmind/formal-conjectures@8323e878b83fcd7f4a448256069352a265460d75, file FormalConjectures/OEIS/166944.lean (OeisA166944.a, OeisA166944.d, OeisA166944.IsDifferenceRecord, OeisA166944.IsGreaterTwinPrime, OeisA166944.conjecture). Bridge theorem: https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/Bridge.lean

-- Simulated Prove2Me definition bundle: exactly what /submit-definition would carry.
import Mathlib.Data.Nat.Prime.Defs

namespace A166944Research

/-- The Rowland-type recurrence of OEIS A166944. -/
def a : Nat → Nat
  | 0 => 0
  | 1 => 2
  | n + 2 =>
    let prev := a (n + 1)
    let idx := n + 2
    if idx % 2 = 0 then prev + Nat.gcd idx prev
    else prev + Nat.gcd (idx - 2) prev

/-- First differences. -/
def d (n : Nat) : Nat := a n - a (n - 1)

/-- Offset of the sequence from the identity: `D n = a n - n`. -/
def D (n : Nat) : Nat := a n - n

/-- `R` is a difference record. -/
def IsDifferenceRecord (R : Nat) : Prop :=
  ∃ n : Nat, 2 ≤ n ∧ d n = R ∧ ∀ k : Nat, 2 ≤ k → k < n → d k < R

/-- `p` is the greater member of a twin-prime pair. -/
def IsGreaterTwinPrime (p : Nat) : Prop := p.Prime ∧ (p - 2).Prime

/-- The A166944 conjecture, as a proposition. -/
def Target : Prop :=
  ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R

end A166944Research


