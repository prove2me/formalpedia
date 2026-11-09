-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Models
-- name    : WatsonPseudodeterminism_MASeparation_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:47.234765+00:00
-- url     : https://prove2.me/theorems/36707a3e-01a2-4a34-a9bb-8483a82386d4
-- title:
--   MA-type and error-parameterized N·BPP-type protocols
-- statement:
--   Let $F:X\times Y\to\{0,1,\bot\}$ be a partial function and let $d$ be a natural cost bound. An MA protocol consists of $k\le2^d$ randomized protocols, each of depth at most $d$. It satisfies
--
--   $$F(x,y)=1\Rightarrow\exists i:\ D_i(x,y)\ge2/3,\qquad F(x,y)=0\Rightarrow\forall i:\ D_i(x,y)\le1/3.$$
--
--   An $\varepsilon$-error N·BPP protocol uses thresholds $1-\varepsilon$ and $\varepsilon$ instead, and additionally requires, for every valid input and every witness,
--
--   $$D_i(x,y)\in[0,\varepsilon]\cup[1-\varepsilon,1].$$
--
--   Standard N·BPP means $\varepsilon=1/3$. No gap requirement is imposed when $F(x,y)=\bot$. Finite indexing permits duplicate witnesses and the empty set of witnesses, exactly as a set of size at most $2^d$ does. These predicates retain both the witness-size and communication bounds.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §1.1, p. 4 (MA and N·BPP definitions and amplification); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Protocol

namespace WatsonPseudodeterminism.MASeparation

/-- §1.1, p. 4: at most 2^d witnesses, each naming a depth-at-most-d public-coin protocol. -/
def MAProtocol {X Y : Type} (F : PartialFn X Y) (d : ℕ) : Prop :=
  ∃ (k : ℕ) (D : Fin k → RandomProtocol X Y), k ≤ 2 ^ d ∧
    (∀ i, DepthBound (D i) d) ∧
    (∀ x y, F x y = some true → ∃ i, (2 / 3 : ℝ) ≤ acceptance (D i) x y) ∧
    (∀ x y, F x y = some false → ∀ i, acceptance (D i) x y ≤ (1 / 3 : ℝ))

/-- §1.1, p. 4: the pseudodeterministic gap is imposed on valid inputs only. -/
def NBPPProtocolErr {X Y : Type} (ε : ℝ) (F : PartialFn X Y) (d : ℕ) : Prop :=
  ∃ (k : ℕ) (D : Fin k → RandomProtocol X Y), k ≤ 2 ^ d ∧
    (∀ i, DepthBound (D i) d) ∧
    (∀ x y, F x y ≠ none → ∀ i,
      (0 ≤ acceptance (D i) x y ∧ acceptance (D i) x y ≤ ε) ∨
      (1 - ε ≤ acceptance (D i) x y ∧ acceptance (D i) x y ≤ 1)) ∧
    (∀ x y, F x y = some true → ∃ i, 1 - ε ≤ acceptance (D i) x y) ∧
    (∀ x y, F x y = some false → ∀ i, acceptance (D i) x y ≤ ε)

/-- N·BPP uses the standard error 1/3. -/
def NBPPProtocol {X Y : Type} (F : PartialFn X Y) (d : ℕ) : Prop :=
  NBPPProtocolErr (1 / 3) F d

end WatsonPseudodeterminism.MASeparation


