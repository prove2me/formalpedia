-- Prove2me | Definitions.Def_PolyEulerFlow_CompilesTo
-- name    : PolyEulerFlow_CompilesTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:50.485287+00:00
-- url     : https://prove2.me/theorems/1e0a0720-b79f-4d41-b558-d342ade41446
-- title:
--   A dyadic program compiles a two-stack decider with overhead $a$
-- statement:
--   The link between the source machine $M$ and the compiled two-stack program $P$ of Theorem 1.
--
--   $P$ **compiles** $M$ with overhead $a\in\mathbb N$ when there are a block length $b\ge1$, an injective block code $\beta:\Gamma\to\{1,2\}^b$ and a map $\pi$ from the states of $P$ to the states of $M$ (partial), fixed once for all inputs, such that for every input $x$ and every scale $s\ge\ell(x)+4$, with $h=2^{-s}$, there are indices $j_0<j_1<\dots<j_{T_x}$, where $T_x$ is the halting time of $M$ on $x$, with:
--
--   1. $j_0\le a(\ell(x)+s+1)$ and $j_{i+1}-j_i\le a$;
--   2. at index $j_i$ the state of $P$ is mapped by $\pi$ to the state of $M$ after $i$ transitions, and each stack of $P$ is the block encoding, by $\beta$, of the corresponding stack of $M$ after $i$ transitions;
--   3. at index $j_{T_x}+a$, $P$ is in its accepting state exactly when $M$ accepts $x$, and in its rejecting state exactly when $M$ rejects $x$.
--
--   **Formalization Note** The paper describes the compiled program only as "the canonical raw reader of Lemma 24, followed by the fixed word program", with "fixed encodings of the alphabet, and any reversal needed to load the word", using at most $a(T(n)+s+n+1)$ transitions (proof of Theorem 1, p.43). The definition records exactly this: a loading prefix of length $O(n+s)$, a simulation with bounded delay per transition and block-encoded stacks, and the resetting halt with $M$'s answer.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), proof of Theorem 1, p.43 (PDF 45); proof of Lemma 24, pp.54–55 (PDF 56–57)

import Definitions.Def_PolyEulerFlow_TwoStackDecider
import Definitions.Def_PolyEulerFlow_DyadicProgram

namespace PolyEulerFlow

/-- `P` is a compiled two-stack program of the decider `M`, with overhead `a`: the link that makes the
section clause of Theorem 1 a statement about `M`. Bournez, One Polynomial Field for Every Euler Step and
the Flow (manuscript, sha256 c4e01b2b…), proof of Theorem 1, p.43, and proof of Lemma 24, pp.54–55.
**Formalization Note.** The paper describes the compiled program only as "the canonical raw reader of Lemma 24,
followed by the fixed word program", using "at most a(T(n) + s + n + 1) transitions". So `β` and `π` are
fixed once for all inputs: `β` is an injective block code of one length, `π` reads `M`'s state off `P`'s state.
For every input and every scale `s ≥ ℓ(x) + 4`, there are indices `j₀ < j₁ < …`, one per transition of `M`, with
`j₀ ≤ a(ℓ(x) + s + 1)` and gaps at most `a`, at which `P` holds `M`'s state and block-encoded stacks; and `a`
transitions after the last of them `P` is in `acc` exactly if `M` accepts, and in `rej` exactly if it rejects. -/
def CompilesTo (P : DyadicProgram) (M : TwoStackDecider) (a : ℕ) : Prop :=
  ∃ (b : ℕ) (β : M.Γ → List (Fin 2)) (π : P.Q → Option M.Q),
    1 ≤ b ∧ Function.Injective β ∧ (∀ γ, (β γ).length = b) ∧
    ∀ (x s : ℕ), inputLength x + 4 ≤ s →
      ∃ j : ℕ → ℕ,
        j 0 ≤ a * (inputLength x + s + 1) ∧
        (∀ i < M.haltTime x, j i < j (i + 1) ∧ j (i + 1) ≤ j i + a) ∧
        (∀ i ≤ M.haltTime x,
          π (P.conf x (scale s) (j i)).q = some (M.conf x i).q ∧
          (P.conf x (scale s) (j i)).st1 = (M.conf x i).s1.flatMap β ∧
          (P.conf x (scale s) (j i)).st2 = (M.conf x i).s2.flatMap β) ∧
        ((P.conf x (scale s) (j (M.haltTime x) + a)).q = P.acc ↔ M.Accepts x) ∧
        ((P.conf x (scale s) (j (M.haltTime x) + a)).q = P.rej ↔ ¬ M.Accepts x)

end PolyEulerFlow


