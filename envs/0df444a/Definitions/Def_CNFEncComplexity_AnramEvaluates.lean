-- Prove2me | Definitions.Def_CNFEncComplexity_AnramEvaluates
-- name    : CNFEncComplexity_AnramEvaluates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:10.846263+00:00
-- url     : https://prove2.me/theorems/1c87d438-a733-4ffe-b929-264d88a482cc
-- title:
--   $f$ is evaluated in time $t$ by an ANRAM with advice $A$ and $b$ queries
-- statement:
--   An ANRAM consists of an advice-free nondeterministic RAM program $\pi$ and an advice string $A\in\{0,1\}^m$ that does not depend on the input. On input $\vec x$ it first guesses indices $i_1,\dots,i_b\in\{0,\dots,m-1\}$, fetches $A[i_1],\dots,A[i_b]$, and passes $\vec x$ together with the queries $((i_1,A[i_1]),\dots,(i_b,A[i_b]))$ to $\pi$. The ANRAM **evaluates $f$ in time $t$** if for every $x\in\{0,1\}^n$,
--   $$f(x)=1 \iff \exists\, i_1,\dots,i_b:\ \pi \text{ accepts } x\,\mathrm{bin}(i_1)A[i_1]\cdots\mathrm{bin}(i_b)A[i_b] \text{ within cost } t,$$
--   where $\mathrm{bin}(i)$ is the $\lceil\log_2 m\rceil$-bit binary expansion of $i$, most significant bit first.
--
--   This is the model of the main result, Theorem 2: it accesses at most $b$ bits of an $m$-bit advice string per input.
--
--   **Formalization Note** Exactly $b$ indices are guessed, possibly repeated, which covers "at most $b$". The prefetch step is free and "time $t$" is the cost of the advice-free program, as in the proof of Theorem 2, which applies Theorem 10 to it on inputs of length $n+b(\lg m+1)$. No relation between $b$ and $m$ is assumed; for $m=0<b$ there is no guess and $f\equiv0$.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 2, p.2 (PDF 3) and §3.1, p.11 (PDF 12)

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr
import Definitions.Def_CNFEncComplexity_AcceptsWithin

namespace CNFEncComplexity

/-- The `w`-bit binary expansion of `v`, most significant bit first (`v` is reduced mod `2^w`). -/
def bitsMSB (w v : ℕ) : List Bool :=
  List.ofFn fun i : Fin w => v.testBit (w - 1 - i)

/-- The advice queries `((i₁, A[i₁]), …, (i_b, A[i_b]))` written on the input tape: for each
`j < b` in order, the `⌈lg m⌉`-bit binary expansion of the index `idx j` (`m = A.length`, most
significant bit first), followed by the advice bit `A[idx j]`. -/
def queryBits (A : List Bool) {b : ℕ} (idx : Fin b → Fin A.length) : List Bool :=
  (List.ofFn fun j : Fin b => bitsMSB (Nat.clog 2 A.length) (idx j) ++ [A.get (idx j)]).flatten

/-- **"f can be evaluated in time t with m bits of advice by an ANRAM machine that accesses at most b
bits of the advice for each input".** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 2, p.2 (PDF 3), with the ANRAM of §3.1,
p.11 (PDF 12): "1. First, the machine nondeterministically guesses the indices i₁, i₂, . . . , i_b of A
that will be queried during the computation on x⃗. The machine then fetches those bits of advice,
storing the results as a list of ordered pairs ((i₁, A[i₁]), . . . , (i_b, A[i_b])). 2. Then, the
machine passes x⃗ together with the advice queries ((i₁, A[i₁]), . . . , (i_b, A[i_b])) to a
nondeterministic RAM machine without advice."

`AnramEvaluates prog A b t f`: for every `x ∈ {0,1}ⁿ`, `f x = 1` iff for some guess of `b` indices
`idx : Fin b → Fin m` into the advice string `A` (`m = A.length`), the advice-free program `prog`
accepts the input tape `x ++ queryBits A idx` within cost `t` (`AcceptsWithin`).

**Formalization Note.** The advice string is `A`, of length `m`. Exactly `b` indices are guessed,
possibly with repetitions, which covers "at most `b`". The prefetch step is free and "time `t`" is
the cost of the advice-free machine, as in the proof of Theorem 2 (p.12), which applies Theorem 10 to
it on an input of length `n + b·(lg m + 1)`. No relation between `b` and `m` is assumed; with
`m = 0 < b` there is no guess and `f ≡ 0`. -/
def AnramEvaluates {n : ℕ} (prog : List Instr) (A : List Bool) (b t : ℕ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool,
    f x = true ↔ ∃ idx : Fin b → Fin A.length, AcceptsWithin prog (List.ofFn x ++ queryBits A idx) t

end CNFEncComplexity


