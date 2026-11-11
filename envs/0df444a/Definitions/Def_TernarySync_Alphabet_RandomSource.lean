-- Prove2me | Definitions.Def_TernarySync_Alphabet_RandomSource
-- name    : TernarySync_Alphabet_RandomSource
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:53:43.390843+00:00
-- url     : https://prove2.me/theorems/41c20b96-6b0c-4175-9680-d1eef659db58
-- title:
--   The random source of Section 4: uniform choice vectors, the intervals $X$, $Y$, the bad events $E_{t,\ell}$, complete macroblocks, the deletion ball $B_\ell(y)$ and the dependency structure
-- statement:
--   Fix an outer word $T$ of length $N$ over $\{0,1,2\}$ and let $R = (R_1, \dots, R_N)$ be independent fair bits, i.e. $R$ is uniform on $\{0,1\}^N$; the probability of a set $A$ of choice vectors is $\Pr[A] = |A|/2^N$, and $\Pr[A \mid B] = \Pr[A \cap B]/\Pr[B]$. Let $W = W(T,R)$, a word of length $18N$ made of $N$ macroblocks of length 18.
--
--   For an integer length $\ell$ and an **available** start $t$ (both $[t, t+\ell)$ and $[t+\ell, t+2\ell)$ lie inside $W$), put
--
--   $$X = W[t, t+\ell), \qquad Y = W[t+\ell, t+2\ell), \qquad E_{t,\ell} = \{\mathrm{LCS}(X,Y) > (1-\eta)\ell\}, \quad \eta = \tfrac{1}{1000}.$$
--
--   These are Equation (9); the paper considers $E_{t,\ell}$ for integers $\ell > L = 1000$.
--
--   - $I_X$ (Lemma 4.2) is the set of macroblocks contained completely in $X$; conditioning on $F = (R_i)_{i \notin I_X} = f$ means restricting to the choice vectors that agree with $f$ outside $I_X$.
--   - The **deletion ball** (Equation (11)) of a word $y$ of length $\ell$ over an alphabet $\Sigma$ is $B_\ell(y) = \{x \in \Sigma^\ell : \mathrm{LCS}(x,y) > (1-\eta)\ell\}$.
--   - The variables of $E_{t,\ell}$ are the macroblock choices $R_i$ whose block meets $[t, t+2\ell)$, boundary blocks included; two long bad events are **neighbours** ($F \sim E_{t,\ell}$) when they are different and share such a choice (p. 17).
--
--   **Formalization Note.** Indices are 0-based: macroblock $i \in \{0, \dots, N-1\}$ is $[18i, 18i+18)$, and a start $t$ is available for length $\ell$ when $t + 2\ell \le 18N$. `unifProb A` is the count ratio $|A|/2^N$ on `Fin N → Fin 2` (the uniform probability measure on $\{0,1\}^N$, written as a count), `condProb A B` its conditional probability. `blockX`, `blockY` are $X$, $Y$; `badEvent T t ℓ` is $E_{t,\ell}$ with $\eta = 1/1000$ written as a literal; `completeBlocks N t ℓ` is $I_X$; `agreeOff I f` is the event $F = f$ (only the values of $f$ outside $I$ matter, and every such event has probability $2^{|I|-N} > 0$); `delBall η ℓ y` is $B_\ell(y)$ (a set of lists of length $\ell$); `eventVars N t ℓ` is $\mathrm{vbl}(E_{t,\ell})$; `availEvents N` is the set of pairs $(t,\ell)$ with $\ell > 1000$ and $t + 2\ell \le 18N$; `neighbours N t ℓ` is $\{F : F \sim E_{t,\ell}\}$.
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 15 (PDF 16), §4, Eq. (9) and Lemma 4.2; p. 16 (PDF 17), Eq. (11); p. 17 (PDF 18), the dependency structure

import Mathlib
import Definitions.Def_TernarySync_Alphabet_Brinkhuis

set_option autoImplicit false

namespace TernarySync.Alphabet

open Classical in
/-- The uniform probability on choice vectors `R ∈ {0, 1}^N` (independent fair bits, Section 4,
p. 15): the probability of a set `A` of choice vectors is `|A| / 2^N`. -/
noncomputable def unifProb {N : ℕ} (A : Set (Fin N → Fin 2)) : ℝ :=
  ((Finset.univ.filter fun R => R ∈ A).card : ℝ) / (2 : ℝ) ^ N

/-- Conditional probability under the uniform probability: `Pr[A | B] = Pr[A ∩ B] / Pr[B]`. -/
noncomputable def condProb {N : ℕ} (A B : Set (Fin N → Fin 2)) : ℝ :=
  unifProb (A ∩ B) / unifProb B

/-- The left interval `X = W[t, t + ℓ)` of Section 4 (p. 15), 0-based start `t`. -/
def blockX (T : List (Fin 3)) (R : Fin T.length → Fin 2) (t ℓ : ℕ) : List (Fin 3) :=
  factor (W T R) t (t + ℓ)

/-- The right interval `Y = W[t + ℓ, t + 2ℓ)` of Section 4 (p. 15), 0-based start `t`. -/
def blockY (T : List (Fin 3)) (R : Fin T.length → Fin 2) (t ℓ : ℕ) : List (Fin 3) :=
  factor (W T R) (t + ℓ) (t + 2 * ℓ)

/-- The bad event `E_{t,ℓ} = {LCS(X, Y) > (1 − η)ℓ}` of Equation (9) (p. 15), with
`η = 1/1000`, as a set of choice vectors. -/
def badEvent (T : List (Fin 3)) (t ℓ : ℕ) : Set (Fin T.length → Fin 2) :=
  {R | (1 - (1 : ℝ) / 1000) * (ℓ : ℝ) < (lcs (blockX T R t ℓ) (blockY T R t ℓ) : ℝ)}

/-- `I_X` of Lemma 4.2 (p. 15): the (0-based) indices `i < N` of the macroblocks
`[18 i, 18 i + 18)` contained completely in `X = W[t, t + ℓ)`. -/
def completeBlocks (N t ℓ : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => t ≤ 18 * i.val ∧ 18 * i.val + 18 ≤ t + ℓ

/-- The event `F = f` of Lemma 4.2: the choice vector agrees with `f` at every index outside
`I`. Only the values of `f` outside `I` matter. -/
def agreeOff {N : ℕ} (I : Finset (Fin N)) (f : Fin N → Fin 2) : Set (Fin N → Fin 2) :=
  {R | ∀ i, i ∉ I → R i = f i}

/-- The deletion ball of Equation (11) (p. 16): the words `x` of length `ℓ` with
`LCS(x, y) > (1 − η)ℓ`. -/
def delBall {β : Type*} (η : ℝ) (ℓ : ℕ) (y : List β) : Set (List β) :=
  {x | x.length = ℓ ∧ (1 - η) * (ℓ : ℝ) < (lcs x y : ℝ)}

/-- `vbl(E_{t,ℓ})` in the proof of Theorem 4.1 (p. 17): the macroblock choices whose block
`[18 i, 18 i + 18)` meets `[t, t + 2ℓ)`, boundary blocks included. -/
def eventVars (N t ℓ : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => 18 * i.val < t + 2 * ℓ ∧ t < 18 * i.val + 18

/-- The index set of the long bad events for an outer word of length `N` (Section 4): pairs
`(t, ℓ)` of an integer length `ℓ > L = 1000` and an available 0-based start `t`, i.e. both
`[t, t + ℓ)` and `[t + ℓ, t + 2ℓ)` lie inside the word of length `18 N`. -/
def availEvents (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (18 * N + 1) ×ˢ Finset.range (18 * N + 1)).filter
    fun p => 1000 < p.2 ∧ p.1 + 2 * p.2 ≤ 18 * N

/-- The neighbours `F ∼ E_{t,ℓ}` (p. 17): the other long bad events `E_{u,r}` that share a
macroblock choice with `E_{t,ℓ}`. -/
def neighbours (N t ℓ : ℕ) : Finset (ℕ × ℕ) :=
  (availEvents N).filter fun p =>
    p ≠ (t, ℓ) ∧ (eventVars N p.1 p.2 ∩ eventVars N t ℓ).Nonempty

end TernarySync.Alphabet


