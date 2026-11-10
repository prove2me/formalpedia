-- Prove2me | Definitions.Def_AvgWorstGap_nKt
-- name    : AvgWorstGap_nKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:57.16119+00:00
-- url     : https://prove2.me/theorems/5cdc1427-909a-4e61-a7e6-9f08a6891993
-- title:
--   Nondeterministic time-bounded Kolmogorov complexity $nK^{t,O}(x\mid y;r)$
-- statement:
--   A program $(M,\alpha)$ **nondeterministically outputs** $x$ on $(y;r)$ in time $t$ if
--
--   1. for every guess $w\in\{0,1\}^t$, $M(\alpha;y;w;r)$ outputs either $x$ or $\bot$ within $t$ steps, and
--   2. for some guess $w\in\{0,1\}^t$, $M(\alpha;y;w;r)$ outputs $x$ within $t$ steps.
--
--   Then
--   $$\mathrm{nK}^{t,O}(x\mid y;r)=\min\{|\Pi| : \Pi=(M,\alpha)\text{ nondeterministically outputs }x\text{ on }(y;r)\text{ in time }t\},$$
--   with $+\infty$ when no program qualifies. The machine has access to the oracle $O$. The unrelativized notion of Definition 2.3 is $O=\emptyset$, and $\mathrm{nK}^t(x\mid y)=\mathrm{nK}^t(x\mid y;\epsilon)$.
--
--   **Formalization Note** Programs here are single machine-advice pairs, run with the guess tape as in the model of p.12; the composition model of p.13 has no guess tape. Outputting $\bot$ means the output word is the single symbol $\bot$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.1, p.12 (nondeterministic output); Definition 2.3, p.14

import Mathlib
import Definitions.Def_AvgWorstGap_Program

namespace AvgWorstGap

open NKtLB

/-- **Nondeterministic output of a program `(M, α)`** (arXiv:2610.19162, version of October 30,
2026, §2.1, p.12): "We say that a program `Π` non-deterministically outputs `y` on input `(x; r)`
in time `t` if: `∀w ∈ {0, 1}^t`, `Π(x; w; r)` outputs either `y` or `⊥` in time `t`, and
`∃w ∈ {0, 1}^t`, `Π(x; w; r)` outputs `y` in time `t`." Here `Π(x; w; r)` is `M(α; x; w; r)`.

**Formalization Note.** The program is a single machine-advice pair, run with the guess tape (the
model of p.12; the composition model of p.13 has no guess tape). Guesses have length exactly `t`;
"outputs `⊥`" is the one-symbol output word `⊥`; the oracle `O` is given to `M`. -/
def NondetOutputs (O : Set (List Bool)) (p : Machine × List Bool) (y r : List Bool) (t : ℕ)
    (x : List Bool) : Prop :=
  (∀ w : List Bool, w.length = t →
      p.1.HaltsWith O ⟨p.2, y, w, r⟩ t (bitsSym x) ∨ p.1.HaltsWith O ⟨p.2, y, w, r⟩ t [Sym.bot]) ∧
    ∃ w : List Bool, w.length = t ∧ p.1.HaltsWith O ⟨p.2, y, w, r⟩ t (bitsSym x)

/-- **Nondeterministic time-bounded Kolmogorov complexity `nK^{t,O}(x | y; r)`** (Def. 2.3,
p.14): "`nK^t(x | y; r) ≜ min_{Π∈{0,1}∗} ( |Π| | ∀w ∈ {0, 1}^t, Π(y; w; r) outputs x or ⊥ in t
steps; ∃w ∈ {0, 1}^t, Π(y; w; r) outputs x in t steps )`. We write `nK^t(x | y)` for
`nK^t(x | y; ϵ)`." The oracle version (used in Theorem 2.13 and Lemma 2.17) gives `M` access to `O`.

**Formalization Note.** Programs are single pairs `(M, α)` of size `|pairEnc (M, α)|`; values in
`ℕ∞`, `⊤` when no program qualifies. -/
noncomputable def nKt (O : Set (List Bool)) (t : ℕ) (x y r : List Bool) : ℕ∞ :=
  ⨅ (p : Machine × List Bool) (_ : NondetOutputs O p y r t x), ((pairEnc p).length : ℕ∞)

end AvgWorstGap


