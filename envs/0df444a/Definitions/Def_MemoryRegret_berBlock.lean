-- Prove2me | Definitions.Def_MemoryRegret_berBlock
-- name    : MemoryRegret_berBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:24.597327+00:00
-- url     : https://prove2.me/theorems/0538034e-1150-46bf-9aee-7d95dd22cc87
-- title:
--   Law of a block of $m$ i.i.d. $\mathrm{Ber}(b,\tfrac12+\varepsilon)$ labels; bad blocks
-- statement:
--   $\mathrm{Ber}(b,q)$ takes the value $b$ with probability $q$ and $1-b$ with probability $1-q$. For $c\in\{0,1\}^m$,
--   $$\mathrm{berBlock}_\varepsilon(b,c)=\prod_{i\le m}\Bigl(\tfrac12+\varepsilon\text{ if }c_i=b,\text{ else }\tfrac12-\varepsilon\Bigr)$$
--   is the probability of the block $c$ under $\mathrm{Ber}(b,\frac12+\varepsilon)^m$, and $\mathrm{blockLabelLaw}_\varepsilon(c)=\frac12\mathrm{berBlock}_\varepsilon(0,c)+\frac12\mathrm{berBlock}_\varepsilon(1,c)$ is the law of a block whose common bit is a fair coin. A block is **bad** when it is unbalanced:
--   $$\mathrm{BadBlock}=\Bigl\{c:\Bigl|\sum_j c_j-\frac m2\Bigr|\ge50\,r\sqrt m\Bigr\}.$$
--
--   These are the elementary laws of the distinguishing problem.
--
--   **Formalization Note** The weights form a distribution exactly when $|\varepsilon|\le\frac12$; every theorem of the mission restricts $\varepsilon$ accordingly.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §2, p.7 (Ber); Definition 3, p.9; BadBlock, p.18 (the same set as the display on p.10)

import Mathlib

namespace MemoryRegret

/-- **The law of a block of `m` labels drawn i.i.d. from `Ber(b, ½ + ε)`.**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§2, p.7: "We use the notation Ber(b, q) to denote the Bernoulli distribution which takes value b
with probability q, and 1 − b with probability 1 − q"; Definition 3, p.9: "for all i ∈ [m],
b^{(i)} ∼ Ber(b, 1/2 + ε)".

`berBlock ε b c = ∏_{i<m} (½ + ε if c_i = b, else ½ − ε)` is the probability of the block
`c ∈ {0,1}^m` when its `m` labels are independent `Ber(b, ½ + ε)`.

**Formalization Note.** Labels are `Bool` (`false = 0`). For `ε ∈ [−½, ½]` this is a probability
vector on `Fin m → Bool`; every theorem using it restricts `ε` so. -/
noncomputable def berBlock {m : ℕ} (ε : ℝ) (b : Bool) (c : Fin m → Bool) : ℝ :=
  ∏ i, if c i = b then 1 / 2 + ε else 1 / 2 - ε

/-- `E_{b ∈_R {0,1}} Pr_{c ∼ Ber(b, ½+ε)^m}[c]`: the law of a block whose common bit is a fair
coin (the NO-case block of Definition 3, and the law of `(Y_1, …, Y_m)` in Lemma 6.1). -/
noncomputable def blockLabelLaw {m : ℕ} (ε : ℝ) (c : Fin m → Bool) : ℝ :=
  1 / 2 * berBlock ε false c + 1 / 2 * berBlock ε true c

/-- The number of ones (`true` entries) of a block. -/
def numOnes {m : ℕ} (c : Fin m → Bool) : ℕ := (Finset.univ.filter fun i => c i = true).card

/-- The number of zeros (`false` entries) of a block. -/
def numZeros {m : ℕ} (c : Fin m → Bool) : ℕ := (Finset.univ.filter fun i => c i = false).card

/-- BadBlock (p.18; the same set as the p.10 display `|(ones in b) − (zeros in b)| ≥ 100r√m`):
the blocks with `|∑_j b^{(j)} − m/2| ≥ 50·r·√m`. -/
def BadBlock (m : ℕ) (r : ℝ) : Set (Fin m → Bool) :=
  {c | 50 * r * Real.sqrt m ≤ |(numOnes c : ℝ) - m / 2|}

end MemoryRegret


