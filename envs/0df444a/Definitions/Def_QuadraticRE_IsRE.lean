-- Prove2me | Definitions.Def_QuadraticRE_IsRE
-- name    : QuadraticRE_IsRE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:05:15.438201+00:00
-- url     : https://prove2.me/theorems/89906aee-6dec-48a7-b9e1-3235b166a463
-- title:
--   Randomized encodings (Definition 3.1)
-- statement:
--   Let $X,Y,R,Z$ be finite sets, $R$ nonempty, $g:X\to Y$, and $\hat g:X\times R\to Z$. Given a deterministic **decoder** $\mathrm{Dec}:Z\to Y\cup\{\bot\}$ and a **simulator** $\mathrm{Sim}$ assigning to each $y\in Y$ a law on $Z$, the map $\hat g$ is a **$\delta$-correct, $\varepsilon$-private randomized encoding** of $g$ if for every $x\in X$
--   $$\Pr_{r\leftarrow R}\bigl[\mathrm{Dec}(\hat g(x;r))\neq g(x)\bigr]\le\delta,\qquad \mathrm{SD}\bigl(\mathrm{Sim}(g(x)),\hat g(x;U_R)\bigr)\le\varepsilon .$$
--   The two conditions are also available separately (correctness, privacy). The encoding is **perfect** when $\delta=\varepsilon=0$.
--
--   The decoder sees only the encoded output and the simulator only $g(x)$; this is what makes the notion nontrivial.
--
--   **Formalization Note** $\bot$ is `none`. The decoder and the simulator are named arguments, so a statement can name a specific simulator; "$g$ has an RE" is the existential over them. The page takes $\delta,\varepsilon\in[0,1]$; here they are arbitrary real upper bounds, because Lemma 4.11 states bounds $\delta_0+M\delta_\lambda$, $\varepsilon_0+M\varepsilon_\lambda$ that can exceed one. On $[0,1]$ the notions agree.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Definition 3.1, p.13

import Mathlib
import Definitions.Def_QuadraticRE_SD

namespace QuadraticRE

/-- `δ`-correctness in Definition 3.1 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.13: for **every** `x`,
`Pr_{r←R}[Dec(ĝ(x; r)) ≠ g(x)] ≤ δ`. `none` is the failure symbol `⊥`. The decoder sees only the
encoded output. -/
def IsCorrect {X Y R Z : Type} [Fintype R] [Nonempty R]
    (g : X → Y) (ghat : X → R → Z) (δ : ℝ) (Dec : Z → Option Y) : Prop :=
  ∀ x, prob (fun r : R => Dec (ghat x r) ≠ some (g x)) ≤ δ

/-- `ε`-privacy in Definition 3.1, p.13: `Sim` assigns to every `y ∈ Y` a law on `Z`, and for
**every** `x`, `SD(Sim(g x), ĝ(x; U_R)) ≤ ε`. The simulator sees only `g x`. -/
def IsPrivate {X Y R Z : Type} [Fintype R] [Nonempty R] [Fintype Z]
    (g : X → Y) (ghat : X → R → Z) (ε : ℝ) (Sim : Y → Z → ℝ) : Prop :=
  (∀ y, IsLaw (Sim y)) ∧ ∀ x, SD (Sim (g x)) (law (ghat x)) ≤ ε

/-- Definition 3.1 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.13: `ĝ : X × R → Z` is a `δ`-correct, `ε`-private
randomized encoding of `g`, with the decoder `Dec` and the simulator `Sim` named. "`g` has such an
RE" is the existential over `Dec` and `Sim`. The encoding is perfect when `δ = ε = 0`.

**Formalization Note.** The page takes `δ, ε ∈ [0, 1]`. Here they are arbitrary reals, read as upper
bounds, because Lemma 4.11 states the bounds `δ₀ + Mδ_λ`, `ε₀ + Mε_λ`, which may exceed one. On
`[0, 1]` this is the page's notion. A randomized simulator is an arbitrary law for each `y`. -/
structure IsRE {X Y R Z : Type} [Fintype R] [Nonempty R] [Fintype Z]
    (g : X → Y) (ghat : X → R → Z) (δ ε : ℝ) (Dec : Z → Option Y) (Sim : Y → Z → ℝ) : Prop where
  correct : IsCorrect g ghat δ Dec
  priv : IsPrivate g ghat ε Sim

end QuadraticRE


