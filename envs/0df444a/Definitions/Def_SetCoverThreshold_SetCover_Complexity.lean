-- Prove2me | Definitions.Def_SetCoverThreshold_SetCover_Complexity
-- name    : SetCoverThreshold_SetCover_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:52:04.277242+00:00
-- url     : https://prove2.me/theorems/00c5d56f-c56e-48ea-8c49-e3332db2eea1
-- title:
--   Gap NP-hardness and the class $\mathrm{TIME}(n^{O(\log\log n)})$
-- statement:
--   Two complexity notions used in Feige's paper, built on Cook's one-tape Turing machines and the classes $\mathrm{P}$, $\mathrm{NP}$ of the published definition `CookPvsNP_defs`.
--
--   **Gap NP-hardness.** Let $\alpha$ be a set of instances with a string encoding $\mathrm{enc}$, and let $\mathrm{Yes},\mathrm{No}$ be two properties of instances. "It is NP-hard to distinguish between $\mathrm{Yes}$ and $\mathrm{No}$" means: for every finite nonempty alphabet $\Sigma'$ and every language $L'\in\mathrm{NP}$ over $\Sigma'$ there is a map $f$ from strings to instances such that $x\mapsto\mathrm{enc}(f(x))$ is polynomial-time computable and
--
--   $$x\in L' \Rightarrow \mathrm{Yes}(f(x)),\qquad x\notin L' \Rightarrow \mathrm{No}(f(x)).$$
--
--   **The class $\mathrm{TIME}(n^{O(\log\log n)})$.** The paper writes (p. 636): "we let TIME(t) denote the class of languages that have a deterministic algorithm that runs in time t". A language $L$ over $\Sigma$ belongs to the class when some deterministic one-tape Turing machine, with some constant $c\in\mathbb N$, halts on every input $w$ within
--
--   $$|w|^{\,c\,(\lfloor\log_2\lfloor\log_2|w|\rfloor\rfloor+1)}+c$$
--
--   steps and accepts exactly the words of $L$.
--
--   These are the two ends of the goal theorem: gap NP-hardness is how the cited PCP input enters, and the time class is its conclusion.
--
--   **Formalization Note** The time class copies Cook's definition of $\mathrm{P}$ with the polynomial bound $|w|^k+k$ replaced by the bound above; the $+1$ in the exponent only matters for $|w|<4$. Multi-tape machines are simulated by one-tape machines with quadratic overhead, which the class absorbs.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 636 (definition of TIME(t)); p. 639, Theorem 2.1.1 and p. 640, Proposition 2.1.2 ("NP-hard to distinguish")

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.SetCover

/-- Gap (promise) NP-hardness, Karp style: every NP language over every finite nonempty alphabet
maps in polynomial time to instances satisfying `Yes` (members) and `No` (non-members).
"It is NP-hard to distinguish between `Yes` and `No`" (Feige 1998, Theorem 2.1.1, Prop. 2.1.2). -/
def GapNPHard {α Sym : Type} (enc : α → List Sym) (Yes No : α → Prop) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.NP Sym' →
      ∃ f : List Sym' → α, CookPvsNP.PolyTimeComputable (fun x => enc (f x)) ∧
        ∀ x, (x ∈ L' → Yes (f x)) ∧ (x ∉ L' → No (f x))

/-- The class `TIME(n^{O(log log n)})` (Feige 1998, p. 636): languages decided by a deterministic
one-tape Turing machine (in the sense of `CookPvsNP`) that halts on every input `w` within
`|w|^(c * (⌊log₂ ⌊log₂ |w|⌋⌋ + 1)) + c` steps, for some constant `c`. -/
def LogLogTime (Sym : Type) [Fintype Sym] : Set (CookPvsNP.Lang Sym) :=
  { L | ∃ (Γ : Type) (_ : Fintype Γ) (ι : Sym ↪ Γ) (M : CookPvsNP.TM Γ) (c : ℕ),
      (∀ w : List Sym,
        M.HaltsWithin (w.length ^ (c * (Nat.log 2 (Nat.log 2 w.length) + 1)) + c) (w.map ι)) ∧
      ∀ w : List Sym, w ∈ L ↔ M.Accepts (w.map ι) }

end SetCoverThreshold.SetCover


