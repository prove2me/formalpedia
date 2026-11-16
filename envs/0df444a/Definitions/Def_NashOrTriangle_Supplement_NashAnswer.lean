-- Prove2me | Definitions.Def_NashOrTriangle_Supplement_NashAnswer
-- name    : NashOrTriangle_Supplement_NashAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:45:50.129337+00:00
-- url     : https://prove2.me/theorems/44b27e8c-ada7-4aef-8edd-79cda56c76ce
-- title:
--   Mixed payoff $M(p,q)$, $\varepsilon$-Nash pairs and correct answers to $\mathrm{NorT}(k,t)$
-- statement:
--   Let $G=(A,B,M)$ be a zero-sum game with payoffs $M(a,b)\in[0,1]\cap\mathbb Q$, and let $p$, $q$ be finite rational mixtures of rows and columns. The expected payoff is
--   $$M(p,q)=\sum_{a}\sum_{b}p(a)\,q(b)\,M(a,b).$$
--   With $U(q)=\sup_{a\in A}M(a,q)$ and $L(p)=\inf_{b\in B}M(p,b)$ computed in the full game, the pair $(p,q)$ is an **$\varepsilon$-Nash equilibrium** if
--   $$U(q)-M(p,q)\le\varepsilon,\qquad M(p,q)-L(p)\le\varepsilon .$$
--
--   A run of an algorithm in the oracle model **solves $\mathrm{NorT}(k,t)$** on a binary game when it halts with either a pair of finite rational mixtures of strategies it already knows that is a $1/k$-Nash equilibrium, or with $t$ known rows and $t$ known columns forming a $t$-triangle.
--
--   These are the correctness notions against which the lower bounds of Theorems 3.1 and 4.1 are stated. A $1/k$-Nash equilibrium only satisfies $D(p,q)\le 2/k$, so this answer predicate is weaker than asking for $D(p,q)\le1/k$, and lower bounds against it are the paper's lower bounds.
--
--   **Formalization Note** Mixtures are finitely supported functions with rational weights; payoffs are cast to real numbers. The output layout in memory and the labels of known strategies are those of the published oracle machine (`decode`, `labelMix`, `ValidLabelMix`).
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), §1.1 and Definition 1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_NashOrTriangle_upper
import Definitions.Def_NashOrTriangle_lower
import Definitions.Def_NashOrTriangle_decode
import Definitions.Def_NashOrTriangle_IsTriangle
import Definitions.Def_NashOrTriangle_IsTriangleAnswer

namespace NashOrTriangle.Supplement

/-- `M(p, q) = ∑_a ∑_b p(a) q(b) M(a, b)`: the expected payoff to the row player when the finitely
supported row mixture `p` meets the finitely supported column mixture `q` (the extension of `M`
to mixed strategies "by taking expectations").

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4).

**Formalization Note** Same convention as the published `payoffRow`: rational payoffs cast to
`ℝ`, the sums run over the finite supports. -/
noncomputable def payoffMix {A B : Type*} (M : A → B → ℚ) (p : A →₀ ℚ) (q : B →₀ ℚ) : ℝ :=
  p.sum fun a w => (w : ℝ) * payoffRow M a q

/-- `(p, q)` is an `ε`-Nash equilibrium of the finite rational mixtures `p`, `q`: neither player
gains more than `ε` by deviating, `U(q) − M(p, q) ≤ ε` and `M(p, q) − L(p) ≤ ε`, with `U` and `L`
computed in the full game.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4): "A pair
(p, q) is a 1/k-Nash equilibrium if neither player can gain more than 1/k by deviating:
U(q) − M(p, q) ≤ 1/k, M(p, q) − L(p) ≤ 1/k." -/
def IsNashPair {A B : Type*} (M : A → B → ℚ) (ε : ℝ) (p : A →₀ ℚ) (q : B →₀ ℚ) : Prop :=
  upper M q - payoffMix M p q ≤ ε ∧ payoffMix M p q - lower M p ≤ ε

/-- A correct answer to `NorT(k, t)` (Definition 1.1) on a binary game: the halted state's output
decodes to a pair of finite rational label mixtures of **known** rows and columns whose strategy
pair is a `1/k`-Nash equilibrium of the full game, or to a `t`-triangle of known strategies.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Definition 1.1, printed p. 3 (PDF p. 4):
"NorT(k, t) asks for a 1/k-Nash equilibrium or a t-triangle. … Mixed strategies in inputs and
outputs are finitely supported and have rational probabilities."

**Formalization Note** The Nash alternative is the two Nash inequalities (`IsNashPair`), which
imply only `D(p, q) ≤ 2/k`; it is weaker than the published `IsNorTAnswerBinary` (which asks
`D(p, q) ≤ 1/k`), so lower bounds against this predicate are the lower bounds of the paper. The
output layout is the published `decode`. -/
def IsNorTNashAnswer {A B : Type*} (M : A → B → ℚ) (k t : ℕ) (s : State A B) : Prop :=
  (∃ base : ℤ, ∃ p q : ℕ →₀ ℚ, s.output = some base ∧
    decode s.core.mem base = some (Answer.pair p q) ∧
    ValidLabelMix s.rows.length p ∧ ValidLabelMix s.cols.length q ∧
    IsNashPair M (1 / (k : ℝ)) (labelMix s.rows p) (labelMix s.cols q)) ∨
  IsTriangleAnswer t (fun a b => IsTriangle M a b) s

end NashOrTriangle.Supplement


