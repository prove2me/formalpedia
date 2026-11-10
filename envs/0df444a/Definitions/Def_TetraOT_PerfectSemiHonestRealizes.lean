-- Prove2me | Definitions.Def_TetraOT_PerfectSemiHonestRealizes
-- name    : TetraOT_PerfectSemiHonestRealizes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:06.275074+00:00
-- url     : https://prove2.me/theorems/d51f77d5-4cd7-429b-a373-ddaba9067b47
-- title:
--   Perfect simulation-based security against semi-honest parties (two parties, no inputs)
-- statement:
--   Consider a two-party protocol without inputs whose randomness is $\omega \sim \mu$. Write $V_A(\omega)$ and $O_A(\omega)$ for Alice's view and output, and $V_B(\omega)$ and $O_B(\omega)$ for Bob's. Let $\mathcal F$ be a distribution on pairs of outputs (an ideal randomized functionality). The protocol **perfectly realizes $\mathcal F$ against semi-honest parties** if all three of the following hold:
--
--   1. **Correctness.** The joint law of $(O_A, O_B)$ under $\mu$ equals $\mathcal F$.
--   2. **Alice corrupted.** There is a simulator $S_A$, mapping Alice's ideal output $o_1$ to a distribution on views, such that
--   $$
--   \mathrm{law}_\mu\big(V_A, O_A, O_B\big) = \mathrm{law}\big(S_A(o_1), o_1, o_2\big), \qquad (o_1, o_2) \sim \mathcal F .
--   $$
--   3. **Bob corrupted.** There is a simulator $S_B$, mapping Bob's ideal output $o_2$ to a distribution on views, such that
--   $$
--   \mathrm{law}_\mu\big(V_B, O_A, O_B\big) = \mathrm{law}\big(S_B(o_2), o_1, o_2\big), \qquad (o_1, o_2) \sim \mathcal F .
--   $$
--
--   Each simulator sees only the corrupted party's own ideal output, and the simulated view is compared jointly with both outputs. This is the standard simulation-based definition for semi-honest adversaries and randomized functionalities (Goldreich, *Foundations of Cryptography*, Vol. II, Def. 7.2.1) in the perfect, information-theoretic, standalone setting that the paper adopts in §2 ("showing perfect conditional independence of messages given outputs. Isolated Real-Ideal simulations are straightforward").
--
--   **Formalization Note** Laws are probability mass functions (`PMF`); image laws are `PMF.map` and the simulated law is `PMF.bind` of $\mathcal F$ with the simulator. Simulators are arbitrary maps (no efficiency requirement), as the notion is information-theoretic. Correctness follows from either simulation clause by taking marginals; it is stated for readability.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), §2, paragraph "We take an entirely information-theoretic approach", p.2 (p. = PDF page; the PDF has no printed page numbers); Goldreich, Foundations of Cryptography Vol. II, Def. 7.2.1

import Mathlib

set_option autoImplicit false

namespace TetraOT

universe u v w x y

/-- **Perfect standalone security against semi-honest parties** for a two-party protocol without
inputs that realizes a randomized two-output functionality (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), §2, p.2: "We take an entirely
information-theoretic approach to Oblivious Transfer, contemplating semi-honest players and showing
perfect conditional independence of messages given outputs. Isolated Real-Ideal simulations are
straightforward …"; p. = PDF page, the PDF has no printed page numbers).

The protocol's randomness is `ω ∼ μ`. Alice's view is `viewA ω` and her output `outA ω`; Bob's view
is `viewB ω` and his output `outB ω`. `F` is the ideal functionality: the law of the pair of ideal
outputs. The protocol perfectly realizes `F` against a semi-honest party when

1. (correctness) the joint law of the real outputs `(outA, outB)` equals `F`;
2. (Alice corrupted) there is a simulator `SA`, which sees only Alice's ideal output `o₁` and
   samples a view `SA o₁`, such that the real joint law of (Alice's view, Alice's output, Bob's output)
   equals the ideal joint law of (`SA o₁`, `o₁`, `o₂`) with `(o₁, o₂) ∼ F`;
3. (Bob corrupted) likewise with a simulator `SB` that sees only Bob's ideal output `o₂`.

This is the standard simulation-based definition for semi-honest adversaries and randomized
functionalities (Goldreich, *Foundations of Cryptography* Vol. II, Def. 7.2.1), with no inputs, perfect
(equality of distributions) and standalone (no composition). The simulated view is compared jointly
with **both** outputs, so the honest party's output is part of the comparison.

**Formalization Note.** Laws are `PMF`s; `PMF.map` is the image law and `PMF.bind` the composition with
a Markov kernel. A simulator is any map from the corrupted party's ideal output to a distribution on
views (no computational restriction, since the notion is information-theoretic). Clause 1 follows from
either of clauses 2 and 3 by taking marginals; it is stated for readability. -/
def PerfectSemiHonestRealizes {Ω : Type u} {VA : Type v} {VB : Type w} {OA : Type x} {OB : Type y}
    (μ : PMF Ω) (viewA : Ω → VA) (viewB : Ω → VB) (outA : Ω → OA) (outB : Ω → OB)
    (F : PMF (OA × OB)) : Prop :=
  μ.map (fun ω => (outA ω, outB ω)) = F ∧
  (∃ SA : OA → PMF VA,
    μ.map (fun ω => (viewA ω, outA ω, outB ω)) =
      F.bind (fun o => (SA o.1).map (fun v => (v, o.1, o.2)))) ∧
  (∃ SB : OB → PMF VB,
    μ.map (fun ω => (viewB ω, outA ω, outB ω)) =
      F.bind (fun o => (SB o.2).map (fun v => (v, o.1, o.2))))

end TetraOT


