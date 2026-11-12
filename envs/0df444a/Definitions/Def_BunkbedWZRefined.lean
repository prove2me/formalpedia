-- Prove2me | Definitions.Def_BunkbedWZRefined
-- name    : BunkbedWZRefined
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-12T01:00:17.816527+00:00
-- url     : https://prove2.me/theorems/e85adc80-8261-47e6-996f-f8e964f3c877
-- title:
--   The refined pair state space and the half-reflection involution
-- statement:
--   In the Wierman--Ziff model each hyperedge $e$ of a $3$-uniform hypergraph carries a *pair* of states, one for each level of the bunkbed, so the per-hyperedge state space is $\Upsilon \times \Upsilon$ with $25$ elements, where $\Upsilon = \{abc,\; a|b|c,\; a|bc,\; ab|c,\; ac|b\}$ records which of the three vertices a hyperedge connects.
--
--   Following Gladkov--Pak--Zimin we *refine* this space by splitting each of the two pairs $(abc,\,a|b|c)$ and $(a|b|c,\,abc)$ into a $+$ and a $-$ variant, with weights
--   $$\mathbb{P}\bigl[(abc,a|b|c)^{+}\bigr] = P_{ab|c}P_{ac|b}, \qquad \mathbb{P}\bigl[(abc,a|b|c)^{-}\bigr] = P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b},$$
--   and similarly for $(a|b|c,\,abc)$. The two weights sum to $P_{abc}P_{a|b|c}$, the weight of the unsplit pair, so the refinement changes no probability whatsoever. Its purpose is to provide a domain for the half-reflection involution: the $-$ variants are exactly the configurations in which a hyperedge lies wholly on one level, and it is the $+$ variants that the involution is able to move.
--
--   The refined space $\Upsilon^2_{\mathrm{ext}}$ has $27$ elements — the $23$ unsplit pairs together with the four variants — and is modelled here as $(\Upsilon \times \Upsilon) \sqcup \{0,1,2,3\}$, with a predicate $\texttt{legal}$ cutting out the two now-redundant copies of the split pairs on the left summand.
--
--   This file provides:
--
--   - $\texttt{toPair}$, the underlying pair of states, which is what determines the realised graph (the $+$ and $-$ variants of a pair have the *same* underlying pair, hence the same graph);
--   - $\texttt{wt}$, the refined weight;
--   - $\texttt{inLamSq}$, membership in the $16$-element set $\Lambda^2_{+}$, where $\Lambda = \{abc, ab|c, ac|b, a|b|c\}$ is $\Upsilon$ with the state $a|bc$ removed, and the two split pairs are represented by their $+$ variants only;
--   - $\texttt{rho}$, the reflection involution exchanging the two levels;
--   - $\texttt{eta}$, the half-reflection involution of Definition 3.6, which is the identity on $\Omega_0$, coincides with $\texttt{rho}$ on $\Omega_1$, and on $\Xi$ exchanges $(abc,a|b|c)^{+} \leftrightarrow (ab|c,ac|b)$ and $(a|b|c,abc)^{+} \leftrightarrow (ac|b,ab|c)$.
--
--   **Mathematical role.** These are the ingredients of the involution argument by which Gladkov--Pak--Zimin prove their robustness lemma. The composite involution takes the first hyperedge along a distinguished path whose state lies in $\Lambda^2_+$, applies $\texttt{eta}$ there and $\texttt{rho}$ to every later hyperedge; it is weight-preserving and exchanges the two connection events, so the configurations meeting $\Lambda^2_+$ contribute *equally* to both and cancel from the difference. What remains are the configurations avoiding $\Lambda^2_+$ entirely, which is where the alternative model and Hollom's computation enter.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Sections 3.3-3.4 (pp. 3-5): the extended state space Upsilon^2_ext and Eq. [4] (p. 4), Definition 3.4 (refined pair set Lambda^2_+), Definition 3.5 (reflection involution) and Definition 3.6 (half-reflection involution).

import Definitions.Def_BunkbedHypergraph

/-!
# The refined pair state space and the half-reflection involution

Sections 3.3 and 3.4 of Gladkov-Pak-Zimin, *The bunkbed conjecture is false*,
PNAS 122 (2025) e2420725122.

In the Wierman-Ziff model each hyperedge `e` carries a pair of states, one for each level, so the
per-hyperedge state space is `WZ x WZ` with 25 elements. Following the source we *refine* it by
splitting each of the two pairs `(abc, a|b|c)` and `(a|b|c, abc)` into a `+` and a `-` variant,
whose weights are `P_ab|c * P_ac|b` and `P_abc * P_a|b|c - P_ab|c * P_ac|b`. These sum to the
original weight `P_abc * P_a|b|c`, so the refinement does not change any probability; it exists
only to give the half-reflection involution a domain.

The refined space has 27 elements: the 23 ordinary pairs other than the two split ones, plus the
four variants. It is modelled here as `(WZ x WZ) + Fin 4`, with `legal` cutting out the two
now-redundant copies of the split pairs on the left summand.
-/

namespace Bunkbed.Hyper

/-- The refined per-hyperedge state space. `inl (a, b)` is the ordinary pair `(a, b)`; the four
right-hand elements are `(abc, a|b|c)+`, `(abc, a|b|c)-`, `(a|b|c, abc)+`, `(a|b|c, abc)-`. -/
abbrev WZExt := (WZ × WZ) ⊕ Fin 4

namespace WZExt

/-- The two pairs that get split are represented only on the right summand, so their copies on
the left are excluded. Exactly 27 of the 29 elements are legal. -/
def legal : WZExt → Bool
  | .inl (.abc, .a_b_c) => false
  | .inl (.a_b_c, .abc) => false
  | _ => true

/-- The underlying pair of WZ states, which is what determines the graph. -/
def toPair : WZExt → WZ × WZ
  | .inl p => p
  | .inr 0 => (.abc, .a_b_c)
  | .inr 1 => (.abc, .a_b_c)
  | .inr 2 => (.a_b_c, .abc)
  | .inr 3 => (.a_b_c, .abc)

/-- The refined weight. The `+` variants carry `P_ab|c * P_ac|b`, the `-` variants the
complementary `P_abc * P_a|b|c - P_ab|c * P_ac|b`. -/
def wt (P : WZ → ℚ) : WZExt → ℚ
  | .inl (a, b) => P a * P b
  | .inr 0 => P .ab_c * P .ac_b
  | .inr 1 => P .abc * P .a_b_c - P .ab_c * P .ac_b
  | .inr 2 => P .ab_c * P .ac_b
  | .inr 3 => P .abc * P .a_b_c - P .ab_c * P .ac_b

/-- Membership in `Λ²₊`: both components lie in `Λ = {abc, ab|c, ac|b, a|b|c}` (equivalently,
neither is `a|bc`), with the two split pairs represented by their `+` variants only. -/
def inLamSq : WZExt → Bool
  | .inl (.abc, .a_b_c) => false
  | .inl (.a_b_c, .abc) => false
  | .inl (a, b) => a != .a_bc && b != .a_bc
  | .inr 0 => true
  | .inr 1 => false
  | .inr 2 => true
  | .inr 3 => false

/-- The reflection involution: swap the two levels. It fixes the sign of a refined state. -/
def rho : WZExt → WZExt
  | .inl (a, b) => .inl (b, a)
  | .inr 0 => .inr 2
  | .inr 1 => .inr 3
  | .inr 2 => .inr 0
  | .inr 3 => .inr 1

/-- The half-reflection involution on `Λ²₊`, Definition 3.6. It is the identity on `Ω₀`, the
reflection on `Ω₁`, and swaps the `+` variants with the mixed pairs on `Ξ`. Outside `Λ²₊` it is
the identity. -/
def eta : WZExt → WZExt
  | .inr 0 => .inl (.ab_c, .ac_b)
  | .inr 2 => .inl (.ac_b, .ab_c)
  | .inl (.ab_c, .ac_b) => .inr 0
  | .inl (.ac_b, .ab_c) => .inr 2
  | .inl (.abc, .ab_c) => .inl (.ab_c, .abc)
  | .inl (.ab_c, .abc) => .inl (.abc, .ab_c)
  | .inl (.a_b_c, .ac_b) => .inl (.ac_b, .a_b_c)
  | .inl (.ac_b, .a_b_c) => .inl (.a_b_c, .ac_b)
  | q => q

end WZExt

end Bunkbed.Hyper


