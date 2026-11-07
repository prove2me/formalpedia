-- Prove2me | Definitions.Def_PDSEquiv_UnknownSize
-- name    : PDSEquiv_UnknownSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:52.302764+00:00
-- url     : https://prove2.me/theorems/471dc126-eb97-4846-91ae-f9240795af76
-- title:
--   The parameters (12) and the guarantees of the distinguishers $B$ and $D$ of Lemma 8.2
-- statement:
--   With $K_N=\lfloor N^c\rfloor$ and $n=\lfloor N^r\rfloor$, display (12) sets $\kappa=\bigl\lfloor\frac{1-q}{64}\cdot\frac{nK_N}{N}\bigr\rfloor$.
--
--   For an oracle program and an oracle, and an input condition at each size $N$:
--
--   1. **Guarantee of $B^O(H,N)$** (input $N$ and a graph $H$ on $[n]$): polynomially bounded runs for every $N$ and $H$; every query is $(G,k)$ with $G$ a graph on $[N]$ and $k\in[N]$; output in $\{-1,1\}$; for $N\ge N_1$, $\Pr_{H\sim\mathrm{ER}(n,q)}[B^O(H,N)=1]\le N^{-1}$ regardless of the input condition; and if the condition holds at $N\ge N_1$, $\Pr_{H\sim\mathrm{PDS}(n,j,p,q)}[B^O(H,N)=1]\ge\gamma$ for all $\kappa\le j\le n$.
--   2. **Guarantee of $D^O(G)$** (input a graph on $[N]$ only): the same run, query and output bounds, and for every $N\ge N_1$ satisfying the condition the (AD) acceptance bounds with exponent $c$ and constant $\gamma/2$.
--
--   These package the two conclusions of Lemma 8.2 for each of its cases.
--
--   **Formalization Note** $B$ receives $N$ explicitly, as on the page, since $|V(H)|=\lfloor N^r\rfloor$ does not determine $N$.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 8.2 and display (12), p.34

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Assertions

set_option autoImplicit false

namespace PDSEquiv

noncomputable section

/-!
# The parameters (12) and the guarantees of Lemma 8.2

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 8.2, p.34.

**Formalization Note.** `B^O(H, N)` has input cells `N`, then `enc H`, with `H` a graph on
`[⌊N^r⌋]`, since `|V(H)|` does not determine `N`. The time and query bounds are for every `N`, every
input graph and every oracle (quantified in the theorem). The acceptance bounds are as printed: the
bound on `ER(n, q)` for `B` holds regardless of the input condition; every other bound under it.
-/

/-- `κ = ⌊((1 − q)/64) · n K_N / N⌋` with `K_N = ⌊N^c⌋`, `n = ⌊N^r⌋`, display (12), p.34. -/
def kappaN (q r c : ℝ) (N : ℕ) : ℕ :=
  ⌊(1 - q) / 64 * ((floorPow N r : ℝ) * (floorPow N c : ℝ) / (N : ℝ))⌋₊

/-- The guarantee of `B^O(H, N)` in one case of Lemma 8.2, p.34, for one oracle, with input condition
`cond`: bounded runs, queries `(G, k)` with `G` on `[N]`, `k ∈ [N]`, values in `{−1, 1}`; for `N ≥ N₁`
acceptance at most `N⁻¹` on `ER(n, q)` regardless of the condition; under the condition, acceptance
at least `γ` on `PDS(n, j, p, q)` for all `κ ≤ j ≤ n`. -/
def UnknownSizeB (p q r c γ : ℝ) (N₁ e : ℕ) (B : Program) (Q : Oracle) (cond : ℕ → Prop) : Prop :=
  (∀ (N : ℕ) (H : Graph (floorPow N r)),
    HaltsWithin B Q (N :: enc H) ((N + 2) ^ e) ((N + 2) ^ e) ∧
      QueriesSatisfy B Q (N :: enc H) (IsGraphQueryK N) ∧
      OutputsSatisfy B Q (N :: enc H) IsValueOut) ∧
  (∀ N : ℕ, N₁ ≤ N →
    expect (erMass (floorPow N r) q) (fun H => outMass B Q (N :: enc H) acceptOut) ≤ (N : ℝ)⁻¹) ∧
  (∀ N : ℕ, N₁ ≤ N → cond N → ∀ j : ℕ, kappaN q r c N ≤ j → j ≤ floorPow N r →
    expect (pdsMass (floorPow N r) j p q) (fun H => outMass B Q (N :: enc H) acceptOut) ≥ γ)

/-- The guarantee of `D^O(G)` in one case of Lemma 8.2, p.34, for one oracle, with input condition
`cond`: bounded runs on a graph alone, with the same query form; and for every `N ≥ N₁` satisfying
the condition, the acceptance bounds in (AD) with exponent `c` and constant `γ/2`. -/
def UnknownSizeD (p q c γ : ℝ) (N₁ e : ℕ) (D : Program) (Q : Oracle) (cond : ℕ → Prop) : Prop :=
  (∀ (N : ℕ) (G : Graph N),
    HaltsWithin D Q (enc G) ((N + 2) ^ e) ((N + 2) ^ e) ∧
      QueriesSatisfy D Q (enc G) (IsGraphQueryK N) ∧
      OutputsSatisfy D Q (enc G) IsValueOut) ∧
  (∀ N : ℕ, N₁ ≤ N → cond N → holdsAt .AD p q c (γ / 2) (Behaviour.ofProgram D Q) N)

end

end PDSEquiv


