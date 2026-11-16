-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_BalanceTester
-- name    : RobustBoolPCSP_Supplement_BalanceTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:25:47.8996+00:00
-- url     : https://prove2.me/theorems/dc32b924-658c-4fbf-a9fe-b5cc0078b2e0
-- title:
--   The multi-scale balance tester of §6.1
-- statement:
--   For $\ell\ge2$ put $\eta=9^{-\ell}$, $w=3^{-\ell}$, $L=2\ell-1$, $r_j=3^{j-2\ell}$. For $f:\{0,1\}^N\to\{0,1\}$ with two correctly pinned constants, the tester has
--
--   1. two **shift blocks** of mass one: $X$ uniform, $Y^\pm$ obtained by turning each $0$ into $1$ (resp. each $1$ into $0$) with probability $\eta$, and the gadget $C_1=(x,z,y,y)$, $C_2=(y,z,x,x)$ with $x=f(X)$, $y=f(Y^\pm)$, $z=f(1-X)$, the two constraints sharing the block's weight;
--   2. for $j=1,\dots,L$ two **amplification blocks** of mass $w$: four query strings sampled columnwise from $\Lambda_{r_{j-1}}$ (root mean $3r$, heads uniform among the triples with two, resp. one, plus signs) and from its complement;
--   3. a positive and a negative **anchor block** of mass $w$: root pinned to $1$ (resp. $0$), heads columnwise uniform among triples with two ones (resp. one one).
--
--   The **error mass** with respect to $P$ (strong) or $Q$ (weak) is the sum of block masses times violation probabilities. The module also defines the biased means $\mathbb E_{\mu_r}f$, $\mu_r$ the product law with sign mean $r$.
--
--   This is the device that forces balanced long codes in the hardness reduction for $T^*$ (Theorem 6.5).
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §6.1, pp.44–47 (Lemma 6.2 gadget, μ_r and Λ_r p.46, parameters (53) and blocks p.47)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_Witness

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

/-- The probability of the bit `b` under the Bernoulli law with `P[1] = p`. -/
def bitProb (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- The probability of the word `x ∈ {0,1}^N` under the product of Bernoulli(`p`) laws. -/
noncomputable def wordProb {N : ℕ} (p : ℝ) (x : Fin N → Bool) : ℝ := ∏ k, bitProb p (x k)

/-- `E_{μ_r} f`: the mean of `f : {0,1}^N → {0,1}` under `μ_r`, "the product distribution on bit
strings for which the associated signs 2X_i − 1 have mean r" (p.46), i.e. `P[X_i = 1] = (1+r)/2`. -/
noncomputable def meanMu {N : ℕ} (r : ℝ) (f : (Fin N → Bool) → Bool) : ℝ :=
  ∑ x, wordProb ((1 + r) / 2) x * (if f x then 1 else 0)

/-- The complemented query string `1 − X`. -/
def cmplW {N : ℕ} (x : Fin N → Bool) : Fin N → Bool := fun k => !x k

/-- The indicator `1[t ∉ S]` of a four-bit tuple. -/
noncomputable def outside (S : Set (Fin 4 → Bool)) (t : Fin 4 → Bool) : ℝ :=
  Sᶜ.indicator (fun _ => (1 : ℝ)) t

/-- The cost of the disagreement gadget of Lemma 6.2 (p.44) with respect to the relation `S`
(`P` for strong, `Q` for weak cost): the constraints `C₁ = (x, z, y, y)` and `C₂ = (y, z, x, x)`
"receive equal shares of the weight of the gadget" (p.45), so the cost per unit gadget mass is
`(1[C₁ ∉ S] + 1[C₂ ∉ S]) / 2`. -/
noncomputable def gadgetCost (S : Set (Fin 4 → Bool)) (x y z : Bool) : ℝ :=
  (outside S ![x, z, y, y] + outside S ![y, z, x, x]) / 2

/-- Transition probability of the positive shift (p.47): "Obtain Y⁺ by independently changing each
zero of X to one with probability η." -/
def kPlus (η : ℝ) (x y : Bool) : ℝ :=
  if x then (if y then 1 else 0) else (if y then η else 1 - η)

/-- Transition probability of the negative shift (p.47): "Obtain Y⁻ by independently changing each
one to zero with the same probability." -/
def kMinus (η : ℝ) (x y : Bool) : ℝ :=
  if x then (if y then 1 - η else η) else (if y then 0 else 1)

/-- The cost of a **shift block** of unit mass (p.47): "Draw X uniformly. … Each block applies the
gadget with x = f(X), y = f(Y^±), and z = f(1 − X)." `kern` is `kPlus η` or `kMinus η`. -/
noncomputable def shiftCost {N : ℕ} (S : Set (Fin 4 → Bool)) (kern : Bool → Bool → ℝ)
    (f : (Fin N → Bool) → Bool) : ℝ :=
  ∑ X : Fin N → Bool, ∑ Y : Fin N → Bool,
    (1 / 2 : ℝ) ^ N * (∏ k, kern (X k) (Y k)) * gadgetCost S (f X) (f Y) (f (cmplW X))

/-- The distribution `Λ_r` on `P` (p.46): "In sign coordinates (S0, S1, S2, S3), the root has mean
3r. Given S0 = 1, choose the heads uniformly from the three triples with two plus signs. Given
S0 = −1, choose them uniformly from the three triples with one plus sign." In bits: each of the three
tuples of `P` with root `1` has probability `(1+3r)/6`, each of the three with root `0` has
probability `(1−3r)/6`, every tuple outside `P` probability `0`. -/
noncomputable def lamR (r : ℝ) (x : Fin 4 → Bool) : ℝ :=
  PStar.indicator (fun y => (1 + (if y 0 then 3 * r else -(3 * r))) / 6) x

/-- The complemented distribution of `Λ_r` ("Reversing every sign gives the corresponding formulas
for the complemented distribution", p.46). -/
noncomputable def lamRc (r : ℝ) (x : Fin 4 → Bool) : ℝ := lamR r (fun i => !x i)

/-- The cost of a **product test** of unit mass with column distribution `dist` on `{0,1}⁴`
(amplification blocks, p.47): "sample the four query strings coordinatewise from Λ_{r_{j−1}} and
apply f to each string." -/
noncomputable def prodTestCost {N : ℕ} (S : Set (Fin 4 → Bool)) (dist : (Fin 4 → Bool) → ℝ)
    (f : (Fin N → Bool) → Bool) : ℝ :=
  ∑ cols : Fin N → Fin 4 → Bool,
    (∏ n, dist (cols n)) * outside S (fun i => f (fun n => cols n i))

/-- The cost of an **anchor block** of unit mass with pinned root value `root` and head column
distribution `heads` on `{0,1}³` (p.47): "In the positive anchor, the root is pinned to one.
Generate the three head strings independently across coordinates, choosing each coordinate triple
uniformly from the triples with two ones. … The negative anchor is the complemented test, with the
root pinned to zero." The root is the correctly pinned global constant. -/
noncomputable def anchorCost {N : ℕ} (S : Set (Fin 4 → Bool)) (root : Bool)
    (heads : (Fin 3 → Bool) → ℝ) (f : (Fin N → Bool) → Bool) : ℝ :=
  ∑ cols : Fin N → Fin 3 → Bool, (∏ n, heads (cols n)) *
    outside S ![root, f (fun n => cols n 0), f (fun n => cols n 1), f (fun n => cols n 2)]

/-- Uniform distribution on the triples with exactly `c` ones (`c = 2` positive, `c = 1` negative
anchor). -/
noncomputable def headsUnif (c : ℕ) (h : Fin 3 → Bool) : ℝ :=
  if (Finset.univ.filter (fun i => h i = true)).card = c then 1 / 3 else 0

/-- The **balance tester** of §6.1 (pp.47) with parameter `ℓ`, `η = 9^{−ℓ}`, `w = 3^{−ℓ}`,
`L = 2ℓ − 1`, `r_j = 3^{j−2ℓ}` (53): the total error mass, with respect to `S` (`P` for strong,
`Q` for weak error mass), of the function `f : {0,1}^N → {0,1}` with both anchors correctly pinned.
"The mass of a block is its total constraint weight before normalization." Blocks: two shift blocks
of mass one; for `j = 1, …, L` the amplification blocks from `Λ_{r_{j−1}}` and its complement, of mass
`w` each; the positive and negative anchors, of mass `w` each. Here `j − 1` runs over `0, …, L − 1`
and `r_{j−1} = (1/3)^{2ℓ − (j−1)}`. -/
noncomputable def testerMass (S : Set (Fin 4 → Bool)) (ℓ N : ℕ) (f : (Fin N → Bool) → Bool) : ℝ :=
  let η : ℝ := (1 / 9 : ℝ) ^ ℓ
  let w : ℝ := (1 / 3 : ℝ) ^ ℓ
  shiftCost S (kPlus η) f + shiftCost S (kMinus η) f +
    w * ∑ j ∈ Finset.range (2 * ℓ - 1),
      (prodTestCost S (lamR ((1 / 3 : ℝ) ^ (2 * ℓ - j))) f +
        prodTestCost S (lamRc ((1 / 3 : ℝ) ^ (2 * ℓ - j))) f) +
    w * (anchorCost S true (headsUnif 2) f + anchorCost S false (headsUnif 1) f)

end RobustBoolPCSP.Supplement


