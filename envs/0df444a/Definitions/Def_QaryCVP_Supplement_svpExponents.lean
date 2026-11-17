-- Prove2me | Definitions.Def_QaryCVP_Supplement_svpExponents
-- name    : QaryCVP_Supplement_svpExponents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:13:34.013522+00:00
-- url     : https://prove2.me/theorems/3bb83115-2b89-4cf5-b2db-8b3db16ebb15
-- title:
--   The constants of Algorithm 4, the rule (46), Table 2, the per-$a$ exponents $T_{in}(a),S_{in}(a)$, the exponents of Theorem 5.8, and the objective (45) with its parameter family
-- statement:
--   The **constants** of Algorithm 4 (§5.1) are rationals $\delta_0,\kappa,\lambda,\varepsilon,\eta$, integers $k,\nu$ and ratios $c_0,\dots,c_k$; they are *admissible* when $\delta_0\in(1/2,1)$, $\kappa\in(0,1)$, $\lambda,\varepsilon,\eta>0$, $c_0=1$, $c_1,\dots,c_k>0$, $k,\nu\ge1$. The **rule (46)** is $\delta_0=0.54$, $k=3$, $\kappa=10^{-8}$, $\lambda=10^{-9}$, $\eta=\varepsilon=10^{-10}$, $\nu=16$, $(c_0,c_1,c_2,c_3)=(1,0.874597414466,0.589775545104,0.310623936690)$. **Table 2** lists the seven rows $(D,T,S)$: $(1,0.27400949,0.261392024)$, $(1.05,0.286,0.270)$, $(1.10,0.298,0.276)$, $(1.20,0.326,0.286)$, $(1.30,0.361,0.309)$, $(1.40,0.408,0.320)$, $(1.50,0.468,0.329)$.
--
--   With $t_i=c_i(p_a(1)+\lambda)$ and $\rho=(1-\kappa)H(p_a)$, $T_{in}(a)$ and $S_{in}(a)$ are the exponents (9) of the common enumeration. The exponents of Theorem 5.8 are
--
--   $$T=\max\Big\{\frac{\delta_0}2,\ \sup_{a>0:\ \delta_0\le H(p_a)\le D}\Big(H(r_a)+\varepsilon+\frac{T_{in}(a)}{1-\kappa}\Big)\Big\},\qquad S=\max\Big\{\frac{\delta_0}4,\ \sup_{a>0:\ \delta_0\le H(p_a)\le D}\frac{S_{in}(a)}{1-\kappa}\Big\}.$$
--
--   A **choice** for (45) is a depth $k$, a cutoff $\delta_0$, tolerances $\varepsilon,\eta$, a rate $\rho(a)$ and proportions $t_i(a)$ depending on $a$, and a margin $\mu$; it is **feasible** when $k\ge1$, $\delta_0\in(1/2,1)$, $\varepsilon,\eta,\mu>0$ and, for every $a>0$ with $\delta_0\le H(p_a)\le1$: $\rho\ge\mu$, $\mu\le t_i\le1/2-\mu$, the coordinate conditions (3) (non-strict), the equation conditions (5) and the even-modulus conditions (8) with margin $\mu$, and the padding condition (72) $t_0H(p_a)/\rho\ge p_a(1)+\varepsilon+\mu$. Its **complete time objective** (45) is
--
--   $$\max\Big\{\frac{\delta_0}2,\ \sup_{a>0:\ \delta_0\le H(p_a)\le1}\Big[H(r_a)+\varepsilon+\max_{\substack{0\le w\le1\\|w-2p_a(1)|\le2\varepsilon}}G\Big(\frac{(1-2t_0)H(p_a)}{\rho},w\Big)+T_{in}\frac{H(p_a)}{\rho}\Big]\Big\}.$$
--
--   The module also records the strict conditions that Theorem 5.7 imposes on its compact set of tuples $(\rho,t_0,\dots,t_k)$.
--
--   **Formalization Note** Suprema are real `sSup`s of bounded nonempty images (the theorems assume the continuity, or the margins, that make them so). The decimals are exact rationals.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §5.1, p.49; p.54 (T_in(a), S_in(a)); Theorem 5.8, p.54; (44)–(46) and Table 2, p.56; G.1, (72)–(74), pp.104–105; Theorem 5.7, pp.52–53

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_QaryCVP_ent3
import Definitions.Def_QaryCVP_Supplement_thetaDist

namespace QaryCVP.Supplement

/-- The constants of Algorithm 4 (Section 5.1, p.49: "Fix rational constants `δ₀ ∈ (1/2, 1)`,
`κ ∈ (0, 1)`, `λ, ε, η > 0`, a fixed number `k ≥ 1` of decomposition steps, rational constants
`c₀ = 1, c₁, …, c_k > 0`, and an integer `ν ≥ 1` for the list limits").
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §5.1, p.49.

**Formalization Note.** `lam` is `λ` (a Lean keyword). The ratios are a sequence `c : ℕ → ℚ`, of
which only `c 0, …, c k` are used. -/
structure Params where
  δ0 : ℚ
  κ : ℚ
  lam : ℚ
  ε : ℚ
  η : ℚ
  k : ℕ
  ν : ℕ
  c : ℕ → ℚ

/-- The ranges of the constants fixed in §5.1 (p.49) and in Theorems 5.7 and 5.8:
`δ₀ ∈ (1/2, 1)`, `κ ∈ (0, 1)`, `λ, ε, η > 0`, `c₀ = 1`, `c₁, …, c_k > 0`, `k ≥ 1`, `ν ≥ 1`. -/
def Params.Admissible (P : Params) : Prop :=
  1 / 2 < P.δ0 ∧ P.δ0 < 1 ∧ 0 < P.κ ∧ P.κ < 1 ∧ 0 < P.lam ∧ 0 < P.ε ∧ 0 < P.η ∧ P.c 0 = 1 ∧
    (∀ i, 1 ≤ i → i ≤ P.k → 0 < P.c i) ∧ 1 ≤ P.k ∧ 1 ≤ P.ν

/-- The constants (46), p.56 (= (74), p.104): `δ₀ = 0.54`, `k = 3`, `κ = 10⁻⁸`, `λ = 10⁻⁹`,
`η = ε = 10⁻¹⁰`, `ν = 16`, `(c₀, c₁, c₂, c₃) = (1, 0.874597414466, 0.589775545104, 0.310623936690)`.
The decimals are exact rationals. -/
def rule46 : Params where
  δ0 := 54 / 100
  κ := 1 / 10 ^ 8
  lam := 1 / 10 ^ 9
  ε := 1 / 10 ^ 10
  η := 1 / 10 ^ 10
  k := 3
  ν := 16
  c := fun i => if i = 0 then 1 else if i = 1 then 874597414466 / 10 ^ 12
    else if i = 2 then 589775545104 / 10 ^ 12 else if i = 3 then 310623936690 / 10 ^ 12 else 0

/-- Table 2, p.56: the rows `(D, T, S)` of proved SVP bounds, the decimals as exact rationals. -/
def table2 : List (ℚ × ℚ × ℚ) :=
  [(1, 27400949 / 10 ^ 8, 261392024 / 10 ^ 9),
   (105 / 100, 286 / 1000, 270 / 1000),
   (110 / 100, 298 / 1000, 276 / 1000),
   (120 / 100, 326 / 1000, 286 / 1000),
   (130 / 100, 361 / 1000, 309 / 1000),
   (140 / 100, 408 / 1000, 320 / 1000),
   (150 / 100, 468 / 1000, 329 / 1000)]

/-- The limiting proportions `tᵢ = cᵢ(p_a(1) + λ)` at the counting parameter `a` (p.54). -/
noncomputable def tLim (P : Params) (a : ℝ) : ℕ → ℝ := fun i => (P.c i : ℝ) * (pa a 1 + P.lam)

/-- `T_in(a)` (p.54): the time exponent (9) of the common enumeration (`QaryCVP.Tin`), evaluated at
`tᵢ = cᵢ(p_a(1) + λ)` and equation rate `ρ = (1 − κ)H(p_a)`, with margin `η`. -/
noncomputable def TinA (P : Params) (a : ℝ) : ℝ :=
  Tin P.k ((1 - P.κ) * entZ (pa a)) P.η (tLim P a)

/-- `S_in(a)` (p.54): the space exponent (9) (`QaryCVP.Sin`) at the same arguments as `TinA`. -/
noncomputable def SinA (P : Params) (a : ℝ) : ℝ :=
  Sin P.k ((1 - P.κ) * entZ (pa a)) P.η (tLim P a)

/-- The time exponent (41) of Theorem 5.8, p.54:
`max{δ₀/2, sup_{a>0: δ₀≤H(p_a)≤D} (H(r_a) + ε + T_in(a)/(1 − κ))}`.

**Formalization Note.** A real supremum (`sSup`) of the image of the compact range `aRange δ₀ D`;
every statement using it assumes `T_in` continuous on a neighbourhood of it, so the image is
bounded and nonempty. -/
noncomputable def svpTimeExp (P : Params) (D : ℝ) : ℝ :=
  max ((P.δ0 : ℝ) / 2)
    (sSup ((fun a => entZ (ra a) + P.ε + TinA P a / (1 - P.κ)) '' aRange P.δ0 D))

/-- The space exponent of Theorem 5.8, p.54: `max{δ₀/4, sup_{a>0: δ₀≤H(p_a)≤D} S_in(a)/(1 − κ)}`. -/
noncomputable def svpSpaceExp (P : Params) (D : ℝ) : ℝ :=
  max ((P.δ0 : ℝ) / 4) (sSup ((fun a => SinA P a / (1 - P.κ)) '' aRange P.δ0 D))

/-- Extend a tuple `(t₀, …, t_k)` to a sequence (zero beyond `k`). -/
def extT {k : ℕ} (s : Fin (k + 1) → ℝ) : ℕ → ℝ := fun i => if h : i < k + 1 then s ⟨i, h⟩ else 0

/-- The strict conditions that Theorem 5.7 (pp.52–53) requires on its compact set of tuples
`(ρ, t₀, …, t_k)`: `ρ > 0`, `0 < tᵢ < 1/2`, `tᵢ₋₁/2 < tᵢ < (1 − tᵢ₋₁)/2`, `d₀ > d₁ > ⋯ > d_k > 0`
with `d₀ = ρ`, `dᵢ = rᵢ − η`, and `h(2t₀) > d₀/2`, `h(2tᵢ) > dᵢ₋₁/2`,
`rᵢ > dᵢ/2 + 2tᵢ − tᵢ₋₁` (`1 ≤ i ≤ k`), with `rᵢ` the rates (4) (`QaryCVP.rRate`). -/
def StrictTuple (k : ℕ) (η : ℝ) (x : ℝ × (Fin (k + 1) → ℝ)) : Prop :=
  0 < x.1 ∧ StrictCoordCond k (extT x.2) ∧ EqCond k x.1 η (extT x.2) ∧
    ParityCond k x.1 η (extT x.2)

/-- A parameter choice in the family of (45) and Theorem G.2 (pp.56, 104–105, 111): a depth `k`, an
exact-search cutoff `δ₀`, a coordinate tolerance `ε`, an equation margin `η`, an equation rate
`ρ(a)` and proportions `t₀(a), …, t_k(a)` that may depend on the counting parameter `a`
(equivalently on the input density, `H(p_a) = δ + o(1)`), and a uniform positive margin `μ` for the
strict constraints. -/
structure Choice45 where
  k : ℕ
  δ0 : ℝ
  ε : ℝ
  η : ℝ
  ρ : ℝ → ℝ
  t : ℝ → ℕ → ℝ
  margin : ℝ

/-- Feasibility of a choice (G.1, pp.104–105; Theorem G.2, p.111): `k ≥ 1`, `δ₀ ∈ (1/2, 1)`,
`ε, η > 0`, and, with one margin `μ > 0`, for every `a > 0` with `δ₀ ≤ H(p_a) ≤ 1`:
`ρ ≥ μ`; `μ ≤ tᵢ ≤ 1/2 − μ` (`0 ≤ i ≤ k`); the coordinate conditions (3)
`tᵢ₋₁/2 ≤ tᵢ ≤ (1 − tᵢ₋₁)/2` (non-strict, as printed on p.15); the equation conditions (5)
`dᵢ₊₁ + μ ≤ dᵢ`, `d_k ≥ μ`; the even-modulus conditions (8) with margin `μ`; and the padding
condition (72) `t₀H(p_a)/ρ ≥ p_a(1) + ε + μ`. -/
def Feasible45 (C : Choice45) : Prop :=
  1 ≤ C.k ∧ 1 / 2 < C.δ0 ∧ C.δ0 < 1 ∧ 0 < C.ε ∧ 0 < C.η ∧ 0 < C.margin ∧
    ∀ a ∈ aRange C.δ0 1,
      C.margin ≤ C.ρ a ∧
      (∀ i ≤ C.k, C.margin ≤ C.t a i ∧ C.t a i ≤ 1 / 2 - C.margin) ∧
      (∀ i, 1 ≤ i → i ≤ C.k → C.t a (i - 1) / 2 ≤ C.t a i ∧ C.t a i ≤ (1 - C.t a (i - 1)) / 2) ∧
      (∀ i, i < C.k → dRate (C.ρ a) C.η (C.t a) (i + 1) + C.margin ≤ dRate (C.ρ a) C.η (C.t a) i) ∧
      C.margin ≤ dRate (C.ρ a) C.η (C.t a) C.k ∧
      C.ρ a / 2 + C.margin ≤ binEnt (2 * C.t a 0) ∧
      (∀ i, 1 ≤ i → i ≤ C.k →
        dRate (C.ρ a) C.η (C.t a) (i - 1) / 2 + C.margin ≤ binEnt (2 * C.t a i) ∧
        dRate (C.ρ a) C.η (C.t a) i / 2 + 2 * C.t a i - C.t a (i - 1) + C.margin ≤
          rRate (C.t a) i) ∧
      pa a 1 + C.ε + C.margin ≤ C.t a 0 * entZ (pa a) / C.ρ a

/-- The subset term of (45), p.56: `max_{0≤w≤1, |w − 2p_a(1)| ≤ 2ε} G((1 − 2t₀)H(p_a)/ρ, w)`.

**Formalization Note.** A real supremum over a nonempty compact interval (it contains `2p_a(1)`)
of a continuous function of `w`, hence attained: the maximum of the page. -/
noncomputable def subsetTerm (C : Choice45) (a : ℝ) : ℝ :=
  sSup ((fun w => Gfun ((1 - 2 * C.t a 0) * entZ (pa a) / C.ρ a) w) ''
    {w : ℝ | 0 ≤ w ∧ w ≤ 1 ∧ |w - 2 * pa a 1| ≤ 2 * C.ε})

/-- The complete time objective (45), p.56, of a choice:
`max{δ₀/2, sup_{a>0: δ₀≤H(p_a)≤1} [H(r_a) + ε + (subset term) + T_in · H(p_a)/ρ]}`, with `T_in` the
exponent (9) (`QaryCVP.Tin`) at `(k, ρ(a), η, t(a))`.

**Formalization Note.** A real supremum; on a feasible choice the bracket is bounded on the range
(`ρ ≥ μ`, all entropies are bounded), so `sSup` is the supremum of the page. -/
noncomputable def obj45 (C : Choice45) : ℝ :=
  max (C.δ0 / 2)
    (sSup ((fun a => entZ (ra a) + C.ε + subsetTerm C a +
      Tin C.k (C.ρ a) C.η (C.t a) * entZ (pa a) / C.ρ a) '' aRange C.δ0 1))

end QaryCVP.Supplement


