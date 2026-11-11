-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_APTASScheme
-- name    : BeyondConvexity_APTAS_APTASScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:13:22.736983+00:00
-- url     : https://prove2.me/theorems/a06e386a-45e7-43b9-911e-5e986c16afa2
-- title:
--   Effective exact rational no-augmentation APTAS
-- statement:
--   For a fixed polygon class $\mathcal P$, an effective scheme uses one finite-alphabet Turing machine. Its input is an integer accuracy index $k\ge2$ followed by the binary polygon instance. A computable exponent function $g(k)$ and integer additive bound $\delta(k)$ are fixed before the instance. On every valid class instance $I$ of binary length $L\ge2$, the same machine returns an exact rational packing with output length and runtime at most $L^{g(k)}$ and
--
--   $$
--   \operatorname{bins}(I)\le(1+1/k)\operatorname{OPT}(I)+\delta(k).
--   $$
--
--   For every real target $0<\varepsilon<1$, the definition explicitly uses $k=\lceil1/\varepsilon\rceil+1$, requires $k\ge2$ and $1/k\le\varepsilon$, and records the same machine's exact rational output, polynomial time, polynomial encoding length, and $(1+\varepsilon)\operatorname{OPT}(I)+\delta(k)$ bound. Comparison optima use real translations; output feasibility uses the original unit-square bins and polygonal regions. Correctness is promised on class inputs and does not require a decidable membership test.
--
--   This is the full effective conclusion to be established by Theorem 1, not an assumption on a validity record. Parameter-dependent polynomial coefficients are absorbed into the computable exponent because $L\ge2$. The existence of such a scheme is not asserted by this definition.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Definition 1, printed p.5 / PDF p.6; Theorem 1, printed p.7 / PDF p.8; Section 3 rational-accuracy bridge, printed p.9 / PDF p.10; Appendix D.9, printed pp.32–33 / PDF pp.33–34.

import Definitions.Def_BeyondConvexity_APTAS_PolynomialOn

noncomputable section

namespace BeyondConvexity.APTAS

open RSListDecodingCapacity.AllRates (encNat)

/-- Section 3's rational-accuracy bridge, also defined harmlessly off its intended domain. -/
def accuracyIndex (ε : ℝ) : ℕ := Nat.ceil (1 / ε) + 1

/-- The full effective conclusion of Theorem 1, not a hypothesis about a geometric
class. One finite-alphabet machine returns the exact rational packing being timed.
The integer additive constant and computable exponent are chosen before the input.
For L ≥ 2, parameter-dependent polynomial coefficients can be absorbed in the exponent. -/
def APTASScheme (P : Set Polygon) : Prop :=
  ∃ (M : BitMachine) (g δ : ℕ → ℕ),
    M.Finite ∧ Effective encNat encNat g ∧
    (∀ k : ℕ, 2 ≤ k → ∀ I : Instance, I.InClass P →
      ∃ out : Packing ℚ,
        M.Runs (encNat k ++ encInstance I) (encPacking out) ((inputLength I) ^ g k) ∧
        RationalPacking I out ∧
        (encPacking out).length ≤ (inputLength I) ^ g k ∧
        (out.bins : ℝ) ≤ (1 + 1 / (k : ℝ)) * OPT I + δ k) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      2 ≤ accuracyIndex ε ∧ 1 / (accuracyIndex ε : ℝ) ≤ ε ∧
      ∀ I : Instance, I.InClass P → ∃ out : Packing ℚ,
        M.Runs (encNat (accuracyIndex ε) ++ encInstance I) (encPacking out)
          ((inputLength I) ^ g (accuracyIndex ε)) ∧
        RationalPacking I out ∧
        (encPacking out).length ≤ (inputLength I) ^ g (accuracyIndex ε) ∧
        (out.bins : ℝ) ≤ (1 + ε) * OPT I + δ (accuracyIndex ε)

end BeyondConvexity.APTAS


