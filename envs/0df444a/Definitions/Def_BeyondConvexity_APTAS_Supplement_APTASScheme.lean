-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Supplement_APTASScheme
-- name    : BeyondConvexity_APTAS_Supplement_APTASScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:16:32.195445+00:00
-- url     : https://prove2.me/theorems/16a317a7-f047-49ec-a4f5-c8bc895ef76e
-- title:
--   Full effective dimensional APTAS conclusion
-- statement:
--   For fixed dimension $d$ and class $\mathcal P$, an APTAS means one finite-alphabet machine, a computable exponent $g:\mathbb N\to\mathbb N$ and an integer allowance $\delta:\mathbb N\to\mathbb N$ chosen before every input instance. For every $k\ge2$ and every valid class input $I$ of binary length $L\ge2$, that machine returns an exact rational feasible translation packing $A_k(I)$ with
--
--   $$\operatorname{bins}(A_k(I))\le(1+1/k)\operatorname{OPT}_d(I)+\delta(k).$$
--
--   The same returned packing has complete output length and actual machine time at most $L^{g(k)}$. The optimum permits real translations and the bins have side exactly one. For every real $0<\varepsilon<1$, the reused index $k=\lceil1/\varepsilon\rceil+1$ satisfies $k\ge2$ and $1/k\le\varepsilon$; the same machine at this index returns an exact rational packing with at most $(1+\varepsilon)\operatorname{OPT}_d(I)+\delta(k)$ bins and the same time and output-length guarantees. The allowance is independent of $I,n,L$ and need not be computable.
--
--   This is a conclusion to be established, not an algorithm oracle in either class hypothesis. Parameter-only polynomial coefficients are absorbed into the computable exponent because $L\ge2$.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), Definition 1, printed p.5 / PDF p.6; Section 3, printed p.9 / PDF p.10; Theorem 2, printed p.16 / PDF p.17; Appendix D.9, printed pp.32-33 / PDF pp.33-34

import Definitions.Def_BeyondConvexity_APTAS_Supplement_TranslationPacking
import Definitions.Def_BeyondConvexity_APTAS_APTASScheme

noncomputable section

namespace BeyondConvexity.APTAS.Supplement

open RSListDecodingCapacity.AllRates (encNat)

/-- Operational dimensional conclusion: the same machine produces the very
packing whose exact feasibility, bit length, time and approximation are checked.
Dimension and class are fixed outside all machine and parameter witnesses. -/
def APTASScheme {d : ℕ} (P : Set (PolyhedralRegion d)) : Prop :=
  ∃ (M : BitMachine) (g δ : ℕ → ℕ),
    M.Finite ∧ Effective encNat encNat g ∧
    (∀ k : ℕ, 2 ≤ k → ∀ I : Instance d, InClass I P →
      ∃ out : TranslationPacking d ℚ,
        M.Runs (encNat k ++ encInstance I) (encPacking out) ((inputLength I) ^ g k) ∧
        RationalPacking I out ∧
        (encPacking out).length ≤ (inputLength I) ^ g k ∧
        (out.bins : ℝ) ≤ (1 + 1 / (k : ℝ)) * (OPT I : ℝ) + δ k) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      2 ≤ accuracyIndex ε ∧ 1 / (accuracyIndex ε : ℝ) ≤ ε ∧
      ∀ I : Instance d, InClass I P → ∃ out : TranslationPacking d ℚ,
        M.Runs (encNat (accuracyIndex ε) ++ encInstance I) (encPacking out)
          ((inputLength I) ^ g (accuracyIndex ε)) ∧
        RationalPacking I out ∧
        (encPacking out).length ≤ (inputLength I) ^ g (accuracyIndex ε) ∧
        (out.bins : ℝ) ≤ (1 + ε) * (OPT I : ℝ) + δ (accuracyIndex ε)

end BeyondConvexity.APTAS.Supplement


