-- Prove2me | Definitions.Def_CompNonlocal_ASP_predictionAdvantage
-- name    : CompNonlocal_ASP_predictionAdvantage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:31.077421+00:00
-- url     : https://prove2.me/theorems/c02ff3f4-627c-450f-bb1e-c89d3ee04281
-- title:
--   Private prediction advantage in the coordinate game
-- statement:
--   For a public predictor $\mathcal A$ reading $T^+=(T,J)$:
--   $$\mathbb E\big[(B_R-\mathcal A(T^+))^2-(B_R-\hat B_S)^2\big],$$
--   where $T$ is an honest ASP transcript, $J$ is uniform on $\{1,2,3\}$, $B_R\in\{\pm1\}$ is the outcome of measuring $\sigma_J$ on $Q$, and $\hat B_S=(\hat r_S)_J$ with $\hat r_S$ the decoder's output.
--
--   **Formalization Note** The predictor's output is read as a real and clipped to $[-1,1]$; $J$ is given to it after the transcript.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 17, p.44; Definition 15, p.34

import Mathlib
import Definitions.Def_CompNonlocal_ASP
import Definitions.Def_CompNonlocal_decVec
import Definitions.Def_CompNonlocal_clipUnit
import Definitions.Def_CompNonlocal_pauli

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The sender's private prediction advantage over a public predictor in the coordinate game of an
ASP. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 17, p.44:
`E[(B_R − A(T⁺))² − (B_R − B̂_S)² | (T, S, Q) ← Prep(1^κ), J ← {1, 2, 3}, T⁺ := (T, J),
B_R ← outcome of measuring σ_J on Q, r̂_S ← ASP.Dec(S, msg_S, msg_R), B̂_S := (r̂_S)_J]`, with
Definition 15, p.34 (`Prep`, `T⁺ = (T, J)`; a public predictor "receives only T⁺").

**Formalization Note** `J` is uniform on `Fin 3` (the paper's `{1, 2, 3}`), given to the predictor
as `encNat J` after `msg_S ++ msg_R`. `B_R = +1` (resp. `−1`) is the `+1` (resp. `−1`) eigenvalue
outcome of `σ_J`, of probability `Tr(ζ (I ± σ_J)/2)`. The predictor's output is read as a real and
clipped to `[−1, 1]`. The three outputs are independent given `T` (the parties act on disjoint
registers). -/
noncomputable def ASP.predictionAdvantage (P : ASP) (κ : ℕ) (Pd : ICirc) : ℝ :=
  (1 / 3) * ∑ j : Fin 3, ∑ mS : Bits (P.Sen κ).outC.length, ∑ mR : Bits (P.Rec κ).outC.length,
    ∑ bR : Bool, ∑ e : Bits Pd.outC.length, ∑ d : Bits (P.Dec κ).outC.length,
      let sgn : ℝ := if bR then -1 else 1
      (P.prepared κ (List.ofFn mS) (List.ofFn mR) *
          ((1 / 2 : ℂ) • (1 + (sgn : ℂ) • pauli j))).trace.re *
        (Pd.effectOn 0 (List.ofFn mS ++ List.ofFn mR ++ encNat (j : ℕ))
          (fun t => decide (t = List.ofFn e))).trace.re *
        P.decProb κ (List.ofFn mS) (List.ofFn mR) (List.ofFn d) *
        ((sgn - clipUnit (decDyadic (List.ofFn e)).1) ^ 2 - (sgn - (decVec (List.ofFn d)) j) ^ 2)

end CompNonlocal


