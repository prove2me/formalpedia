-- Prove2me | Definitions.Def_PreservePast_Supplement_SpectralAchieves
-- name    : PreservePast_Supplement_SpectralAchieves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:21.950427+00:00
-- url     : https://prove2.me/theorems/227abc7f-960d-476f-a6cc-9973e3a40b8a
-- title:
--   Spectral-energy histories $\mathcal H_E(K,d)$, the excess $D_r$, $B$-bit response protocols and the rate $\Phi(E,K,d,\alpha)$
-- statement:
--   For $d\ge 2$ and $1\le E\le K\le d$ the **history class** is
--   $$\mathcal H_E(K,d)=\{Z\in\mathbb R^{K\times d}:\ \|Z\|_{\mathrm{op}}\le 1,\ \|Z\|_F^2\le E\}.$$
--   After $Z$ is encoded, a query reveals $L\in\mathbb R^{m\times K}$ with $\|L\|_F\le 1$ and a rank budget $r$. For $Y=LZ$ the response $W$ must have rank at most $r$ and Frobenius norm at most one, and its **excess** is
--   $$D_r(Y,W)=\|Y-W\|_F^2-\min_{\operatorname{rank}V\le r,\ \|V\|_F\le 1}\|Y-V\|_F^2 .$$
--   A $B$-bit retained-state protocol **achieves** tolerance $\alpha$ with failure probability $\delta$ if, for every fixed history in $\mathcal H_E(K,d)$ and every query, the response is feasible on every outcome and has excess at most $\alpha$ with probability at least $1-\delta$. $B^\ast$ is the least such width.
--
--   With $\lambda_j=\min\{1,E/j\}$ the **rate** is
--   $$\Phi(E,K,d,\alpha)=\max_{1\le j\le K:\ \lambda_j>\alpha} j\,[1+d\log(\lambda_j/\alpha)].$$
--
--   **Formalization Note** The output dimension $m$ and the rank budget $r$ are fixed parameters of a protocol, as in Theorem 20. The logarithm in $\Phi$ is base two. The comparator minimum and the maximum in $\Phi$ are an infimum and a supremum over nonempty sets on which they are attained (for $\Phi$: when $E\ge1$, $K\ge1$, $\alpha<1$).
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Appendix N, pp.66–67 (PDF pp.68–69), eqs. (240)–(242)

import Mathlib
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

open MeasureTheory Matrix

namespace PreservePast.Supplement

/-- **The spectral-energy history class** (240), p.66 (PDF p.68):
`𝓗_E(K, d) = {Z ∈ ℝ^{K×d} : ‖Z‖_op ≤ 1, ‖Z‖_F² ≤ E}`. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Appendix N. -/
def spectralClass (E : ℝ) (K d : ℕ) : Set (Matrix (Fin K) (Fin d) ℝ) :=
  {Z | WainwrightHDS.NucNorm.opNorm2 Z ≤ 1 ∧ LowRankMEG.frobNorm Z ^ 2 ≤ E}

/-- **The excess** (241), p.66 (PDF p.68):
`D_r(Y, W) = ‖Y − W‖_F² − min_{rank V ≤ r, ‖V‖_F ≤ 1} ‖Y − V‖_F²`.

**Formalization Note.** The minimum is a real `⨅` over the subtype of comparators; the set
contains `V = 0` and is compact, so the infimum is attained. -/
noncomputable def spectralExcess {m d : ℕ} (r : ℕ) (Y W : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  LowRankMEG.frobNorm (Y - W) ^ 2 -
    ⨅ V : {V : Matrix (Fin m) (Fin d) ℝ // V.rank ≤ r ∧ LowRankMEG.frobNorm V ≤ 1},
      LowRankMEG.frobNorm (Y - V.1) ^ 2

/-- **A B-bit retained-state protocol for future linear responses** (the contract of `B*` in
Theorem 20). P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Appendix N, pp.66–67 (PDF pp.68–69): "After encoding Z, a query reveals
L ∈ ℝ^{m×K} with ‖L‖_F ≤ 1 and a rank budget r ≥ 1. For Y = LZ, the response must have rank at
most r and norm at most one. … Let B* be the least register width giving excess at most α with
probability 1 − δ for each fixed history and query. Feasibility is required on every outcome."

**Formalization Note.** One coin space `Ω`; the encoder sees `Z` and the coins, the decoder the
message, the coins and `L`. The output dimension `m` and the rank budget `r` are fixed
parameters of the protocol, as in the statement of Theorem 20 ("m, r ≥ 1"). Rank and norm
feasibility hold for every coin value; the excess bound holds with probability `≥ 1 − δ`. -/
def SpectralAchieves {K d m B : ℕ} {Ω : Type*} [MeasurableSpace Ω] (E : ℝ) (r : ℕ) (α δ : ℝ)
    (P : Measure Ω) (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ Z, Measurable (enc Z)) ∧
    (∀ M L, Measurable (fun ω => Matrix.of.symm (dec M ω L))) ∧
    ∀ Z ∈ spectralClass E K d, ∀ L : Matrix (Fin m) (Fin K) ℝ, LowRankMEG.frobNorm L ≤ 1 →
      (∀ ω, (dec (enc Z ω) ω L).rank ≤ r ∧ LowRankMEG.frobNorm (dec (enc Z ω) ω L) ≤ 1) ∧
      ENNReal.ofReal (1 - δ) ≤ P {ω | spectralExcess r (L * Z) (dec (enc Z ω) ω L) ≤ α}

/-- **The rate** (242), p.67 (PDF p.69): with `λ_j = min{1, E/j}`,
`Φ(E, K, d, α) = max_{1 ≤ j ≤ K : λ_j > α} j[1 + d log(λ_j/α)]`.

**Formalization Note.** A real `⨆` over the finite set of admissible `j`, which contains `j = 1`
when `1 ≤ E`, `1 ≤ K` and `α < 1` (the range of Theorem 20). The logarithm is base two (§N.1:
"logarithms below are base two"); another base changes `Φ` by a bounded factor only. -/
noncomputable def spectralPhi (E : ℝ) (K d : ℕ) (α : ℝ) : ℝ :=
  ⨆ j : {j : ℕ // 1 ≤ j ∧ j ≤ K ∧ α < min 1 (E / j)},
    (j.1 : ℝ) * (1 + d * Real.logb 2 (min 1 (E / j.1) / α))

end PreservePast.Supplement


