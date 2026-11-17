-- Prove2me | Definitions.Def_HoneycombCodes_Supplement_kappaCh
-- name    : HoneycombCodes_Supplement_kappaCh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:33:53.63774+00:00
-- url     : https://prove2.me/theorems/45c4d9fa-a9ce-48a4-be0a-a8b6d69d0400
-- title:
--   Horn pairs $\mathcal K_m$, $\Gamma_{ch}$, $\Phi_{ch}$, the Horn–channel exponent $\kappa^{[r]}_{ch}(\delta)$ and $\mathfrak B_{PGM}(\delta)$
-- statement:
--   All logarithms are base $2$. For a positive semidefinite matrix $M$ of trace at most one, $S(M)=-\operatorname{tr}(M\log_2 M)$ with $0\log 0=0$. For $m\ge 1$ let
--
--   $$
--   \mathcal K_m=\{(K,L): K,L\in\mathrm{Herm}_m(\mathbb C),\ K,L\succeq 0,\ \operatorname{tr}(K+L)=1\},
--   $$
--
--   and for $(K,L)\in\mathcal K_m$ put
--
--   $$
--   \Gamma_{ch}(K,L)=2\operatorname{tr}(K^{1/2}L^{1/2}),\qquad \Phi_{ch}(K,L)=S(K)+S(L)-S(K+L).
--   $$
--
--   For $r\ge 0$ and $0<\delta<1/2$ the **Horn–channel exponent** at row level $r$ is
--
--   $$
--   \kappa^{[r]}_{ch}(\delta)=\inf\{\Phi_{ch}(K,L): (K,L)\in\mathcal K_{r+1},\ \Gamma_{ch}(K,L)>1-2\delta\},
--   $$
--
--   so level $r$ uses $(r+1)\times(r+1)$ matrices. A **density matrix** on $\mathbb C^d$ is a positive semidefinite matrix of trace one, and the **unrestricted finite-dimensional channel infimum** is
--
--   $$
--   \mathfrak B_{PGM}(\delta)=\inf\{\chi(\rho_0,\rho_1): d\ge 1,\ \rho_0,\rho_1\text{ density matrices on }\mathbb C^d,\ p_e(\rho_0,\rho_1)<\delta\},
--   $$
--
--   where $\chi(\rho_0,\rho_1)=S(\bar\rho)-\tfrac12(S(\rho_0)+S(\rho_1))$, $\bar\rho=(\rho_0+\rho_1)/2$, is the uniform-prior Holevo information and $p_e(\rho_0,\rho_1)=\tfrac12\operatorname{tr}(\rho_0\bar\rho^{-1/2}\rho_1\bar\rho^{-1/2})$ the uniform-prior pretty-good-measurement bit error (inverse square roots on the support).
--
--   These objects carry the Horn–channel hierarchy of Section 9 and its completeness for the pretty-good criterion (Appendix E).
--
--   **Formalization Note** $K^{1/2}$ is the continuous functional calculus square root; the trace in $\Gamma_{ch}$ is real for positive semidefinite $K,L$ and its real part is taken. $S$ is the published `QAlgorithms.vnEntropy`; $\chi$ and $p_e$ are the published `PrettyGoodCriterion.holevoUniform` and `PrettyGoodCriterion.pgmBitErrorUniform`. Both infima are real `sInf`s of nonempty sets bounded below by $0$, with the strict constraints of the paper; $\mathfrak B_{PGM}$ ranges over all pairs, not only output-symmetric ones.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §9, p.42 (PDF 44); Definition 9.2, eq. (103), p.43 (PDF 45); App. E.1, eqs. (139)–(140), (145), pp.65–67 (PDF 67–69)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_PrettyGoodCriterion_holevoUniform
import Definitions.Def_PrettyGoodCriterion_pgmError

set_option autoImplicit false

open scoped ComplexOrder

namespace HoneycombCodes.Supplement

/-- The **Horn pair set** `K_m = {(K, L) : K, L ∈ Herm_m(ℂ), K, L ⪰ 0, tr(K + L) = 1}`, Gay, Granha
Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51),
§9, p.42 (PDF 44).

**Formalization Note.** Matrices are `Matrix (Fin m) (Fin m) ℂ`; `Matrix.PosSemidef` includes the
Hermitian condition. -/
def InKset (m : ℕ) (K L : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  K.PosSemidef ∧ L.PosSemidef ∧ (K + L).trace = 1

/-- The **channel statistic** `Γ_ch(K, L) = 2 tr(K^{1/2} L^{1/2})`, arXiv:2608.20287v2, §9, p.42
(PDF 44).

**Formalization Note.** `K^{1/2}` is the positive square root `cfc Real.sqrt K` (continuous
functional calculus). The trace is real for positive semidefinite `K, L` (p.42); the real part is
taken. -/
noncomputable def GammaCh {m : ℕ} (K L : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  2 * ((cfc Real.sqrt K) * (cfc Real.sqrt L)).trace.re

/-- The **channel potential** `Φ_ch(K, L) = S(K) + S(L) − S(K + L)` with the subnormalized entropy
`S(M) = −tr(M log₂ M)` (`0 log 0 = 0`), arXiv:2608.20287v2, §9, p.42 (PDF 44).

**Formalization Note.** `S` is the published `QAlgorithms.vnEntropy`, `−Re tr(M log₂ M)` computed by
the continuous functional calculus with `Real.logb 2` (so `0 log 0 = 0`); it is evaluated on
positive semidefinite matrices of trace at most one, as on p.42, and imposes no trace condition. -/
noncomputable def PhiCh {m : ℕ} (K L : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  QAlgorithms.vnEntropy K + QAlgorithms.vnEntropy L - QAlgorithms.vnEntropy (K + L)

/-- The **Horn–channel exponent** at row level `r` (Definition 9.2, eq. (103)),
`κ^{[r]}_ch(δ) = inf {Φ_ch(K, L) : (K, L) ∈ K_{r+1}, Γ_ch(K, L) > 1 − 2δ}`, arXiv:2608.20287v2,
p.43 (PDF 45). Level `r` uses `(r + 1) × (r + 1)` matrices.

**Formalization Note.** A real `sInf` of the set of objective values over the strictly feasible
pairs (the paper's strict constraint). For `0 < δ < 1/2` the set is nonempty
(`K = L = I/(2(r + 1))` has `Γ_ch = 1`) and bounded below by `0` (`Φ_ch` is a Holevo quantity), so
this is the printed infimum. -/
noncomputable def kappaCh (r : ℕ) (δ : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ K L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
    InKset (r + 1) K L ∧ 1 - 2 * δ < GammaCh K L ∧ v = PhiCh K L}

/-- A **density matrix** on `ℂ^d`: positive semidefinite (Hermitian) with trace one,
arXiv:2608.20287v2, App. E.1, p.65 (PDF 67). -/
def IsDensity {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The **unrestricted finite-dimensional channel infimum** (145),
`B_PGM(δ) = inf {χ(ρ₀, ρ₁) : d ≥ 1, ρ₀, ρ₁ density matrices on ℂ^d, p_e(ρ₀, ρ₁) < δ}`,
arXiv:2608.20287v2, App. E.1, p.67 (PDF 69); Theorem 1.3(c), p.5 (PDF 7).

**Formalization Note.** `χ` is the uniform-prior Holevo information (139), the published
`PrettyGoodCriterion.holevoUniform`, and `p_e` the uniform-prior PGM bit error, the published
`PrettyGoodCriterion.pgmBitErrorUniform` (inverse square roots on the support), which equals the
binary formula (140) `p_e = ½ tr(ρ₀ ρ̄^{−1/2} ρ₁ ρ̄^{−1/2})`. The pair is any pair of density matrices
(not only output-symmetric ones), the constraint is strict, and the infimum is a real `sInf`; the
set is nonempty (orthogonal pure states have `p_e = 0`) and bounded below by `0`. -/
noncomputable def BPGM (δ : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (d : ℕ) (ρ : Fin 2 → Matrix (Fin d) (Fin d) ℂ), 1 ≤ d ∧
    (∀ b, IsDensity (ρ b)) ∧ PrettyGoodCriterion.pgmBitErrorUniform ρ < δ ∧
    v = PrettyGoodCriterion.holevoUniform ρ}

end HoneycombCodes.Supplement


