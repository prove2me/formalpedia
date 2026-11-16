-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_StatComplete
-- name    : FourMsgQMA_Supplement_StatComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:25:39.488229+00:00
-- url     : https://prove2.me/theorems/5d6966f5-f712-4065-b243-e373d2ce1c9a
-- title:
--   Uniform statistical completeness of block commitments and vector BARGs (§§3.10–3.11)
-- statement:
--   **Uniform statistical completeness** of a somewhere-extractable block commitment $\mathrm{SC}$ (§3.10): for all polynomial $k,m$ and every $i^*\in[k]$, writing $\mathrm{Good}_{\mathrm{SC}}(hk)$ for "every honest opening of every block vector verifies",
--   $$
--   \Pr\big[\neg\mathrm{Good}_{\mathrm{SC}}(hk):(hk,td)\leftarrow\mathrm{SC.Setup}(1^\lambda,k,m,i^*)\big]\le\nu(\lambda)
--   $$
--   for a negligible $\nu$.
--
--   **Uniform statistical completeness** of a vector batch argument $B$ (§3.11): for all polynomial $k$, every relation of polynomial size and every $i^*\in[k]$, with $\mathrm{Good}_B(crs)$ meaning "every honest proof of every valid vector verifies",
--   $$
--   \Pr\big[\neg\mathrm{Good}_B(crs):(crs,td)\leftarrow B.\mathrm{Setup}(1^\lambda,k,R,i^*)\big]\le\nu(\lambda)
--   $$
--   for a negligible $\nu$.
--
--   Perfect completeness (the published `SEC.PerfectlyComplete`, `VectorBARG.PerfectlyComplete`) is the case $\nu=0$. Theorem 4.1 charges the bad-setup probabilities $\varepsilon_{\mathrm{sc}}$, $\varepsilon_B$, so it assumes only these statistical forms.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.10, p.18 (PDF 20); §3.11, p.20 (PDF 22); §4.3, p.29 (PDF 31)

import Mathlib
import Definitions.Def_FourMsgQMA_IndexBARG

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.10 (p.18, PDF 20) and §3.11 (p.20,
PDF 22): uniform statistical completeness of a block commitment and of a vector batch argument.
"Uniform statistical completeness requires a negligible `ν` with `Pr[¬Good_SC(hk) : (hk, td) ←
Setup(1^λ, k, m, i*)] ≤ ν(λ)`. Perfect completeness means zero failure probability." and
"Uniform statistical completeness requires `Pr[¬Good_B(crs) : (crs, td) ← Setup(1^λ, k, R, i*)] ≤
ν(λ)` for a negligible `ν`. Perfect completeness has `ν = 0`."

The published `FourMsgQMA.SEC.PerfectlyComplete` and `FourMsgQMA.VectorBARG.PerfectlyComplete` are
the `ν = 0` cases. Theorem 4.1 charges the bad-setup probabilities `ε_sc`, `ε_B` (p.29), so it
assumes only these statistical forms.
-/

namespace Supplement

open Classical QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- Uniform statistical completeness of a block commitment (§3.10, p.18): for all polynomial `k, m`
and every `i* ∈ [k]` (a sequence `i*(λ)`), the probability over the setup coins that `Good_SC(hk)`
fails is at most a negligible `ν(λ)`. -/
def secStatComplete (S : SEC) : Prop :=
  ∀ k m istar : ℕ → ℕ, PolyBound k → PolyBound m → (∀ lam, 1 ≤ istar lam ∧ istar lam ≤ k lam) →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      avgCoins (S.setupCoins lam (k lam) (m lam)) (fun r =>
        if S.Good (k lam) (m lam) (S.setup lam (k lam) (m lam) (istar lam) r).1 then 0 else 1) ≤ ν lam

/-- Uniform statistical completeness of a vector batch argument (§3.11, p.20): for all polynomial
`k`, every relation family `R(λ)` on `n(λ) + m(λ)` inputs of polynomial size `s_R = |R| + n + m`
and every `i* ∈ [k]`, the probability over the setup coins that `Good_B(crs)` fails is at most a
negligible `ν(λ)`. -/
def vbStatComplete (B : VectorBARG) : Prop :=
  ∀ (k n m istar : ℕ → ℕ) (R : ℕ → NandCircuit), PolyBound k →
    PolyBound (fun lam => relSize (n lam) (m lam) (R lam)) → (∀ lam, RelationOK (n lam) (m lam) (R lam)) →
    (∀ lam, 1 ≤ istar lam ∧ istar lam ≤ k lam) →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      avgCoins (B.setupCoins lam (k lam) (relSize (n lam) (m lam) (R lam))) (fun r =>
        if B.Good lam (k lam) (n lam) (m lam) (R lam)
            (B.setup lam (k lam) (n lam) (m lam) (R lam) (istar lam) r).1 then 0 else 1) ≤ ν lam

end Supplement

end FourMsgQMA


