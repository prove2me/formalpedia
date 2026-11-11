-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_DualCertificate
-- name    : BetterKMedian_LMPGreedy_DualCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:15.935067+00:00
-- url     : https://prove2.me/theorems/8ca8b30f-54de-4e0f-9d0f-906c36b97269
-- title:
--   Section B.3 — advice, Algorithm 2, Table 2 and (26): the dual certificate built from advice
-- statement:
--   Fix $n$, $\gamma$, $\tau$; $\varepsilon=\gamma-1$, $\theta=\varepsilon+\varepsilon^2$, $\omega=2\varepsilon+\varepsilon^2$, $\bar\omega=1-\omega$.
--
--   **Advice** (`Advice`, Definition B.6): $T^\star\in\{1,\dots,n\}$, weights $\mu^\star_j\in[0,1]$ for $\tau_j=T^\star$, and $\hat g^\star_n\in[0,1]$ when $T^\star=n$ (`IsAdvice`). **Property B.7** (`IsAdmissibleFrontier`): the $\mu^\star_j$ ($\tau_j=T^\star$) are non-increasing in $j$ with at most one strictly fractional entry, and all equal $1$ when $T^\star=n$. `IsAdmissible` is both.
--
--   (23) $\mu^C_j=1,\mu^\star_j,0$ for $\tau_j>,=,<T^\star$. **Algorithm 2** builds $\hat g_i=\hat g^A_i+\hat g^B_i$ backwards with $R_i=\sum_{k>i}\hat g_k$: $\hat g_n=\hat g^\star_n$ if $T^\star=n$ else $0$, $\hat g^A_n=\max\{0,\hat g_n-\bar\omega\}$, $\hat g^B_n=\min\{\hat g_n,\bar\omega\}$, $j_{\bar\omega}=n$ if $\hat g_n\ge\bar\omega$ else $0$; for $i=n-1,\dots,1$: if $R_i<\bar\omega$, $\hat g^A_i=0$, $\hat g^B_i=\mathcal G^B(i)=(1-\mu^C_i)\frac{R_i+\omega}{n-i}$ (24), and if moreover $R_i+\hat g^B_i\ge\bar\omega$ then $j_{\bar\omega}=i$, $\hat g^B_i=\bar\omega-R_i$, $\hat g^A_i=\frac{1-\mu^C_i-(n-i+1-\mu^C_i)\hat g^B_i}{n-i+1-\mu^C_i-\frac\varepsilon\omega z_i}$; otherwise $\hat g^A_i=\mathcal G^A(i)=\frac{1-\mu^C_i}{n-i+1-\mu^C_i-\frac\varepsilon\omega z_i}$ (25), $\hat g^B_i=0$; here $\chi_j=[1-R_{j-1}/\theta]^+$ and $z_i=\sum_{j>i}\mu^C_j\chi_j$. The advice is correct iff $R_0=1$ (`Rsuf … 0 = 1`).
--
--   Memberships $(\mu^A_j,\mu^B_j)=(1-\mu^C_j,0)$ for $j<j_{\bar\omega}$ and $(0,1-\mu^C_j)$ otherwise. **Table 2** with (26) gives $g_{i,j}=\mu^A_j(\hat g_i-\frac\varepsilon{\bar\omega}\hat g^B_i)+\mu^B_j\hat g_i+\mu^C_j(\hat g_i-\chi_j\frac\varepsilon\omega\hat g^A_i)$ (`gCert`); for $i>j$, $s_{i,j}=\mu^A_j(g^A_{i,j}+\varepsilon\mathbb 1[i=\tau_j+1])+\mu^B_j(g^B_{i,j}+\varepsilon\mathbb 1[i=\tau_j+1])$, else $0$ (`sCert`); $t_{\tau_j,j}=\mu^B_j[\bar\omega-R_{j-1}]^++\mu^C_j(1-R_{j-1})$, other $t=0$ (`tCert`).
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Section B.3, printed pp. 38–42 (PDF 40–44); constants of §B.2, printed p. 37 (PDF 39)

import Mathlib

set_option autoImplicit false

/-!
# The dual certificate built from advice (Section B.3: Definition B.6, Property B.7, (23)–(26),
# Algorithm 2, Table 2)

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, Section B.3, printed pp. 38–42 (PDF 40–44); constants θ, ω, ω̄ of §B.2,
printed p. 37 (PDF 39).

Everything is a function of `n`, `γ`, the first bidding times `τ` and the advice `Γ`, with
`ε = γ − 1`, `θ = ε + ε²`, `ω = 2ε + ε²`, `ω̄ = 1 − ω` (the section fixes `n ≥ 2`,
`γ ∈ (1, 1.224]`, `τ_j ∈ {j, …, n}`). The paper's 1-based indices are used throughout.

Algorithm 2 builds the row profile `ĝ_i = ĝ^A_i + ĝ^B_i` backwards from row `n` to row `1`,
with suffix sums `R_i = Σ_{k=i+1}^n ĝ_k`, and records the crossing index `j_ω̄`. It "returns ⊥"
unless `R_0 = 1`; the statements about it assume `R_0 = 1`. The matrix variables of Table 2 are
then combined with the memberships `µ^A, µ^B, µ^C` by (26).
-/

namespace BetterKMedian.LMPGreedy

open Finset

/-- Advice `Γ` (Definition B.6, p. 38): a threshold `T⋆`, weights `µ⋆_j` (used for the clients
with `τ_j = T⋆`), and the last-row value `ĝ⋆_n` (used only when `T⋆ = n`). Entries the
construction does not use are ignored. -/
structure Advice where
  /-- the threshold `T⋆` -/
  T : ℕ
  /-- the boundary weights `µ⋆_j` -/
  mu : ℕ → ℝ
  /-- the last-row value `ĝ⋆_n` -/
  gn : ℝ

namespace Advice

/-- **Definition B.6** (p. 38): `T⋆ ∈ {1, …, n}`, `µ⋆_j ∈ [0, 1]` for every client with
`τ_j = T⋆`, and `ĝ⋆_n ∈ [0, 1]` when `T⋆ = n`. -/
def IsAdvice (n : ℕ) (τ : ℕ → ℕ) (Γ : Advice) : Prop :=
  1 ≤ Γ.T ∧ Γ.T ≤ n ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ n → τ j = Γ.T → 0 ≤ Γ.mu j ∧ Γ.mu j ≤ 1) ∧
  (Γ.T = n → 0 ≤ Γ.gn ∧ Γ.gn ≤ 1)

/-- **Property B.7** (p. 38): the weights `{µ⋆_j}_{τ_j = T⋆}` are non-increasing in `j`, with at
most one entry strictly between `0` and `1`; and when `T⋆ = n`, `µ⋆_j = 1` for all `τ_j = n`. -/
def IsAdmissibleFrontier (n : ℕ) (τ : ℕ → ℕ) (Γ : Advice) : Prop :=
  (∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → τ j = Γ.T → τ k = Γ.T → Γ.mu k ≤ Γ.mu j) ∧
  (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n → τ j = Γ.T → τ k = Γ.T →
      (0 < Γ.mu j ∧ Γ.mu j < 1) → (0 < Γ.mu k ∧ Γ.mu k < 1) → j = k) ∧
  (Γ.T = n → ∀ j : ℕ, 1 ≤ j → j ≤ n → τ j = n → Γ.mu j = 1)

/-- Admissible advice: Definition B.6 together with Property B.7. -/
def IsAdmissible (n : ℕ) (τ : ℕ → ℕ) (Γ : Advice) : Prop :=
  Γ.IsAdvice n τ ∧ Γ.IsAdmissibleFrontier n τ

end Advice

/-- `ε = γ − 1`. -/
def epsOf (γ : ℝ) : ℝ := γ - 1
/-- `θ = ε + ε²` (§B.2, p. 37). -/
def thetaOf (γ : ℝ) : ℝ := epsOf γ + epsOf γ ^ 2
/-- `ω = 2ε + ε²` (§B.2, p. 37). -/
def omegaOf (γ : ℝ) : ℝ := 2 * epsOf γ + epsOf γ ^ 2
/-- `ω̄ = 1 − ω = 1 − 2ε − ε²` (§B.2, p. 37). -/
def omegaBarOf (γ : ℝ) : ℝ := 1 - omegaOf γ

/-- (23): the `C`-membership `µ^C_j = 1` if `τ_j > T⋆`, `µ⋆_j` if `τ_j = T⋆`, `0` if
`τ_j < T⋆`. -/
noncomputable def muC (τ : ℕ → ℕ) (Γ : Advice) (j : ℕ) : ℝ :=
  if Γ.T < τ j then 1 else if τ j = Γ.T then Γ.mu j else 0

/-- The state of Algorithm 2 while it builds the profile backwards: the components
`ĝ^A_i, ĝ^B_i` of the rows built so far (rows not yet built hold `0`) and the crossing index
`j_ω̄`. -/
structure ProfileState where
  /-- `ĝ^A_i` -/
  gA : ℕ → ℝ
  /-- `ĝ^B_i` -/
  gB : ℕ → ℝ
  /-- the crossing index `j_ω̄` -/
  jw : ℕ

namespace ProfileState

/-- The suffix sum `R_i = Σ_{k=i+1}^n ĝ_k` with `ĝ_k = ĝ^A_k + ĝ^B_k`. -/
noncomputable def R (n : ℕ) (st : ProfileState) (i : ℕ) : ℝ :=
  ∑ k ∈ Ioc i n, (st.gA k + st.gB k)

/-- `χ_j = [1 − R_{j−1}/θ]⁺` (p. 40). -/
noncomputable def chi (n : ℕ) (γ : ℝ) (st : ProfileState) (j : ℕ) : ℝ :=
  max (1 - st.R n (j - 1) / thetaOf γ) 0

/-- `z_i = Σ_{j=i+1}^n µ^C_j χ_j` (p. 40). -/
noncomputable def z (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (st : ProfileState) (i : ℕ) : ℝ :=
  ∑ j ∈ Ioc i n, muC τ Γ j * st.chi n γ j

end ProfileState

/-- Lines 1–3 of Algorithm 2: `ĝ_n = ĝ⋆_n` if `T⋆ = n` and `ĝ_n = 0` otherwise;
`ĝ^A_n = max{0, ĝ_n − ω̄}`, `ĝ^B_n = min{ĝ_n, ω̄}`; `j_ω̄ = n` if `ĝ_n ≥ ω̄`, else `j_ω̄ = 0`. -/
noncomputable def profileInit (n : ℕ) (γ : ℝ) (Γ : Advice) : ProfileState :=
  let gn : ℝ := if Γ.T = n then Γ.gn else 0
  { gA := fun k => if k = n then max 0 (gn - omegaBarOf γ) else 0
    gB := fun k => if k = n then min gn (omegaBarOf γ) else 0
    jw := if omegaBarOf γ ≤ gn then n else 0 }

/-- Lines 5–14 of Algorithm 2 for row `i < n`, given the rows `i + 1, …, n`. With
`R = R_i`, `µ = µ^C_i`, and `den = n − i + 1 − µ − (ε/ω) z_i`:
* if `R < ω̄` (B-phase): `ĝ^A_i = 0`, `ĝ^B_i = 𝒢^B(i) = (1 − µ)(R + ω)/(n − i)` (24); and if
  `R + ĝ^B_i ≥ ω̄` (the crossing), `j_ω̄ = i`, `ĝ^B_i = ω̄ − R`, and
  `ĝ^A_i = (1 − µ − (n − i + 1 − µ) ĝ^B_i) / den`;
* otherwise (A-phase): `ĝ^A_i = 𝒢^A(i) = (1 − µ)/den` (25), `ĝ^B_i = 0`. -/
noncomputable def profileRow (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (st : ProfileState)
    (i : ℕ) : ProfileState :=
  let R := st.R n i
  let μ := muC τ Γ i
  let ε := epsOf γ
  let den : ℝ := ((n : ℝ) - i + 1 - μ) - ε / omegaOf γ * st.z n γ τ Γ i
  if R < omegaBarOf γ then
    let gb : ℝ := (1 - μ) * ((R + omegaOf γ) / ((n : ℝ) - i))
    if omegaBarOf γ ≤ R + gb then
      let gb' := omegaBarOf γ - R
      { gA := Function.update st.gA i ((1 - μ - ((n : ℝ) - i + 1 - μ) * gb') / den)
        gB := Function.update st.gB i gb'
        jw := i }
    else
      { gA := Function.update st.gA i 0
        gB := Function.update st.gB i gb
        jw := st.jw }
  else
    { gA := Function.update st.gA i ((1 - μ) / den)
      gB := Function.update st.gB i 0
      jw := st.jw }

/-- The state of Algorithm 2 after the rows `n − 1, n − 2, …, n − m` of the loop (line 4). -/
noncomputable def profileAfter (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) : ℕ → ProfileState
  | 0 => profileInit n γ Γ
  | m + 1 => profileRow n γ τ Γ (profileAfter n γ τ Γ m) (n - 1 - m)

/-- The final state of Algorithm 2: rows `n − 1, …, 1` processed. -/
noncomputable def profile (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) : ProfileState :=
  profileAfter n γ τ Γ (n - 1)

/-- The row profile `ĝ_i = ĝ^A_i + ĝ^B_i` constructed by Algorithm 2. -/
noncomputable def ghat (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (i : ℕ) : ℝ :=
  (profile n γ τ Γ).gA i + (profile n γ τ Γ).gB i

/-- The suffix sums `R_i = Σ_{k=i+1}^n ĝ_k` of the constructed profile; `R_0 = Σ_{k=1}^n ĝ_k`.
Algorithm 2 returns `⊥` unless `R_0 = 1` ("correct" advice). -/
noncomputable def Rsuf (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (i : ℕ) : ℝ :=
  (profile n γ τ Γ).R n i

/-- The memberships `µ^A_j = 1 − µ^C_j` for `j < j_ω̄` (else `0`) and `µ^B_j = 1 − µ^C_j` for
`j ≥ j_ω̄` (else `0`) (p. 41). -/
noncomputable def muA (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (j : ℕ) : ℝ :=
  if j < (profile n γ τ Γ).jw then 1 - muC τ Γ j else 0

/-- See `muA`. -/
noncomputable def muB (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (j : ℕ) : ℝ :=
  if j < (profile n γ τ Γ).jw then 0 else 1 - muC τ Γ j

/-- `χ_j = [1 − R_{j−1}/θ]⁺` for the constructed profile. -/
noncomputable def chiFinal (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (j : ℕ) : ℝ :=
  (profile n γ τ Γ).chi n γ j

/-- Table 2 (p. 41), generation column: `g^A_{i,j} = ĝ_i − (ε/ω̄) ĝ^B_i`, `g^B_{i,j} = ĝ_i`,
`g^C_{i,j} = ĝ_i − χ_j (ε/ω) ĝ^A_i`; combined by (26):
`g_{i,j} = µ^A_j g^A_{i,j} + µ^B_j g^B_{i,j} + µ^C_j g^C_{i,j}`. -/
noncomputable def gCert (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (i j : ℕ) : ℝ :=
  let P := profile n γ τ Γ
  let ε := epsOf γ
  let gh := ghat n γ τ Γ i
  muA n γ τ Γ j * (gh - ε / omegaBarOf γ * P.gB i) +
  muB n γ τ Γ j * gh +
  muC τ Γ j * (gh - chiFinal n γ τ Γ j * (ε / omegaOf γ) * P.gA i)

/-- Table 2, deposit column, for `i > j`: `s^A_{i,j} = g^A_{i,j} + ε 1[i = τ_j + 1]`,
`s^B_{i,j} = g^B_{i,j} + ε 1[i = τ_j + 1]`, `s^C_{i,j} = 0`; every other deposit is `0`
(in particular `s_{j,j} = 0`); combined by (26). -/
noncomputable def sCert (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (i j : ℕ) : ℝ :=
  let P := profile n γ τ Γ
  let ε := epsOf γ
  let gh := ghat n γ τ Γ i
  let bonus : ℝ := if i = τ j + 1 then ε else 0
  if j < i then
    muA n γ τ Γ j * (gh - ε / omegaBarOf γ * P.gB i + bonus) +
    muB n γ τ Γ j * (gh + bonus) +
    muC τ Γ j * 0
  else 0

/-- Table 2, withdrawal column, at `i = τ_j` only: `t^A = 0`, `t^B_{τ_j,j} = [ω̄ − R_{j−1}]⁺`,
`t^C_{τ_j,j} = 1 − R_{j−1}`; every other withdrawal is `0`; combined by (26). -/
noncomputable def tCert (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (Γ : Advice) (i j : ℕ) : ℝ :=
  if i = τ j then
    muA n γ τ Γ j * 0 +
    muB n γ τ Γ j * max (omegaBarOf γ - Rsuf n γ τ Γ (j - 1)) 0 +
    muC τ Γ j * (1 - Rsuf n γ τ Γ (j - 1))
  else 0

end BetterKMedian.LMPGreedy


