-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_OA
-- name    : RobustPrefLearn_MTP_OA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:19.231315+00:00
-- url     : https://prove2.me/theorems/58c1ef4b-7ab4-4e3f-a835-ac4c5998b015
-- title:
--   §6 and Appendices D–E, pp. 15–17, 57–63 — OA preferences f^OA_σ (3)–(4), σ̂_k (44), the sequences 𝔞_n, 𝔟_n, λ*_n (6), λ^OA_* (7), µ_m, µ* (50)–(51), u*, l*
-- statement:
--   This file defines the ordinal attraction (OA) preferences and the explicit quantities that describe the optimal display distribution.
--
--   1. **Restricted rank.** For a ranking $\sigma$, a display set $S$ and $X\in S$, $\sigma(X|S)=\sum_{k\in S}\mathbb 1\{\sigma(k)\le\sigma(X)\}$ is the rank of $X$ within $S$ (the top version of $S$ has $\sigma(X|S)=1$).
--   2. **OA preferences (3)–(4).** For every ranking $\sigma$,
--   $$f^{\mathrm{OA}}_\sigma(X|S)=\frac{1-p}{1-p^{|S|}}\,p^{\sigma(X|S)-1}\quad(X\in S),\qquad f^{\mathrm{OA}}_\sigma(X|S)=0\quad(X\notin S),$$
--   and $\mathcal M^{\mathrm{OA}}_p=\{f^{\mathrm{OA}}_\sigma\}$. $\overline{\mathcal M}^{\mathrm{OA}}_p(f)$ is the set of OA preferences whose top-ranked version differs from that of $f$.
--   3. **The ranking $\hat\sigma_k$ (44).** $\hat\sigma_k(i)=i+1$ for $i<k$, $\hat\sigma_k(k)=1$, $\hat\sigma_k(i)=i$ for $i>k$: version $k$ is moved to the top. $\overline\Sigma(\sigma_*)$ is the set of rankings whose top-ranked version is not version $1$.
--   4. **The sequences (6).** For $n\ge 2$,
--   $$\mathfrak a_n=\log\tfrac1p\,\bigl[1-np^{n-1}+(n-1)p^n\bigr],\qquad \mathfrak b_n=1-p^n,\qquad \lambda^*_n=\begin{cases}\mathfrak b_n\bigl(\tfrac1{\mathfrak a_n}-\tfrac1{\mathfrak a_{n+1}}\bigr), & n=2,\dots,K-1,\\ \mathfrak b_K/\mathfrak a_K, & n=K.\end{cases}$$
--   5. **The display distribution (7).** $\lambda^{\mathrm{OA}}_*(S)=\lambda^*_n/(\lambda^*_2+\dots+\lambda^*_K)$ if $S=[n]$ for some $n\in\{2,\dots,K\}$, and $0$ otherwise.
--   6. **The dual certificate (50)–(51).** $\mu_2=\mathfrak b_2/\mathfrak a_2$, $\mu_m=(\mathfrak b_m-\mathfrak b_{m-1})/\mathfrak a_m$ for $m=3,\dots,K$; $\mu^*(\bar\sigma)=\mu_m/(\mu_2+\dots+\mu_K)$ if $\bar\sigma=\hat\sigma_m$ with $m\in\{2,\dots,K\}$, and $0$ otherwise.
--   7. $u^*=1/(\lambda^*_2+\dots+\lambda^*_K)$ and $l^*=1/(\mu_2+\dots+\mu_K)$.
--
--   These are the closed forms in terms of which the paper identifies the hardest preferences and the optimal randomized display rule.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. The restricted rank $\sigma(X|S)$ stays 1-based (it is a count), so $p^{\sigma(X|S)-1}$ reads literally. $[n]$ is the set of versions with index $<n$. $\hat\sigma_k$ is Mathlib's `Fin.cycleRange k`, which sends $i<k$ to $i+1$, $k$ to $0$ and fixes $i>k$. In $\mu^*$ the version `m` with `m.val ≥ 1` is the paper's version $m.val+1$; the $\hat\sigma_m$ are pairwise distinct, so at most one term of the defining sum is nonzero.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), pp. 15–17, (3), (4), M̄^OA_p(f), (6), (7); p. 57, (44); pp. 62–63, Σ̄(σ*), (50), (51), Lemmas 7–8 (u*, l*)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Model

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-! # §6 (pp. 15–17) and Appendices D–E (pp. 57–63): the ordinal attraction (OA) preferences,
the rankings `σ̂_k`, the sequences `𝔞_n, 𝔟_n, λ*_n, µ_m` and the display distribution `λ^OA_*`. -/

/-- The restricted rank `σ(X|S) = ∑_{k ∈ S} 𝕀{σ(k) ≤ σ(X)}` (p. 15); it is **1-based**, as
printed (the top version of `S` has `σ(X|S) = 1`). -/
def relRank {K : ℕ} (σ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) : ℕ :=
  (S.1.filter (fun k => σ k ≤ σ X)).card

/-- The OA preference (3), p. 15:
`f^OA_σ(X|S) = (1 - p)/(1 - p^{|S|}) · p^{σ(X|S) - 1}` for `X ∈ S`, and `0` for `X ∉ S`. -/
noncomputable def oa {K : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin K)) : Pref K :=
  fun S X => if X ∈ S.1 then (1 - p) / (1 - p ^ S.1.card) * p ^ (relRank σ S X - 1) else 0

/-- `M^OA_p = {f^OA_σ : σ ∈ Σ}`, (4) p. 15. -/
def MOA {K : ℕ} (p : ℝ) : Set (Pref K) :=
  Set.range (oa (K := K) p)

/-- `M̄^OA_p(f)` (p. 15): the OA preferences whose top-ranked version differs from that of `f`. -/
def altOA {K : ℕ} (p : ℝ) (f : Pref K) : Set (Pref K) :=
  {g | g ∈ MOA p ∧ ∀ k k' : Fin K, IsTop f k → IsTop g k' → k ≠ k'}

/-- The ranking `σ̂_k` of (44), p. 57: version `k` gets the top rank, the versions before `k` move
down by one rank, the versions after `k` keep their rank. With 0-based versions and ranks:
`σ̂_k k = 0`, `σ̂_k i = i + 1` for `i < k`, `σ̂_k i = i` for `i > k`; this is `Fin.cycleRange k`. -/
def sigmaHat {K : ℕ} (k : Fin K) : Equiv.Perm (Fin K) :=
  Fin.cycleRange k

/-- `Σ̄(σ*)` (p. 62): the rankings whose top-ranked version is not version 1 (`⟨0, _⟩`). -/
def NotTopOne {K : ℕ} (σ : Equiv.Perm (Fin K)) : Prop :=
  ∀ k : Fin K, (σ k).val = 0 → k.val ≠ 0

instance {K : ℕ} (σ : Equiv.Perm (Fin K)) : Decidable (NotTopOne σ) := by
  unfold NotTopOne; infer_instance

/-- `𝔞_n = log(1/p) [1 - n p^{n-1} + (n - 1) p^n]`, (6) p. 17 (a product). -/
noncomputable def aSeq (p : ℝ) (n : ℕ) : ℝ :=
  Real.log (1 / p) * (1 - (n : ℝ) * p ^ (n - 1) + ((n : ℝ) - 1) * p ^ n)

/-- `𝔟_n = 1 - p^n`, (6) p. 17. -/
noncomputable def bSeq (p : ℝ) (n : ℕ) : ℝ :=
  1 - p ^ n

/-- `λ*_n`, (6) p. 17: `𝔟_n (1/𝔞_n - 1/𝔞_{n+1})` for `n = 2, …, K - 1` and `𝔟_K/𝔞_K` for
`n = K`. -/
noncomputable def lamStar (K : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  if n < K then bSeq p n * (1 / aSeq p n - 1 / aSeq p (n + 1)) else bSeq p n / aSeq p n

/-- `[n] = {1, …, n}`, i.e. the versions `0, …, n - 1`. -/
def prefixSet (K : ℕ) (n : ℕ) : Finset (Fin K) :=
  Finset.univ.filter (fun X => X.val < n)

/-- The display distribution (7), p. 17:
`λ^OA_*(S) = λ*_n/(λ*_2 + ⋯ + λ*_K)` if `S = [n]` for some `n ∈ {2, …, K}`, and `0` otherwise. -/
noncomputable def lamOA (K : ℕ) (p : ℝ) : DS K → ℝ :=
  fun S => if ∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n then
    lamStar K p S.1.card / ∑ m ∈ Finset.Icc 2 K, lamStar K p m else 0

/-- `µ_m`, (50) p. 63: `𝔟_2/𝔞_2` for `m = 2` and `(𝔟_m - 𝔟_{m-1})/𝔞_m` for `m = 3, …, K`. -/
noncomputable def muSeq (p : ℝ) (m : ℕ) : ℝ :=
  if m = 2 then bSeq p 2 / aSeq p 2 else (bSeq p m - bSeq p (m - 1)) / aSeq p m

/-- `µ*`, (51) p. 63: `µ*(σ̄) = µ_m/(µ_2 + ⋯ + µ_K)` if `σ̄ = σ̂_m` for a version `m ≥ 2`
(0-based `m.val ≥ 1`, paper index `m.val + 1`), and `0` otherwise. The `σ̂_m` are pairwise
distinct, so at most one summand is nonzero. -/
noncomputable def muStar (K : ℕ) (p : ℝ) (σ : Equiv.Perm (Fin K)) : ℝ :=
  ∑ m : Fin K, if 1 ≤ m.val ∧ σ = sigmaHat m then
    muSeq p (m.val + 1) / ∑ j ∈ Finset.Icc 2 K, muSeq p j else 0

/-- `u* = 1/(λ*_2 + ⋯ + λ*_K)` (Lemma 7, p. 63). -/
noncomputable def uStar (K : ℕ) (p : ℝ) : ℝ :=
  1 / ∑ n ∈ Finset.Icc 2 K, lamStar K p n

/-- `l* = 1/(µ_2 + ⋯ + µ_K)` (Lemma 8, p. 63). -/
noncomputable def lStar (K : ℕ) (p : ℝ) : ℝ :=
  1 / ∑ m ∈ Finset.Icc 2 K, muSeq p m

end RobustPrefLearn.MTP


