-- Prove2me | Definitions.Def_DenseProdQSAT_Testing_FiniteRanges
-- name    : DenseProdQSAT_Testing_FiniteRanges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:45.325223+00:00
-- url     : https://prove2.me/theorems/b67abfa5-9387-4fed-9b53-d015ace5e7f1
-- title:
--   Uniform fixed-cardinality subset probability and actual range growth
-- statement:
--   Let $U$ be a finite universe, $G\subseteq U$ a ground set, and $E$ an event on subsets. Uniform sampling without replacement has probability
--
--   $$\Pr_{S\sim\binom Gm}[E(S)]=\frac{|\{S\subseteq G:|S|=m,\ E(S)\}|}{|\binom Gm|}.$$
--
--   Every theorem using this probability ensures $m\le|G|$, so the denominator is positive. For a range family $\mathcal R\subseteq2^U$, its growth $\pi_{\mathcal R}(m)$ is the maximum number of distinct indicator vectors on an actual tuple of $m$ points of $U$. Tuples may repeat points even when $m>|U|$; the theorem applications have a nonempty universe. The definitions also name $\lceil A\varepsilon^{-1}\log(2/\varepsilon)\rceil$ and $\lceil K\varepsilon^{-3}\log(2/\varepsilon)\rceil$. They count sampled qudits and approximation terms respectively, and use natural logarithms.
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Definition 4.1 and sampling convention in Lemma 4.2; Eq. (3) p. 6 and Eq. (8) p. 15, p. 12

import Mathlib
set_option autoImplicit false

namespace DenseProdQSAT.Testing

/-- Probability under the uniform law on unordered m-subsets; used only for m ≤ |U|. -/
noncomputable def SubsetProbability {U : Type} [Fintype U] [DecidableEq U]
    (ground : Finset U) (m : ℕ) (event : Finset U → Prop) : ℝ := by
  classical
  exact (((ground.powersetCard m).filter event).card : ℝ) /
    ((ground.powersetCard m).card : ℝ)

noncomputable def TracePatterns {U : Type} [Fintype U] [DecidableEq U]
    (ℛ : Set (Finset U)) {m : ℕ} (z : Fin m → U) : Finset (Fin m → Bool) := by
  classical
  exact Finset.univ.filter (fun b => ∃ R ∈ ℛ, ∀ i, b i = decide (z i ∈ R))

/-- Actual maximum on tuples, allowing repeated points even when m exceeds |U|. -/
noncomputable def Growth {U : Type} [Fintype U] [DecidableEq U]
    (ℛ : Set (Finset U)) (m : ℕ) : ℕ := by
  classical
  exact (Finset.univ : Finset (Fin m → U)).sup (fun z => (TracePatterns ℛ z).card)

noncomputable def SampleSize (A ε : ℝ) : ℕ := ⌈A * ε⁻¹ * Real.log (2 / ε)⌉₊
noncomputable def ApproxSize (K ε : ℝ) : ℕ := ⌈K * ε⁻¹ ^ 3 * Real.log (2 / ε)⌉₊

end DenseProdQSAT.Testing


