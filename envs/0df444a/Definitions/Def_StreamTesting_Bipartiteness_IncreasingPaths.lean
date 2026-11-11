-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_IncreasingPaths
-- name    : StreamTesting_Bipartiteness_IncreasingPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:56:17.963862+00:00
-- url     : https://prove2.me/theorems/17409b80-d23a-4999-8a27-03628a6f660d
-- title:
--   Increasing paths, event E, and the exact cutoff
-- statement:
--   An increasing simple path of length $L$ consists of $L+1$ distinct vertices, consecutive graph adjacencies, and strictly increasing arrival positions. Event $E$ is the absence of such a path. For sufficiently large $n$, use
--
--   $$L(n)=\left\lceil\frac{4\log n}{\log\log n}\right\rceil,\qquad b_d(n)=\frac{nd^{L(n)}}{(L(n)+1)!}.$$
--
--   Lengths count edges. The natural logarithm and ceiling appear exactly as in the proof on p.41. All asymptotic assertions exclude the small-input logarithm defaults by an eventual threshold.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Lemma 19 and Appendix A.1, printed p.24 / PDF p.24.

import Definitions.Def_StreamTesting_Bipartiteness_Policy

noncomputable section

namespace StreamTesting.Bipartiteness

/-- An injective path with L edges whose L+1 vertices arrive in path order. -/
def IncreasingPath {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Order n) (L : ℕ) : Prop :=
  ∃ f : Fin (L + 1) → Fin n, Function.Injective f ∧
    (∀ i : Fin L, G.Adj (f i.castSucc) (f i.succ)) ∧
    StrictMono (fun i => σ.symm (f i))

/-- Event E for an explicit edge-length cutoff L. -/
def NoIncreasingPath {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Order n) (L : ℕ) : Prop :=
  ¬ IncreasingPath G σ L

/-- Exact witness in the proof of Lemma 19; used only for sufficiently large n. -/
def cutoff (n : ℕ) : ℕ := ⌈4 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))⌉₊

/-- The union-bound failure estimate from Appendix A.1. -/
def pathFailureBound (d n : ℕ) : ℝ :=
  (n : ℝ) * (d : ℝ) ^ cutoff n / ((cutoff n + 1).factorial : ℝ)

end StreamTesting.Bipartiteness


