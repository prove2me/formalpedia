-- Prove2me | Definitions.Def_NonMarkovColorings_Main_LocalUniformity
-- name    : NonMarkovColorings_Main_LocalUniformity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:09:39.891851+00:00
-- url     : https://prove2.me/theorems/7898bdc8-1839-4081-bbf6-589b4331d975
-- title:
--   The $i$-times blocked subset $S_{c,i}(X)$ (Definition 6.1), $\varepsilon$-uniformity (Definition 5.1) and the event $\mathrm{LU}$ (Definition 5.3)
-- statement:
--   Let $\Delta$ be the maximum degree of $G$ and $d(v)$ the degree of $v$. For a labeling $X$, a vertex $v$, $S\subseteq N(v)$, a color $c$ and $i\in\mathbb N$ (Definition 6.1),
--   $$S_{c,i}(X)=\{w\in S: |(N(w)\setminus\{v\})\cap X^{-1}(c)|=i\}.$$
--   A labeling $X$ is **$\varepsilon$-uniform at $z^*$ for radius $R$** (Definition 5.1) if for every $v\in B_R(z^*)$:
--   (5.1) $\big||A(X,v)|-ke^{-d(v)/k}\big|\le\varepsilon k$;
--   (5.2) for all $c$, $|X^{-1}(c)\cap B_2(v)|\le 400\Delta$ and $|X^{-1}(c)\cap N(v)|\le 400\Delta/\log\Delta$;
--   (5.3) for all $c$ and all $0\le D\le\Delta$, $\Big||N_{\le D}(v)|-\sum_{w\in N_{\le D}(v),\,c\in A_v(X,w)}e^{d(w)/k}\Big|<\varepsilon\Delta$.
--   For $X_0$ and an update sequence $\vec\sigma$ of length $T$, $\mathrm{LU}(X_0,\vec\sigma,\varepsilon,z^*)$ (Definition 5.3) holds if $X_t$ is $\varepsilon$-uniform at $z^*$ for radius $\Delta^{1/10}$ for every $0\le t\le T$.
--
--   **Formalization Note.** `blockedSubset G X v S c i`, `IsEpsUniform G ε z R X`, `LU G ε z X0 σ`. $\log$ is `Real.log`; $\Delta^{1/10}$ is a real power and $B_R$ is `ballReal`.
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 41 Definition 6.1; pp. 33–34 Definitions 5.1, 5.3

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_GraphNotions
import Definitions.Def_NonMarkovColorings_Main_LabelingChain

/-!
# The i-times blocked subset, ε-uniformity and the local-uniformity event LU

Jain, Mizgerd, Vigoda, *Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling
and Local Uniformity*, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…),
Definition 6.1 p. 41, Definitions 5.1 and 5.3 pp. 33–34.

* `blockedSubset G X v S c i` is `S_{c,i}(X) = {w ∈ S : |(N(w) \ {v}) ∩ X⁻¹(c)| = i}`
  (Definition 6.1).
* `IsEpsUniform G ε z R X` is Definition 5.1 with `Δ = G.maxDegree`, `d(v) = G.degree v`:
  for every `v ∈ B_R(z)`,
  (5.1) `||A(X, v)| − k e^{−d(v)/k}| ≤ ε k`;
  (5.2) for every color `c`, `|X⁻¹(c) ∩ B_2(v)| ≤ 400 Δ` and `|X⁻¹(c) ∩ N(v)| ≤ 400 Δ / log Δ`;
  (5.3) for every color `c` and every `0 ≤ D ≤ Δ`,
  `||N_{≤D}(v)| − Σ_{w ∈ N_{≤D}(v), c ∈ A_v(X, w)} e^{d(w)/k}| < ε Δ`.
  The radius `R` is real; `B_R(z)` is `ballReal`.
* `LU G ε z X0 σ` is Definition 5.3: `X_t` is ε-uniform at `z` for radius `Δ^{1/10}` for every
  `0 ≤ t ≤ T`, where `X_t = run G X0 σ t`.
-/

namespace NonMarkovColorings.Main

noncomputable section

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S_{c,i}(X)`: the `w ∈ S` with exactly `i` vertices of color `c` in `N(w) \ {v}`. -/
def blockedSubset (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (X : V → Fin k) (v : V)
    (S : Finset V) (c : Fin k) (i : ℕ) : Finset V :=
  S.filter fun w => (((G.neighborFinset w).erase v).filter fun u => X u = c).card = i

/-- Definition 5.1: `X` is `ε`-uniform at `z` for radius `R`. -/
def IsEpsUniform (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (ε : ℝ) (z : V) (R : ℝ)
    (X : V → Fin k) : Prop :=
  ∀ v ∈ ballReal G R z,
    |((avail G X v).card : ℝ) - k * Real.exp (-((G.degree v : ℝ) / k))| ≤ ε * k ∧
    (∀ c : Fin k,
      (((ball G 2 {v}).filter fun u => X u = c).card : ℝ) ≤ 400 * (G.maxDegree : ℝ) ∧
      ((((G.neighborFinset v).filter fun u => X u = c).card : ℝ) ≤
        400 * (G.maxDegree : ℝ) / Real.log (G.maxDegree : ℝ))) ∧
    (∀ c : Fin k, ∀ D : ℕ, D ≤ G.maxDegree →
      |((lowDegNbrs G D v).card : ℝ) -
        ∑ w ∈ (lowDegNbrs G D v).filter (fun w => c ∈ availExcept G X v w),
          Real.exp ((G.degree w : ℝ) / k)| < ε * (G.maxDegree : ℝ))

/-- Definition 5.3: `LU(X0, σ, ε, z)` — every `X_t`, `0 ≤ t ≤ T`, is `ε`-uniform at `z` for
radius `Δ^{1/10}`. -/
def LU (G : SimpleGraph V) [DecidableRel G.Adj] {k T : ℕ} (ε : ℝ) (z : V) (X0 : V → Fin k)
    (σ : UpdSeq V k T) : Prop :=
  ∀ t : ℕ, t ≤ T →
    IsEpsUniform G ε z ((G.maxDegree : ℝ) ^ ((1 : ℝ) / 10)) (run G X0 σ t)

end

end NonMarkovColorings.Main


