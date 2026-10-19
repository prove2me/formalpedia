-- Prove2me | Definitions.Def_SOSInference_Means_Tarr
-- name    : SOSInference_Means_Tarr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:50.304328+00:00
-- url     : https://prove2.me/theorems/4f757cee-9fae-439f-a926-2084cbf1a2db
-- title:
--   §7.2.2 — the counting processes $N_n^{(i)}(t,\lambda)$ and first-arrival times $T_i(n,\lambda)$
-- statement:
--   Fix a model, $n\ge1$, an index $i\le n$ and a vector $\lambda\in\mathbb R^l$, and let $a_*(X_i,\lambda)=X_i+\lambda/2$. The **counting process** counts the points of the merged sample $\mathcal Z_{n+m}$, other than $X_i$, inside a shrinking ball around $a_*(X_i,\lambda)$:
--   $$N_n^{(i)}(t,\lambda)=\#\Big\{Z_j:\ \|Z_j-a_*(X_i,\lambda)\|_2^2\le \frac{t^{2/l}}{n^{2/l}},\ Z_j\ne X_i\Big\},\qquad t\ge0 .$$
--   Its **first-arrival time** is
--   $$T_i(n,\lambda)=\inf\{t\ge0:\ N_n^{(i)}(t,\lambda)\ge1\}.$$
--   Equivalently, $T_i(n,\lambda)^{2/l}/n^{2/l}$ is the squared distance from $X_i+\lambda/2$ to the nearest other point of the merged sample.
--
--   These are the objects of the technical Lemmas 1 and 2.
--
--   **Formalization Note** The count is over the indices of the merged family; "$Z_j\ne X_i$" is a condition on values, as printed. The infimum is a real infimum, which is $0$ by convention only when every $Z_j$ equals $X_i$ as a vector (an event of probability zero for $n\ge2$).
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 38, §7.2.2, N_n^{(i)}(t, λ); p. 40, T_i(n, λ)

import Mathlib
import Definitions.Def_SOSInference_Means_Model

/-!
# Sample out-of-sample inference: the counting processes `N_n^{(i)}(t, λ)` and first-arrival
# times `T_i(n, λ)`

Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4,
p. 38, §7.2.2 (`N_n^{(i)}(t, λ)`, `a*(X_i, λ) = X_i + λ/2`); p. 40 (`T_i(n, λ)`).
-/

namespace SOSInference.Means

noncomputable section

/-- The counting process (p. 38)
`N_n^{(i)}(t, λ) = #{Z_j : ‖Z_j − a*(X_i, λ)‖₂² ≤ t^{2/l}/n^{2/l}, Z_j ≠ X_i}`, with
`a*(X_i, λ) = X_i + λ/2`, computed from the `n`-sample.

**Formalization Note.** `Z_{n+m}` is the indexed family `Zfam` (`m = ⌊κn⌋`); the count is over
indices `j`, and "`Z_j ≠ X_i`" is a condition on values, as printed. -/
def Ncount {l : ℕ} (M : Model l) (n : ℕ) (i : Fin n) (lam : E l) (t : ℝ) (ω : M.Ω) : ℕ :=
  (Finset.univ.filter (fun j : Fin n ⊕ Fin (mOf M.κ n) =>
      ‖Zfam M n ω j - (M.X i ω + (1 / 2 : ℝ) • lam)‖ ^ 2 ≤
          t ^ ((2 : ℝ) / l) / (n : ℝ) ^ ((2 : ℝ) / l) ∧
        Zfam M n ω j ≠ M.X i ω)).card

/-- The first-arrival time (p. 40) `T_i(n, λ) = inf{t ≥ 0 : N_n^{(i)}(t, λ) ≥ 1}`.

**Formalization Note.** A real `sInf`; the set is empty (value `0` by convention) only if every
`Z_j` equals `X_i` as a vector, an event of probability `0` for `n ≥ 2`. -/
def Tarr {l : ℕ} (M : Model l) (n : ℕ) (i : Fin n) (lam : E l) (ω : M.Ω) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ Ncount M n i lam t ω}

end

end SOSInference.Means


