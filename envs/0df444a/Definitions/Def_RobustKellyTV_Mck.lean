-- Prove2me | Definitions.Def_RobustKellyTV_Mck
-- name    : RobustKellyTV_Mck
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:09.221665+00:00
-- url     : https://prove2.me/theorems/b6d4a5f7-784a-4e50-bca6-a98e980d01df
-- title:
--   Counts, smoothed predictor, empirical distribution and the adaptive clipped-Kelly process $M^{\mathrm{CK}}$
-- statement:
--   Let $N_i(t)=\sum_{r=1}^t\mathbf 1\{X_r=i\}$. For positive pseudocounts $\alpha_1,\dots,\alpha_d$ with $\alpha_+=\sum_i\alpha_i$, the **smoothed predictor** based on $T$ observations with count vector $N$ is $U_i=(N_i+\alpha_i)/(T+\alpha_+)$. The every-round predictor and factor are
--
--   $$\widehat U_{t-1,i}=\frac{N_i(t-1)+\alpha_i}{t-1+\alpha_+},\qquad E_t=E_{\widehat U_{t-1}},$$
--
--   and the **adaptive clipped-Kelly process** is
--
--   $$M^{\mathrm{CK}}_n=\prod_{t=1}^n E_t(X_t).$$
--
--   The **Laplace pseudocounts** are $\alpha_1=\dots=\alpha_d=1$. The empirical distribution after $n$ observations is $\bar S_{n,i}=N_i(n)/n$.
--
--   The factor of round $t$ depends only on $X_1,\dots,X_{t-1}$, which is what makes the process predictable.
--
--   **Formalization Note** With $X_t$ the coordinate $t-1$, round $t$ is indexed by $s=t-1$; the predictor uses coordinates $0,\dots,s-1$ and the factor is evaluated at coordinate $s$.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.2 eq. (15) p.8, (16) p.9, Theorem 2.6 p.9 (S̄_n), Lemma A.2 p.23

import Mathlib
import Definitions.Def_RobustKellyTV_oracleE

namespace RobustKellyTV

variable {d : ℕ}

/-- The count `N_i(t) = Σ_{r=1}^t 1{X_r = i}` of symbol `i` among the first `t` observations
(arXiv:2611.02130v1, p.8). Observation `X_r` is coordinate `r − 1` of `x : ℕ → Fin d`, so the
count runs over coordinates `0, …, t − 1`. -/
def count (x : ℕ → Fin d) (t : ℕ) (i : Fin d) : ℕ :=
  ((Finset.range t).filter (fun r => x r = i)).card

/-- The smoothed empirical predictor based on `T` observations with count vector `N` and positive
pseudocounts `α`: `Uᵢ = (Nᵢ + αᵢ) / (T + α₊)`, `α₊ = Σᵢ αᵢ` (arXiv:2611.02130v1, eq. (15), p.8, and
Lemma A.2, p.23). -/
noncomputable def smoothed (pc : Fin d → ℝ) (N : Fin d → ℕ) (T : ℕ) (i : Fin d) : ℝ :=
  ((N i : ℝ) + pc i) / ((T : ℝ) + ∑ j, pc j)

/-- The empirical distribution `S̄_{n,i} = N_i(n) / n` after `n` observations
(arXiv:2611.02130v1, Theorem 2.6, p.9, and (25), p.11). -/
noncomputable def empirical (x : ℕ → Fin d) (n : ℕ) (i : Fin d) : ℝ :=
  (count x n i : ℝ) / n

/-- The Laplace pseudocounts `α₁ = ⋯ = α_d = 1` (arXiv:2611.02130v1, eq. (16), p.9). -/
def laplace (d : ℕ) : Fin d → ℝ := fun _ => 1

/-- The adaptive clipped-Kelly wealth `M^CK_n = Π_{t=1}^n E_t(X_t)` with
`E_t = E_{Û_{t−1}}` and `Û_{t−1,i} = (N_i(t−1) + αᵢ)/(t − 1 + α₊)` (arXiv:2611.02130v1, eq. (15),
pp.8–9), for a pseudocount vector `α = pc`.

**Formalization Note.** With the paper's `X_t` = coordinate `t − 1`, the factor of round `t` is
indexed by `s = t − 1 ∈ range n`: the predictor uses the counts of coordinates `0, …, s − 1`, and the
factor is evaluated at coordinate `s`. `M^CK_n` reads only coordinates `0, …, n − 1`. -/
noncomputable def Mck (σ : Setting d) (pc : Fin d → ℝ) (n : ℕ) (x : ℕ → Fin d) : ℝ :=
  ∏ s ∈ Finset.range n, oracleE σ (smoothed pc (count x s) s) (x s)

end RobustKellyTV


