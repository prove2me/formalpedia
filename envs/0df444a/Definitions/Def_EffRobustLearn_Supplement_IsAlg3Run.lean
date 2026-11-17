-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_IsAlg3Run
-- name    : EffRobustLearn_Supplement_IsAlg3Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:18:00.167707+00:00
-- url     : https://prove2.me/theorems/1e2cde90-7288-4cb5-89b5-8aca20b958ea
-- title:
--   Algorithm 3: online gradient ascent over low-degree polynomials, as a run relation with a work count
-- statement:
--   Algorithm 3, Online-Gradient-Ascent$(\bar S_{\mathrm{inp}},S_{\mathrm{ref}},\varepsilon,\delta)$ with degree $\ell$, constant $A$ and the algorithm's universal constant $C$. Set
--   $$
--   T=\Big\lceil\frac{(64CA^2(d+1))^{2\ell}}{\varepsilon^5}\Big\rceil,\qquad \alpha=\frac{4\varepsilon^{3/2}}{(CA^2(d+1))^\ell\sqrt T},
--   $$
--   $\bar S_{\mathrm{filt},0}=\bar S_{\mathrm{inp}}$ and $w_1=0$. For $t=1,\dots,T$, let $m_t=q_{w_t}$ and $h_t=\mathrm{sign}(q_{w_t})$, and let $\bar S_{\mathrm{filt},t}$ be the output of a run of WIPF$(\bar S_{\mathrm{filt},t-1},S_{\mathrm{ref}},m_t,\varepsilon,|\bar S_{\mathrm{inp}}|)$. With the gradient of Eq. (4.7),
--   $$
--   g_t=\sum_{(x,y)\in\bar S_{\mathrm{filt},t}}\frac{y(2+|m_t(x)|)-m_t(x)}{4|\bar S_{\mathrm{inp}}|(1+|m_t(x)|)}\psi_\ell(x)+\sum_{x\in S_{\mathrm{ref}}}\frac1{2|S_{\mathrm{ref}}|}\Big(\frac{m_t(x)}{1+|m_t(x)|}-h_t(x)\Big)\psi_\ell(x),
--   $$
--   set $w_{t+1}=\Pi_K(w_t+\alpha g_t)$. The output is $h(x)\sim\mathrm{Rad}(\bar h_T(x))$ with $\bar h_T=T^{-1}\sum_{t=1}^Th_t$.
--
--   The work of a run is $(N+m+1)^4$ for forming $M_\ell^{-1/2}$, plus, in each round, the work of its WIPF call and $(n+m+1)(N+1)^2$ for evaluating the features, forming $g_t$ and projecting. Here $N$ is the number of monomials of degree at most $\ell$.
--
--   **Formalization Note** Rounds are 1-based and $\mathrm{sign}(0)=+1$ (the base mission's `signPM`). Algorithm 3 is deterministic up to the maximizers chosen inside WIPF, so a run is a relation. The failure probability $\delta$ is an input that the body never reads, so it is not an argument. The output is represented by $\bar h_T$; the randomized $h$ has the same error.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Algorithm 3, p.20 (PDF p.21); Eq. (4.7), Lemma 4.5, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_signPM
import Definitions.Def_EffRobustLearn_Supplement_psi
import Definitions.Def_EffRobustLearn_Supplement_IsWIPFRun

namespace EffRobustLearn

namespace Supplement

/-! Algorithm 3 (online gradient ascent over low-degree polynomials) of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.20
(PDF p.21), with the gradient (4.7) of Lemma 4.5, p.21 (PDF p.22). -/

/-- The number of rounds `T := ⌈(64 C A² (d + 1))^{2ℓ} / ε⁵⌉` (Algorithm 3, line 3), for the algorithm's universal
constant `C = Calg`. -/
noncomputable def numRounds3 (Calg A : ℝ) (d ℓ : ℕ) (ε : ℝ) : ℕ :=
  ⌈(64 * Calg * A ^ 2 * ((d : ℝ) + 1)) ^ (2 * ℓ) / ε ^ 5⌉₊

/-- The step size `α := 4ε^{3/2} / ((C A² (d + 1))^ℓ √T)` (line 9). -/
noncomputable def stepSize3 (Calg A : ℝ) (d ℓ : ℕ) (ε : ℝ) : ℝ :=
  4 * ε ^ (3 / 2 : ℝ) /
    ((Calg * A ^ 2 * ((d : ℝ) + 1)) ^ ℓ * Real.sqrt (numRounds3 Calg A d ℓ ε))

/-- The gradient `g_t` of Eq. (4.7), with `m_t = q_{w_t}` and `h_t = sign(q_{w_t})`:
`g_t = ∑_{(x,y)∈S̄filt,t} (y(2 + |m_t(x)|) − m_t(x)) / (4|S̄inp|(1 + |m_t(x)|)) ψ_ℓ(x)
      + ∑_{x∈Sref} (1/(2|Sref|)) (m_t(x)/(1 + |m_t(x)|) − h_t(x)) ψ_ℓ(x)`. -/
noncomputable def gradG {d n m : ℕ} (ℓ : ℕ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (w : MonoIdx d ℓ → ℝ) (F : Finset (Fin n)) : MonoIdx d ℓ → ℝ :=
  fun k =>
    (∑ i ∈ F,
      (pm (Sinp i).2 * (2 + |qw ℓ Sref w (Sinp i).1|) - qw ℓ Sref w (Sinp i).1) /
        (4 * (n : ℝ) * (1 + |qw ℓ Sref w (Sinp i).1|)) * psi ℓ Sref (Sinp i).1 k) +
    ∑ j, (1 / (2 * (m : ℝ))) *
      (qw ℓ Sref w (Sref j) / (1 + |qw ℓ Sref w (Sref j)|) - signPM (qw ℓ Sref w (Sref j))) *
        psi ℓ Sref (Sref j) k

/-- The record of a run of Algorithm 3: iterates `w_t`, filtered samples `S̄filt,t` (as index sets) and the
numbers of rejections of the WIPF calls. -/
structure Alg3Run (d n ℓ : ℕ) where
  w : ℕ → MonoIdx d ℓ → ℝ
  F : ℕ → Finset (Fin n)
  k : ℕ → ℕ

/-- A run of Algorithm 3, Online-Gradient-Ascent(`S̄inp`, `Sref`, `ε`, `δ`), with degree `ℓ`, hypercontractivity
constant `A` and universal constant `C = Calg`:
`S̄filt,0 = S̄inp`, `w_1 = 0`, and for `t = 1, …, T`: `m_t = q_{w_t}`,
`S̄filt,t` is the output of a run of WIPF(`S̄filt,t−1`, `Sref`, `m_t`, `ε`, `|S̄inp|`), and
`w_{t+1} = Π_K(w_t + α g_t)`.

**Formalization Note.**
* Algorithm 3 is deterministic except for the choice of maximizers inside WIPF, so a run is a relation; the
  theorems hold for every run.
* The failure probability `δ` is an input of Algorithm 3 that its body never reads, so it is not an argument.
* Rounds are 1-based, `t ∈ [1, T]`; entries of the record outside the rounds it constrains are unused. -/
def IsAlg3Run {d n m : ℕ} (Calg A : ℝ) (ℓ : ℕ) (ε : ℝ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (run : Alg3Run d n ℓ) : Prop :=
  run.F 0 = Finset.univ ∧ run.w 1 = 0 ∧
    ∀ t ∈ Finset.Icc 1 (numRounds3 Calg A d ℓ ε),
      IsWIPFRun ℓ A ε Sinp Sref (qw ℓ Sref (run.w t)) (run.F (t - 1)) (run.F t) (run.k t) ∧
      run.w (t + 1) =
        projK (run.w t + stepSize3 Calg A d ℓ ε • gradG ℓ Sinp Sref (run.w t) (run.F t))

/-- The output `h̄_T := T⁻¹ ∑_{t=1}^T h_t` with `h_t = sign(q_{w_t})` (line 11, sign 0 = +1). The randomized
output `h(x) ∼ Rad(h̄_T(x))` has `err_D(h, c⋆) = err_D(h̄_T, c⋆)` (p.23). -/
noncomputable def alg3Hbar {d n m : ℕ} (Calg A : ℝ) (ℓ : ℕ) (ε : ℝ) (Sref : Fin m → Fin d → ℝ)
    (run : Alg3Run d n ℓ) (x : Fin d → ℝ) : ℝ :=
  (1 / (numRounds3 Calg A d ℓ ε : ℝ)) *
    ∑ t ∈ Finset.Icc 1 (numRounds3 Calg A d ℓ ε), signPM (qw ℓ Sref (run.w t) x)

/-- The work of a run of Algorithm 3.

**Formalization Note (cost model).** With `N = |MonoIdx d ℓ|` features and `N' = |MonoIdx d (2ℓ)|`:
forming `M_ℓ` and its pseudoinverse square root is one primitive charged `(N + m + 1)^4`; each round `t` is
charged its WIPF call (`wipfWork` on the input size `|S̄filt,t−1|` and its rejection count) plus
`(n + m + 1)(N + 1)^2` for evaluating `ψ_ℓ`, `q_{w_t}` and `h_t` on the samples, forming `g_t` and projecting onto
`K` in closed form. Real arithmetic, comparisons and square roots have unit cost. -/
noncomputable def alg3Work {d n : ℕ} (Calg A : ℝ) (ℓ : ℕ) (ε : ℝ) (m : ℕ) (run : Alg3Run d n ℓ) : ℕ :=
  (Fintype.card (MonoIdx d ℓ) + m + 1) ^ 4 +
    ∑ t ∈ Finset.Icc 1 (numRounds3 Calg A d ℓ ε),
      (wipfWork (Fintype.card (MonoIdx d (2 * ℓ))) (run.F (t - 1)).card m (run.k t) +
        (n + m + 1) * (Fintype.card (MonoIdx d ℓ) + 1) ^ 2)

end Supplement

end EffRobustLearn


