-- Prove2me | Definitions.Def_RobustQSC_infMu
-- name    : RobustQSC_infMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:24.346963+00:00
-- url     : https://prove2.me/theorems/4b1a0f21-22cb-4e54-ad9e-0a2272b70674
-- title:
--   Harmonic-mean weighted influence $\mathrm{Inf}_\mu$ and interior influence $\mathrm{Inf}^{\mathrm{int}(A)}_\mu$
-- statement:
--   The measure induced by $f$ is $\mu_f(x)=|f(x)|^2$. For $\mu$ on $\{0,1\}^n$ and $h:\{0,1\}^n\to\mathbb C$, the harmonic-mean weighted total influence is
--
--   $$
--   \mathrm{Inf}_\mu[h]=\sum_{i,x}\frac{2\mu(x)\mu(x+i)}{\mu(x)+\mu(x+i)}\Bigl|\frac{h(x)-h(x+i)}2\Bigr|^2.
--   $$
--
--   For $A\subseteq\{0,1\}^n$, the interior influence is
--
--   $$
--   \mathrm{Inf}^{\mathrm{int}(A)}_\mu(h)=\sum_{\substack{x,y\in A\\ y\sim x}}\frac{2\mu(x)\mu(y)}{\mu(x)+\mu(y)}\Bigl|\frac{h(x)-h(y)}2\Bigr|^2,
--   $$
--
--   and $\mathrm{Inf}_{\mathrm{unif}}$, $\mathrm{Inf}^{\mathrm{int}(A)}_{\mathrm{unif}}$ are these quantities for $\mu\equiv2^{-n}$.
--
--   These are the quantities in which the paper's uncertainty principle is phrased, and the interior version is what controls the covering number of low-influence functions on the good set.
--
--   **Formalization Note** Sums run over ordered pairs (each edge twice), as printed on pp.8, 22 and 48. An edge with $\mu(x)+\mu(x+i)=0$ has weight $0$ in Lean; this never happens for a measure of full support. The weight is the one on p.48, not the overview's misprint on p.17.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §2.3, p.8; Corollary 2, p.22; §6, p.48; Proposition 14, p.50

import Definitions.Def_RobustQSC_fourier

namespace RobustQSC

open QAlgorithms

/-- The measure `μ_f(x) = |f(x)|²` induced by `f`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 2, p.8 ("μ_f(x) = |f(x)|²"),
§2.5.3, p.15. -/
noncomputable def muOf {n : ℕ} (f : EuclideanSpace ℂ (Qubits n)) : Qubits n → ℝ :=
  fun x => ‖f x‖ ^ 2

/-- The harmonic-mean weighted total influence

$$\mathrm{Inf}_\mu[h] = \sum_{i,x} \frac{2\mu(x)\mu(x+i)}{\mu(x)+\mu(x+i)}
  \Big|\frac{h(x)-h(x+i)}{2}\Big|^2.$$

Source: Coladangelo, Li, Slote, arXiv:2607.27184 (sha256 09d2692e…), §2.3, p.8 ("the
μ-weighted total influence"), Corollary 2, p.22 ("Harmonic mean weighted influence"), §2.5.3,
p.15.

**Formalization Note.** The sum runs over all `i ∈ [n]` and all `x` (each edge twice), as
printed. An edge with `μ(x) + μ(x+i) = 0` gets weight `0/0 = 0` in Lean; for a probability
measure with full support this never happens. -/
noncomputable def infMu {n : ℕ} (μ : Qubits n → ℝ) (h : Qubits n → ℂ) : ℝ :=
  ∑ i : Fin n, ∑ x : Qubits n,
    2 * μ x * μ (flip x i) / (μ x + μ (flip x i)) * ‖(h x - h (flip x i)) / 2‖ ^ 2

/-- The interior influence on `A`,
`Inf^{int(A)}_μ(h) = Σ_{x, y ∈ A, y ∼ x} 2μ(x)μ(y)/(μ(x)+μ(y)) |(h(x)−h(y))/2|²`, the sum over
ordered pairs of neighbours `x, y = x + i` that both lie in `A`.

Source: Coladangelo, Li, Slote, arXiv:2607.27184 (sha256 09d2692e…), §6, p.48 (display "for any
function h, Inf^{int(A)}_μ(h) := …").

**Formalization Note.** The weight is p.48's `2μ(x)μ(y)/(μ(x)+μ(y))`; the overview's display on
p.17 is a typo of it. -/
noncomputable def infInt {n : ℕ} (μ : Qubits n → ℝ) (A : Set (Qubits n)) (h : Qubits n → ℂ) :
    ℝ := by
  classical
  exact ∑ i : Fin n, ∑ x : Qubits n,
    if x ∈ A ∧ flip x i ∈ A then
      2 * μ x * μ (flip x i) / (μ x + μ (flip x i)) * ‖(h x - h (flip x i)) / 2‖ ^ 2
    else 0

/-- `Inf_unif`: the weighted influence for the uniform measure `μ ≡ 2^{-n}` (§3.1, p.19: "unif
denotes the uniform probability distribution"); `Inf_unif = (4N)^{-1} Σ_{x∼y}|h(x)−h(y)|²`
(p.50). -/
noncomputable def infUnif {n : ℕ} (h : Qubits n → ℂ) : ℝ :=
  infMu (fun _ => 1 / (2 : ℝ) ^ n) h

/-- `Inf^{int(A)}_unif`: the interior influence for the uniform measure (Proposition 14, p.50). -/
noncomputable def infIntUnif {n : ℕ} (A : Set (Qubits n)) (h : Qubits n → ℂ) : ℝ :=
  infInt (fun _ => 1 / (2 : ℝ) ^ n) A h

/-! ### Sanity tests -/

/-- Constants have zero influence. -/
example {n : ℕ} (μ : Qubits n → ℝ) (c : ℂ) : infMu μ (fun _ => c) = 0 := by
  simp [infMu]

/-- The interior influence on the whole cube is the influence. -/
example {n : ℕ} (μ : Qubits n → ℝ) (h : Qubits n → ℂ) : infInt μ Set.univ h = infMu μ h := by
  simp [infInt, infMu]

end RobustQSC


