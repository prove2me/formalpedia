-- Prove2me | Definitions.Def_RobustQSC_Compatible
-- name    : RobustQSC_Compatible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:40.52007+00:00
-- url     : https://prove2.me/theorems/db66c916-6c5c-4aa0-b463-568270044b40
-- title:
--   $\mu$-compatibility of $q$, the $L^2(\mu)$ norm and the product $fq$
-- statement:
--   A function $q:\{0,1\}^n\to\mathbb C$ is **$\mu$-compatible** if
--
--   $$
--   \mathbb E_{x\sim\mu}q(x)=\sum_x\mu(x)q(x)=0\quad\text{and}\quad\|q\|^2_{L^2(\mu)}=\sum_x\mu(x)|q(x)|^2=1.
--   $$
--
--   For $\mu=\mu_f$ these say exactly that $g=fq$ is a unit vector orthogonal to $f$. The module also defines the norm $\|w\|_{L^2(\mu)}$ and the pointwise product $fq$ as a vector.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §2.5.3, p.15; §3.1, p.19; Corollary 6, p.53

import Definitions.Def_QAlgorithms_Defs_Basic

namespace RobustQSC

open QAlgorithms

/-- `q` is `μ`-compatible: `E_{x∼μ} q(x) = Σ_x μ(x) q(x) = 0` and
`‖q‖²_{L²(μ)} = Σ_x μ(x)|q(x)|² = 1`. For `μ = μ_f` these say exactly that `g = fq` is a unit
vector orthogonal to `f`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §2.5.3, p.15 ("the compatibility
requirements for q can be written as ‖q‖²_{L²(µf)} = 1 and E_{x∼µf} q(x) = 0 … we will say that
a q is µf-compatible if it satisfies the two equations above"). -/
def Compatible {n : ℕ} (μ : Qubits n → ℝ) (q : Qubits n → ℂ) : Prop :=
  ∑ x, (μ x : ℂ) * q x = 0 ∧ ∑ x, μ x * ‖q x‖ ^ 2 = 1

/-- The norm `‖w‖_{L²(μ)} = (Σ_x μ(x)|w(x)|²)^{1/2}` (§3.1, p.19; Corollary 6, p.53). -/
noncomputable def l2Norm {n : ℕ} (μ : Qubits n → ℝ) (w : Qubits n → ℂ) : ℝ :=
  Real.sqrt (∑ x, μ x * ‖w x‖ ^ 2)

/-- The pointwise product `g = fq`, `g(x) = f(x) q(x)`, as a vector (§2.5.3, p.15; Lemma 3,
p.25: `Avg_f̂[\widehat{fq}]`). -/
noncomputable def ptMul {n : ℕ} (f : EuclideanSpace ℂ (Qubits n)) (q : Qubits n → ℂ) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun x => f x * q x

end RobustQSC


