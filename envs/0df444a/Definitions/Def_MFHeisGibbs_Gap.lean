-- Prove2me | Definitions.Def_MFHeisGibbs_Gap
-- name    : MFHeisGibbs_Gap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:17.416197+00:00
-- url     : https://prove2.me/theorems/d84e3173-d424-44dc-9b76-4af00c08c5d9
-- title:
--   The spectral gap $\mathrm{gap}(-\mathcal L)$, the scalar kernel, and $\mathrm{gap}=\Theta(n^{-a})$
-- statement:
--   For a superoperator $\mathcal L$, the spectral gap of $-\mathcal L$ is
--
--   $$\mathrm{gap}(-\mathcal L)=\inf\{-\mathrm{Re}\,\lambda:\lambda\ne0\text{ an eigenvalue of }\mathcal L\}.$$
--
--   $\mathcal L$ has a **scalar kernel** when $\mathcal L[X]=0$ exactly for $X\in\mathbb C I$. For a family $(\mathcal L_n)$, the statement $\mathrm{gap}(-\mathcal L_n)=\Theta(n^{-a})$ means that there are $c,C>0$ with $c\,n^{-a}\le\mathrm{gap}(-\mathcal L_n)\le C\,n^{-a}$ and a scalar kernel for all $n\ge2$.
--
--   This is the form in which the main theorem is stated at every inverse temperature, including $\beta=\infty$, where the Gibbs state is singular and the KMS form degenerates.
--
--   **Formalization Note** The set of the infimum is finite. If it were empty the infimum would be $0$, which the lower bound excludes. $\Theta$ is read as on p.41: $n\to\infty$ with $\beta,f,\sigma$ fixed.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.5 (PDF 6); p.39 (PDF 40); p.41 (PDF 42); (27), p.9 (PDF 10)

import Definitions.Def_MFHeisGibbs_Model

namespace MFHeisGibbs

/-!
# Spectral gap and the order of the gap

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
p.5 (Theorem 1); p.39 (the spectral gap at `β = ∞`); p.41 (the meaning of `Θ`); p.43 (`gap`).

**Formalization Note.** `specGap` is the spectral meaning of `gap(−L)`, used at every `β`, including
`β = ∞`, where the KMS form degenerates. The milestone `eq_27` links it to the Rayleigh form (27)
at finite `β`. The infimum is over a finite set. If `L` had no nonzero eigenvalue it would be the
junk value `0`, which the lower bound in `GapOrder` excludes. `GapOrder` reads `Θ` as on p.41: `n → ∞`
with `β, f, σ` fixed; the constants `c, C` come after those parameters and before `n`.
-/

/-- The spectral gap `gap(−L) = inf{−Re λ : λ ≠ 0 an eigenvalue of L}`. -/
noncomputable def specGap {n : ℕ} (L : Module.End ℂ (Op n)) : ℝ :=
  sInf {r : ℝ | ∃ l : ℂ, l ≠ 0 ∧ Module.End.HasEigenvalue L l ∧ r = -l.re}

/-- The kernel of `L` is exactly the scalars `ℂ·I`: "only scalar fixed observables", p.50. -/
def ScalarKernel {n : ℕ} (L : Module.End ℂ (Op n)) : Prop :=
  ∀ X, L X = 0 ↔ ∃ c : ℂ, X = c • 1

/-- `gap(−L_n) = Θ(n^{−a})`, with a scalar kernel for every `n ≥ 2`. -/
def GapOrder (L : ∀ n : ℕ, Module.End ℂ (Op n)) (a : ℝ) : Prop :=
  ∃ c > 0, ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
    ScalarKernel (L n) ∧ c * (n : ℝ) ^ (-a) ≤ specGap (L n) ∧ specGap (L n) ≤ C * (n : ℝ) ^ (-a)

end MFHeisGibbs


