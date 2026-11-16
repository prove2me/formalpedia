-- Prove2me | Definitions.Def_GaussDiffSVP_Supplement_DGS
-- name    : GaussDiffSVP_Supplement_DGS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:46:03.06212+00:00
-- url     : https://prove2.me/theorems/bf66c690-6838-4cab-be63-5ca6fc0035b5
-- title:
--   Shifted discrete Gaussian sampling within time, space and total variation bounds
-- statement:
--   An instance of **shifted discrete Gaussian sampling** is a nonsingular basis $B\in\mathbb Q^{n\times n}$ of the lattice $L=B\mathbb Z^n$, a rational shift $a\in\mathbb Q^n$ and a positive rational squared width $\sigma^2$. The target law is
--   $$D_{a+L,\sigma}(x)=\frac{\rho_\sigma(x)}{\rho_\sigma(a+L)}\quad(x\in a+L),\qquad \rho_\sigma(x)=e^{-\pi\|x\|^2/\sigma^2},$$
--   and for $m$ samples the product law $D_{a+L,\sigma}^{\otimes m}$.
--
--   A randomized program **samples $m$ points within time $T$, space $S$ and error $\varepsilon$** on the instance if
--
--   1. on every coin tape it halts with bit time at most $T(\ell+1)^K$ and bit space at most $S(\ell+1)^K$, where $\ell$ is the bit length of the input;
--   2. on every coin tape it outputs $m$ points of $a+L$;
--   3. the total variation distance $\tfrac12\sum_o|\mu(o)-\nu(o)|$ between its output law $\mu$ under fair coins and $\nu=D_{a+L,\sigma}^{\otimes m}$ is at most $\varepsilon$.
--
--   This is the guarantee of Theorems 1.1, 11.2 and 11.3.
--
--   **Formalization Note** The machine is the published randomized log-cost rational RAM. The input word is the basis, then the shift, then $\sigma^2$; points are output by their rational coordinates, so the target is read on output words. The Gaussian is centered at $0$ and supported on the coset, as on p.6.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §1.2, p.6 (notation, Theorems 1.1–1.2); App. C.1.1, p.80

import Mathlib
import Definitions.Def_CosetTreeSVP_SVP_Algo

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace GaussDiffSVP.Supplement

open CosetTreeSVP.SVP

/-- The input word of a shifted discrete Gaussian sampling instance (Gao–Han–Hu, *Gaussian
Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 1.1 and
Theorem 1.2, p.6): the basis `B ∈ ℚ^{n×n}` (`SuperlatSVP.encBasis`, which starts with `n`), then the
rational shift `a ∈ ℚⁿ`, then the rational squared width `σ²`, one stored rational each. -/
def dgsInput {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) (σ2 : ℚ) : List ℚ :=
  SuperlatSVP.encBasis B ++ encQVec a ++ [σ2]

/-- The output word of a tuple `(X₁, …, X_m)` of rational points of `ℚⁿ`: their coordinates, one
point after the other (`m` blocks of `n` entries). -/
def encPts {n m : ℕ} (x : Fin m → Fin n → ℚ) : List ℚ :=
  (List.finRange m).flatMap fun i => encQVec (x i)

/-- The target law `D_{a+L,σ}^{⊗m}` of `m` independent samples of the shifted discrete Gaussian on
the coset `a + L(B)`, read on output words: the probability of the word `o` is the sum, over the
tuples `x` with `encPts x = o`, of `∏ᵢ D_{a+L,σ}(xᵢ)`, where `D_{a+L,σ}(y) = ρ_σ(y)/ρ_σ(a + L)` on
`y ∈ a + L` and `0` off the coset (p.6; the published `RegevLWE.GaussConv.discreteGaussian`).

**Formalization Note.** The Gaussian is centered at `0` and supported on the coset, as on p.6
(`ρ_σ(x)` for `x ∈ a + L`, not `ρ_σ(x − a)`). Every point of `a + L(B)` is rational for rational
`a, B`, and `encPts` is injective, so this is the push-forward of the product law. -/
noncomputable def gaussProdWordLaw {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) (σ : ℝ)
    (m : ℕ) (o : List ℚ) : ℝ≥0∞ := by
  classical
  exact ∑' x : Fin m → Fin n → ℚ, if encPts x = o then
    ∏ i, ENNReal.ofReal (RegevLWE.GaussConv.discreteGaussian (latQ B) (qVec a) σ (qVec (x i)))
    else 0

/-- A randomized program samples `m` points of the shifted discrete Gaussian `D_{a+L,σ}` on the
instance `(B, a, σ²)`, `σ = √σ²`, within bit time `T·(ℓ+1)^K`, bit space `S·(ℓ+1)^K` and total
variation error `ε` (Gao–Han–Hu, Theorems 1.1, 1.2, 11.2, 11.3, pp.6, 55–56; App. C.1.1, p.80):

1. on **every** coin tape the run halts, with bit time at most `T·(ℓ+1)^K` and bit space at most
   `S·(ℓ+1)^K`, where `ℓ` is the bit length of the input word ("their time and bit space bounds
   hold on every execution", p.6; the bit space includes the output, p.6);
2. on **every** coin tape the output is a tuple of `m` points of `a + L(B)` ("outputs `X ∈ a + L`";
   on failure the algorithm returns its affine offset or fallback tuple, p.80);
3. the output events are measurable, and the total variation distance `½ Σ_o |μ(o) − ν(o)|` between
   the output law `μ` under fair coins and `ν = D_{a+L,σ}^{⊗m}` is at most `ε`.

**Formalization Note.** The machine is the published randomized log-cost rational RAM
`TwMSOCount.Main`; the input word is `dgsInput`; points are output by their rational coordinates
(`encPts`); `tvDist` and `outLaw` are the published `CosetTreeSVP.SVP` notions (`½ Σ`). -/
def SamplesDGSWithin (P : Program) (K : ℕ) (T S ε : ℝ) (m : ℕ) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) (σ2 : ℚ) : Prop :=
  (∀ τ : ℕ → Bool, ∃ s : RunStats, runStats P τ (Config.init (dgsInput B a σ2)) = some s ∧
      (s.time : ℝ) ≤ T * ((wordBits (dgsInput B a σ2) : ℝ) + 1) ^ K ∧
      (s.space : ℝ) ≤ S * ((wordBits (dgsInput B a σ2) : ℝ) + 1) ^ K) ∧
    (∀ τ : ℕ → Bool, ∃ x : Fin m → Fin n → ℚ, (∀ i, qVec (x i) - qVec a ∈ latQ B) ∧
      callOutput P (Config.init (dgsInput B a σ2)) τ = some (encPts x)) ∧
    (∀ o : List ℚ, MeasurableSet {τ | callOutput P (Config.init (dgsInput B a σ2)) τ = some o}) ∧
    tvDist (outLaw P (Config.init (dgsInput B a σ2)))
      (gaussProdWordLaw B a (Real.sqrt (σ2 : ℝ)) m) ≤ ENNReal.ofReal ε

end GaussDiffSVP.Supplement


