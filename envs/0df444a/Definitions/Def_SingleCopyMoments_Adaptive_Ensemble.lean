-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Ensemble
-- name    : SingleCopyMoments_Adaptive_Ensemble
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:47:15.048362+00:00
-- url     : https://prove2.me/theorems/2d2da59c-9000-4aca-ad89-a5e221e04b48
-- title:
--   Spectral interpolation, physical Gaussian prior, and frozen likelihoods
-- statement:
--   For $r\ge2$ and $0\le\theta\le\pi/r$, define
--
--   $$\lambda_j(\theta)=\frac{1+\cos(2\pi j/r+\theta)}r,\quad R_\theta=\frac\alpha d\sum_j\lambda_j(\theta)\|g_j\|^2,\quad\rho_\theta=\frac{1-R_\theta}dI+\frac\alpha d\sum_j\lambda_j(\theta)g_jg_j^\dagger.$$
--
--   Each complex Gaussian coordinate consists of independent real and imaginary $N(0,1/2)$ variables. The vectors are independent under their product law $G$. The cutoff is $1$ for $s\le1/3$, $\exp(-(s-1/3)^2/(1/2-s))$ for $1/3<s<1/2$, and $0$ for $s\ge1/2$. The prior has density $\chi(R_\theta)/B_\theta$, where $B_\theta=\mathbb E_G\chi(R_\theta)$; normalization and physical support are conclusions of Lemma 32.
--
--   A frozen history is a sequence of rank-one unit projectors. Its factor is $f_i=d\operatorname{Tr}(P_i\rho_\theta)$, the product likelihood is formed before averaging, and $Z_\theta=\mathbb E_G[\chi(R_\theta)\prod_i f_i]$, $\widetilde Z_\theta=\mathbb E_G\prod_i f_i$. Deleting indices keeps the other projectors fixed. The posterior uses the physical product divided by $Z_\theta$, and the record density is $Z_\theta/B_\theta$. These definitions implement one latent draw for all copies. The budget condition is $T(d)\log(d+T(d)+1)/d\to0$.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §7.1–§7.2, (7.2)–(7.14), printed pp. 32–35 (PDF pp. 34–37); §5 asymptotics, printed pp. 13–14 (PDF pp. 15–16). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Pilot

open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ENNReal ComplexOrder Topology
noncomputable section

namespace SingleCopyMoments.Adaptive

abbrev Latent (d r : ℕ) := Fin r → (Fin d → ℂ)

def spectralWeight (r : ℕ) (θ : ℝ) (j : Fin r) : ℝ :=
  (1 + Real.cos (2 * Real.pi * (j.val : ℝ) / (r : ℝ) + θ)) / (r : ℝ)

def spectralMoment (r k : ℕ) (θ : ℝ) : ℝ := ∑ j : Fin r, spectralWeight r θ j ^ k

def spectralGap (r t : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 - (t : ℤ)) * (r : ℝ) ^ (1 - (t : ℤ)) * ((2*t).choose (t-r) : ℝ)

def vectorSq {d : ℕ} (v : Fin d → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

def complexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))).map
    (fun z : ℝ × ℝ => (⟨z.1,z.2⟩ : ℂ))

def gaussian (d r : ℕ) : Measure (Latent d r) :=
  Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin d => complexGaussian))

def radial {d r : ℕ} (α θ : ℝ) (g : Latent d r) : ℝ :=
  α / (d : ℝ) * ∑ j, spectralWeight r θ j * vectorSq (g j)

def hardMatrix {d r : ℕ} (α θ : ℝ) (g : Latent d r) : Op d :=
  ((1 - radial α θ g) / (d : ℝ)) • (1 : Op d) +
    (α / (d : ℝ)) • ∑ j, spectralWeight r θ j • outer (g j)

/-- exp(-φ), with the +∞ branch of φ represented by zero exactly. -/
def cutoff (s : ℝ) : ℝ :=
  if s ≤ 1/3 then 1 else if s < 1/2 then
    Real.exp (-((s - 1/3)^2 / (1/2 - s))) else 0

def normalizer (d r : ℕ) (α θ : ℝ) : ℝ := ∫ g, cutoff (radial α θ g) ∂gaussian d r

def prior (d r : ℕ) (α θ : ℝ) : Measure (Latent d r) :=
  (gaussian d r).withDensity (fun g => ENNReal.ofReal
    (cutoff (radial α θ g) / normalizer d r α θ))

abbrev FrozenHistory (d N : ℕ) := Fin N → Op d

def IsRankOne {d : ℕ} (A : Op d) : Prop :=
  ∃ v : Fin d → ℂ, vectorSq v = 1 ∧ A = outer v

def Frozen {d N : ℕ} (H : FrozenHistory d N) : Prop := ∀ i, IsRankOne (H i)

def factor {d r : ℕ} (α θ : ℝ) (g : Latent d r) (P : Op d) : ℝ :=
  (d : ℝ) * (P * hardMatrix α θ g).trace.re

def likelihood {d r N : ℕ} (α θ : ℝ) (H : FrozenHistory d N)
    (I : Finset (Fin N)) (g : Latent d r) : ℝ := ∏ i ∈ I, factor α θ g (H i)

def physicalZ {d N : ℕ} (r : ℕ) (α θ : ℝ) (H : FrozenHistory d N)
    (I : Finset (Fin N)) : ℝ :=
  ∫ g, cutoff (radial α θ g) * likelihood α θ H I g ∂gaussian d r

def auxiliaryZ {d N : ℕ} (r : ℕ) (α θ : ℝ) (H : FrozenHistory d N)
    (I : Finset (Fin N)) : ℝ := ∫ g, likelihood α θ H I g ∂gaussian d r

def posterior {d N : ℕ} (r : ℕ) (α θ : ℝ) (H : FrozenHistory d N) : Measure (Latent d r) :=
  (gaussian d r).withDensity (fun g => ENNReal.ofReal
    (cutoff (radial α θ g) * likelihood α θ H Finset.univ g /
      physicalZ r α θ H Finset.univ))

def recordDensity {d N : ℕ} (r : ℕ) (α θ : ℝ) (H : FrozenHistory d N) : ℝ :=
  physicalZ r α θ H Finset.univ / normalizer d r α θ

/-- Genuine little-o budget condition, including every arbitrarily large dimension. -/
def SublinearBudget (T : ℕ → ℕ) : Prop :=
  Tendsto (fun d => (T d : ℝ) * Real.log ((d : ℝ) + T d + 1) / (d : ℝ)) atTop (nhds 0)

end SingleCopyMoments.Adaptive


