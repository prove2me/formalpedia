-- Prove2me | Definitions.Def_RecGaussColoring_Main_Certificates
-- name    : RecGaussColoring_Main_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:24.857236+00:00
-- url     : https://prove2.me/theorems/18a99cce-4d9b-4c63-a598-98d1a773b1b4
-- title:
--   Recursive Gaussian certificates along sequences
-- statement:
--   A sequence of raw instances specifies graphs $G_k$, dimensions $d_k$, vectors $v_{k,j}$, roots $i_k$, and induced vertex sets $W_k$. Write $e=o(t)$ when $e_k/t_k\to0$, $f=o(t^2)$ when $f_k/t_k^2\to0$, and $h=o(1)$ when $h_k\to0$. A certificate supported on $S_k$ has parameters $(a_k,s_k,\delta_k)$ when its root correlations equal $a_k+o(1)$ uniformly over $S_k$, and eventually
--   $$
--   \Pr\left[\exists j\in S_k:\left\langle\gamma,
--   \frac{v_{k,j}-\langle v_{k,i_k},v_{k,j}\rangle v_{k,i_k}}
--    {\sqrt{1-\langle v_{k,i_k},v_{k,j}\rangle^2}}\right\rangle\ge s_k\right]\ge\delta_k.
--   $$
--   Normalization is required to be defined eventually, so those correlations have absolute value below one. A level-$\ell$ certificate uses endpoints of length-$\ell$ walks in $G_k[W_k]$, allowing repeated vertices. The asymptotic certificate predicate means $s_k=\lambda_kt_k-e_k$ and $\delta_k=e^{-f_k}$ for some errors with the stated rates.
--
--   The separate setting predicate records three-colorability, strict vector colorings, the degree bound, the prescribed Gaussian threshold, roots in $W_k$, local covers, and $n_k\to\infty$. It does not assume any propagation result. Equation (2.13) is a computed set from a retained first neighborhood and a type interval.
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), §2.2, Definition 2.6, (2.11) and (2.13); Appendix A, pp. 23–25, p. 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Rounding
import Definitions.Def_RecGaussColoring_Main_Parameters

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- All little-o errors are genuine sequences; no rate is assumed at a single input. -/
def SmallO (e t : ℕ → ℝ) : Prop := Tendsto (fun k => e k / t k) atTop (𝓝 0)
def SmallOSq (e t : ℕ → ℝ) : Prop := SmallO e (fun k => (t k)^2)
def Vanishes (e : ℕ → ℝ) : Prop := Tendsto e atTop (𝓝 0)

/-- Only raw data. All standing assumptions are separate predicates below. -/
structure CertificateData where
  graph : ℕ → Graph3
  dim : ℕ → ℕ
  vectors : (k : ℕ) → Fin (graph k).n → Space (dim k)
  root : (k : ℕ) → Fin (graph k).n
  region : (k : ℕ) → Finset (Fin (graph k).n)

/-- Endpoints of length-ℓ walks within the induced subgraph G[W]; repeats allowed. -/
def WalkEndpoint (I : Graph3) (W : Finset (Fin I.n)) : ℕ → Fin I.n → Fin I.n → Prop
  | 0, i, j => i = j ∧ i ∈ W
  | l+1, i, j => j ∈ W ∧ ∃ u ∈ W, WalkEndpoint I W l i u ∧ I.G.Adj u j

def normalizedDirection {n d : ℕ} (v : Fin n → Space d) (i j : Fin n) : Space d :=
  (1 / Real.sqrt (1-⟪v i, v j⟫^2)) • (v j - ⟪v i, v j⟫ • v i)

/-- Definition 2.6: one uniform correlation error and an eventual cover assertion. -/
def RecursiveCertificate (D : CertificateData)
    (S : (k : ℕ) → Finset (Fin (D.graph k).n)) (a s δ : ℕ → ℝ) : Prop :=
  (∀ᶠ k in atTop, -1 < a k ∧ a k < 1) ∧
  (∃ e : ℕ → ℝ, Vanishes e ∧ ∀ᶠ k in atTop,
    ∀ j ∈ S k, |⟪D.vectors k (D.root k), D.vectors k j⟫-a k| ≤ e k) ∧
  ∀ᶠ k in atTop,
    (∀ j ∈ S k, |⟪D.vectors k (D.root k), D.vectors k j⟫| < 1) ∧
    IsCover
    ((S k).image fun j => normalizedDirection (D.vectors k) (D.root k) j) (s k) (δ k)

def LevelCertificate (D : CertificateData) (l : ℕ)
    (S : (k : ℕ) → Finset (Fin (D.graph k).n)) (a s δ : ℕ → ℝ) : Prop :=
  RecursiveCertificate D S a s δ ∧ ∀ᶠ k in atTop,
    ∀ j ∈ S k, WalkEndpoint (D.graph k) (D.region k) l (D.root k) j

/-- Abbreviation for the parameters (a, λt-o(t), exp(-o(t²))). -/
def AsymptoticCertificate (D : CertificateData) (t : ℕ → ℝ) (l : ℕ)
    (S : (k : ℕ) → Finset (Fin (D.graph k).n)) (a lam : ℕ → ℝ) : Prop :=
  ∃ e f : ℕ → ℝ, SmallO e t ∧ SmallOSq f t ∧
    LevelCertificate D l S a (fun k => lam k*t k-e k) (fun k => Real.exp (-f k))

/-- Standing assumptions of §2.2. Colorability is retained; only failure (i) is omitted. -/
def CertificateSetting (c : ℝ) (D : CertificateData) (t : ℕ → ℝ) : Prop :=
  Tendsto (fun k => (D.graph k).n) atTop atTop ∧
  ∀ᶠ k in atTop,
    ThreeColorable (D.graph k) ∧
    StrictVectorColoring (D.graph k).G (D.vectors k) ∧
    (maxDeg (D.graph k) : ℝ) ≤ ((D.graph k).n : ℝ)^(sparseExponent c) ∧
    PhiTail (t k) = ((D.graph k).n : ℝ)^(-1/(5+3*c)) ∧
    0 < t k ∧ D.root k ∈ D.region k ∧
    LocalCovers (D.graph k) (D.vectors k) (D.region k) (t k)

/-- Equation (2.11). -/
def levelTwoType (D : CertificateData) (k : ℕ)
    (j u : Fin (D.graph k).n) : ℝ :=
  ⟪edgeDirection (D.vectors k) (D.root k) j, edgeDirection (D.vectors k) u j⟫

/-- Equation (2.13): constructed from the retained first neighborhood and interval. -/
def levelTwoSet (D : CertificateData) (k : ℕ) (retained : Finset (Fin (D.graph k).n))
    (lo hi : ℝ) : Finset (Fin (D.graph k).n) := by
  classical exact (D.region k).filter fun u =>
    ∃ j ∈ retained, (D.graph k).G.Adj j u ∧ levelTwoType D k j u ∈ Set.Icc lo hi

end RecGaussColoring.Main


