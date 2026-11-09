-- Prove2me | Definitions.Def_IncoherentPurity_Adaptive_Estimators
-- name    : IncoherentPurity_Adaptive_Estimators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:15.070331+00:00
-- url     : https://prove2.me/theorems/6d5c245b-4516-4714-8bea-3a2b1654b6b3
-- title:
--   Haar experiments and the two purity estimators
-- statement:
--   A normalized left Haar probability on $U(d)$ induces Haar pure vectors by its first column. The uniform measurement on state $\rho$ has density $d\langle v|\rho|v\rangle$ against this pure-vector Haar law. The snapshot is $X=(d+1)|v\rangle\langle v|-I$.
--
--   For $B\ge1,s\ge2$, independent Haar bases each produce $s$ independent Born outcomes; the collision count is $\widehat Q_b=\sum_iN_{b,i}(N_{b,i}-1)/(s(s-1))$ and the batch estimate is $B^{-1}\sum_b((d+1)\widehat Q_b-1)$. Define $Q_j=\sum_iq_i^j$, $\mu_j=\mathbb E Q_j$, $\mu_{22}=\mathbb E Q_2^2$, $\Delta=\rho-I/d$, and $x=\operatorname{tr}\Delta^2$.
--
--   Algorithm 1 averages $n\ge1$ independent snapshots to form $\widehat\rho$, then measures this Hermitian observable on $m\ge1$ fresh copies. Each observation is its signed eigenvalue; their mean is $Y$. The output is $Z=(2Y-\operatorname{tr}\widehat\rho^2+(d^2+d-1)/n)/(1+1/n)$. All experiment measures are computed from these Born laws. Tensor powers and permutation matrices fix the conventions of the moment identities.
--
--   The ceiling allocations in equation (3.5) and the proof of Theorem 4.1 are computed from their absolute constant, dimension, and precision.
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, definitions and constructions, PDF pp.8–14 = printed pp.8–14; equations (3.2)–(3.5), (3.10); Algorithm 1; proof of Theorem 4.1; Lemmas 2.4–2.5

import Definitions.Def_IncoherentPurity_Adaptive_Measurements

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
noncomputable section

namespace IncoherentPurity.Adaptive

abbrev Unitary (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ
/-- The normalized left Haar law on U(d); any representative gives the same experiments. -/
structure HaarBasis (d : ℕ) where
  law : Measure (Unitary d)
  probability : IsProbabilityMeasure law
  invariant : ∀ U : Unitary d, law.map (fun V => U * V) = law

def outer {d : ℕ} (v : Fin d → ℂ) : Op d := fun i j => v i * star (v j)
def pureHaar {d : ℕ} (H : HaarBasis d) : Measure (Fin d → ℂ) := by
  classical
  exact if h : 0 < d then H.law.map (fun U => fun i => (U.val) i ⟨0,h⟩)
    else Measure.dirac 0

def uniformLaw {d : ℕ} (H : HaarBasis d) (ρ : Op d) : Measure (Fin d → ℂ) :=
  (pureHaar H).withDensity (fun v => ENNReal.ofReal ((d : ℝ) * (ρ * outer v).trace.re))
def shadow {d : ℕ} (v : Fin d → ℂ) : Op d := ((d : ℝ)+1) • outer v - 1

def basisProb {d : ℕ} (ρ : Op d) (U : Unitary d) (i : Fin d) : ℝ :=
  ((star U.val * ρ * U.val) i i).re
def basisLaw {d : ℕ} (ρ : Op d) (U : Unitary d) : Measure (Fin d) :=
  ∑ i, ENNReal.ofReal (basisProb ρ U i) • Measure.dirac i

def Q {d : ℕ} (ρ : Op d) (U : Unitary d) (k : ℕ) : ℝ := ∑ i, basisProb ρ U i ^ k
def mu {d : ℕ} (H : HaarBasis d) (ρ : Op d) (k : ℕ) : ℝ := ∫ U, Q ρ U k ∂H.law
def mu22 {d : ℕ} (H : HaarBasis d) (ρ : Op d) : ℝ := ∫ U, (Q ρ U 2)^2 ∂H.law

def collision {d s : ℕ} (a : Fin s → Fin d) : ℝ := by
  classical
  exact (∑ i : Fin d, (Finset.univ.filter (fun t => a t = i)).card *
    (((Finset.univ.filter (fun t => a t = i)).card : ℝ) - 1)) / ((s : ℝ) * ((s : ℝ)-1))
def fixedLaw {d : ℕ} (ρ : Op d) (U : Unitary d) (s : ℕ) :=
  Measure.pi (fun _ : Fin s => basisLaw ρ U)
def blockLaw {d : ℕ} (H : HaarBasis d) (ρ : Op d) (s : ℕ) :
    Measure (Unitary d × (Fin s → Fin d)) :=
  H.law.bind (fun U => (fixedLaw ρ U s).map (fun a => (U,a)))
def batchesLaw {d : ℕ} (H : HaarBasis d) (ρ : Op d) (B s : ℕ) :=
  Measure.pi (fun _ : Fin B => blockLaw H ρ s)
def batchEstimate {d B s : ℕ} (a : Fin B → Unitary d × (Fin s → Fin d)) : ℝ :=
  (∑ b, (((d : ℝ)+1) * collision (a b).2 - 1)) / (B : ℝ)
def centered {d : ℕ} (ρ : Op d) : Op d := ρ - (1 / (d : ℝ)) • (1 : Op d)
def excess {d : ℕ} (ρ : Op d) := powerSum (centered ρ) 2

def prelim {d n : ℕ} (v : Fin n → (Fin d → ℂ)) : Op d :=
  (1 / (n : ℝ)) • ∑ i, shadow (v i)
/-- Spectral measurement of a Hermitian observable, with its signed eigenvalue as output. -/
def observableLaw {d : ℕ} (ρ A : Op d) : Measure ℝ := by
  classical
  exact if h : A.IsHermitian then
    ∑ i : Fin d, ENNReal.ofReal (basisProb ρ h.eigenvectorUnitary i) •
      Measure.dirac (h.eigenvalues i)
    else Measure.dirac 0

def adaptiveLaw {d : ℕ} (H : HaarBasis d) (ρ : Op d) (n m : ℕ) :
    Measure ((Fin n → (Fin d → ℂ)) × (Fin m → ℝ)) :=
  (Measure.pi (fun _ : Fin n => uniformLaw H ρ)).bind (fun v =>
    (Measure.pi (fun _ : Fin m => observableLaw ρ (prelim v))).map (fun y => (v,y)))
def adaptiveEstimate {d n m : ℕ}
    (a : (Fin n → (Fin d → ℂ)) × (Fin m → ℝ)) : ℝ :=
  (2 * ((∑ j, a.2 j) / (m : ℝ)) - powerSum (prelim a.1) 2 +
      ((d : ℝ)^2 + d - 1) / (n : ℝ)) / (1 + 1 / (n : ℝ))

def tensorPower {d : ℕ} (A : Op d) (r : ℕ) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ := fun i j => ∏ k, A (i k) (j k)
def permutationOp (d r : ℕ) (π : Equiv.Perm (Fin r)) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ := by
  classical
  exact fun i j => if i = j ∘ π.symm then 1 else 0

def tensorPair {d : ℕ} (A B : Op d) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  Matrix.of fun i j => A (i 0) (j 0) * B (i 1) (j 1)

/-- The sample allocations displayed in (3.5) and the proof of Theorem 4.1. -/
def batchCount (A : ℝ) (d : ℕ) (ε : ℝ) : ℕ :=
  ⌈A * max 1 (1 / ((d : ℝ)*ε^2))⌉₊
def batchSize (A : ℝ) (d : ℕ) (ε : ℝ) : ℕ :=
  ⌈A * min ((d : ℝ)*Real.sqrt d/ε) ((d : ℝ)^2)⌉₊
def adaptiveFirstCount (C : ℝ) (d : ℕ) (ε : ℝ) : ℕ := ⌈C*(d : ℝ)^2/ε⌉₊
def adaptiveSecondCount (C : ℝ) (d : ℕ) (ε : ℝ) : ℕ :=
  ⌈C*(Real.sqrt d/ε^2 + (d : ℝ)/ε)⌉₊

end IncoherentPurity.Adaptive


