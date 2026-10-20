-- Prove2me | Definitions.Def_MeanFieldDNN_TwoLayer_Model
-- name    : MeanFieldDNN_TwoLayer_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:06.490687+00:00
-- url     : https://prove2.me/theorems/4a117fad-ecef-4826-87ea-19da672111e5
-- title:
--   Assumption 2.1 and equations (1.1)–(1.4), (2.1), (2.6), (5.1) — network and limiting systems
-- statement:
--   Fix an input dimension $d$, an activation $\sigma$, a compactly supported training-data law $\pi$, and independent compactly supported initialization laws $\mu_c$, $\mu_{W^1}$, and $\mu_{W^2}$. The activation and its first two derivatives are bounded, and the initialization laws have continuous densities. For widths $N_1,N_2$, the network output is
--
--   $$g_\theta^{N_1,N_2}(x)=\frac1{N_2}\sum_i C^i\sigma\!\left(\frac1{N_1}\sum_j W^{2,i,j}\sigma(W^{1,j}\cdot x)\right).$$
--
--   The definition gives all three simultaneous SGD updates from (1.4), with learning rates $\alpha_C=N_2/N_1$, $\alpha_{W,1}=1$, and $\alpha_{W,2}=N_2$. Time $t$ corresponds to $\lfloor N_1t\rfloor$ updates. It also specifies the limiting integral system (2.6), the finite $N_2$ particle system (5.1), and their output and error functions. These objects are shared by every result in this mission.
--
--   **Formalization Note** Solution paths are jointly continuous on time times their compact full-measure supports; the differential equations are written in integral form. The first-layer particle retains the full vector of second-layer initial weights.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, pp. 2–6, (1.1)–(1.4), Assumption 2.1, (2.1), (2.6); pp. 18–20, (5.1), §5.1; p. 32, (A.6)

import Mathlib

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Assumption 2.1, with the usual bounded-derivatives reading of C²_b. -/
structure Setting (d : ℕ) where
  σ : ℝ → ℝ
  σ_contDiff : ContDiff ℝ 2 σ
  σ_bdd : ∃ M : ℝ, ∀ z, |σ z| ≤ M
  dσ_bdd : ∃ M : ℝ, ∀ z, |deriv σ z| ≤ M
  ddσ_bdd : ∃ M : ℝ, ∀ z, |deriv (deriv σ) z| ≤ M
  piData : Measure (E d × ℝ)
  piData_prob : IsProbabilityMeasure piData
  X : Set (E d)
  Y : Set ℝ
  X_compact : IsCompact X
  Y_compact : IsCompact Y
  piData_supp : piData (X ×ˢ Y)ᶜ = 0
  μc : Measure ℝ
  μW1 : Measure (E d)
  μW2 : Measure ℝ
  μc_prob : IsProbabilityMeasure μc
  μW1_prob : IsProbabilityMeasure μW1
  μW2_prob : IsProbabilityMeasure μW2
  Cset : Set ℝ
  W1set : Set (E d)
  W2set : Set ℝ
  Cset_compact : IsCompact Cset
  W1set_compact : IsCompact W1set
  W2set_compact : IsCompact W2set
  μc_supp : μc Csetᶜ = 0
  μW1_supp : μW1 W1setᶜ = 0
  μW2_supp : μW2 W2setᶜ = 0
  μc_density : ∃ ρ : ℝ → ℝ, Continuous ρ ∧ (∀ z, 0 ≤ ρ z) ∧
    μc = volume.withDensity (fun z => ENNReal.ofReal (ρ z))
  μW1_density : ∃ ρ : E d → ℝ, Continuous ρ ∧ (∀ z, 0 ≤ ρ z) ∧
    μW1 = volume.withDensity (fun z => ENNReal.ofReal (ρ z))
  μW2_density : ∃ ρ : ℝ → ℝ, Continuous ρ ∧ (∀ z, 0 ≤ ρ z) ∧
    μW2 = volume.withDensity (fun z => ENNReal.ofReal (ρ z))

variable {d N1 N2 : ℕ}

def alphaC (N1 N2 : ℕ) : ℝ := (N2 : ℝ) / (N1 : ℝ)
def alphaW1 (_N1 _N2 : ℕ) : ℝ := 1
def alphaW2 (_N1 N2 : ℕ) : ℝ := N2

structure Params (d N1 N2 : ℕ) where
  C : Fin N2 → ℝ
  W1 : Fin N1 → E d
  W2 : Fin N2 → Fin N1 → ℝ

def H1 (S : Setting d) (θ : Params d N1 N2) (j : Fin N1) (x : E d) : ℝ :=
  S.σ (inner ℝ (θ.W1 j) x)

def Z2 (S : Setting d) (θ : Params d N1 N2) (i : Fin N2) (x : E d) : ℝ :=
  (1 / (N1 : ℝ)) * ∑ j : Fin N1, θ.W2 i j * H1 S θ j x

def H2 (S : Setting d) (θ : Params d N1 N2) (i : Fin N2) (x : E d) : ℝ :=
  S.σ (Z2 S θ i x)

def netOut (S : Setting d) (θ : Params d N1 N2) (x : E d) : ℝ :=
  (1 / (N2 : ℝ)) * ∑ i : Fin N2, θ.C i * H2 S θ i x

/-- The three components use the same pre-update state and sample. -/
def sgdStep (S : Setting d) (θ : Params d N1 N2) (z : E d × ℝ) : Params d N1 N2 :=
  let e := z.2 - netOut S θ z.1
  { C := fun i => θ.C i + (alphaC N1 N2 / (N2 : ℝ)) * e * H2 S θ i z.1
    W1 := fun j => θ.W1 j +
      ((alphaW1 N1 N2 / (N1 : ℝ)) * e *
        ((1 / (N2 : ℝ)) * ∑ i : Fin N2,
          θ.C i * deriv S.σ (Z2 S θ i z.1) * θ.W2 i j) *
        deriv S.σ (inner ℝ (θ.W1 j) z.1)) • z.1
    W2 := fun i j => θ.W2 i j + (alphaW2 N1 N2 / ((N1 : ℝ) * (N2 : ℝ))) *
      e * θ.C i * deriv S.σ (Z2 S θ i z.1) * H1 S θ j z.1 }

def initParams (C0 : ℕ → ℝ) (W20 : ℕ → ℕ → ℝ) (W10 : ℕ → E d) : Params d N1 N2 :=
  { C := fun i => C0 i.val, W1 := fun j => W10 j.val,
    W2 := fun i j => W20 i.val j.val }

def sgdIter (S : Setting d) (C0 : ℕ → ℝ) (W20 : ℕ → ℕ → ℝ)
    (W10 : ℕ → E d) (dat : ℕ → E d × ℝ) : ℕ → Params d N1 N2
  | 0 => initParams C0 W20 W10
  | k + 1 => sgdStep S (sgdIter S C0 W20 W10 dat k) (dat k)

def gNN (S : Setting d) (N1 N2 : ℕ) (t : ℝ) (x : E d)
    (C0 : ℕ → ℝ) (W20 : ℕ → ℕ → ℝ) (W10 : ℕ → E d)
    (dat : ℕ → E d × ℝ) : ℝ :=
  netOut S (sgdIter (N1 := N1) (N2 := N2) S C0 W20 W10 dat
    (Nat.floor ((N1 : ℝ) * t))) x

/-- Joint law of all initial weights and samples. -/
def IsInitLaw (S : Setting d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C0 : Ω → ℕ → ℝ) (W20 : Ω → ℕ → ℕ → ℝ)
    (W10 : Ω → ℕ → E d) (dat : Ω → ℕ → E d × ℝ) : Prop :=
  Measurable (fun ω => (C0 ω, W20 ω, W10 ω, dat ω)) ∧
    P.map (fun ω => (C0 ω, W20 ω, W10 ω, dat ω)) =
      (Measure.infinitePi fun _ : ℕ => S.μc).prod
        ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => S.μW2).prod
          ((Measure.infinitePi fun _ : ℕ => S.μW1).prod
            (Measure.infinitePi fun _ : ℕ => S.piData)))

/-- Three path maps in the limiting system (2.6). -/
structure LimitPaths (d : ℕ) where
  Ct : ℝ → ℝ → ℝ
  W1t : ℝ → E d → E d
  W2t : ℝ → ℝ → E d → ℝ → ℝ

def limH1 (S : Setting d) (L : LimitPaths d) (t : ℝ) (w x : E d) : ℝ :=
  S.σ (inner ℝ (L.W1t t w) x)

def limZ (S : Setting d) (L : LimitPaths d) (t c : ℝ) (x : E d) : ℝ :=
  ∫ w, ∫ u, L.W2t t c w u * limH1 S L t w x ∂S.μW2 ∂S.μW1

def limH2 (S : Setting d) (L : LimitPaths d) (t c : ℝ) (x : E d) : ℝ :=
  S.σ (limZ S L t c x)

def limG (S : Setting d) (L : LimitPaths d) (t : ℝ) (x : E d) : ℝ :=
  ∫ c, L.Ct t c * limH2 S L t c x ∂S.μc

def limV (S : Setting d) (L : LimitPaths d) (t : ℝ) (w x : E d) : ℝ :=
  ∫ c, L.Ct t c * deriv S.σ (limZ S L t c x) *
    (∫ u, L.W2t t c w u ∂S.μW2) ∂S.μc

/-- Integral form of (2.6), on the compact full-measure supports. -/
def IsLimitSolution (S : Setting d) (L : LimitPaths d) : Prop :=
  ContinuousOn (fun z : ℝ × ℝ => L.Ct z.1 z.2) (Icc 0 1 ×ˢ S.Cset) ∧
  ContinuousOn (fun z : ℝ × E d => L.W1t z.1 z.2) (Icc 0 1 ×ˢ S.W1set) ∧
  ContinuousOn (fun z : ℝ × (ℝ × (E d × ℝ)) => L.W2t z.1 z.2.1 z.2.2.1 z.2.2.2)
    (Icc 0 1 ×ˢ (S.Cset ×ˢ (S.W1set ×ˢ S.W2set))) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ S.Cset,
    L.Ct t c = c + ∫ s in 0..t, ∫ z, (z.2 - limG S L s z.1) * limH2 S L s c z.1 ∂S.piData) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ S.W1set,
    L.W1t t w = w + ∫ s in 0..t, ∫ z,
      ((z.2 - limG S L s z.1) * limV S L s w z.1 *
        deriv S.σ (inner ℝ (L.W1t s w) z.1)) • z.1 ∂S.piData) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ S.Cset, ∀ w ∈ S.W1set, ∀ u ∈ S.W2set,
    L.W2t t c w u = u + ∫ s in 0..t, ∫ z,
      (z.2 - limG S L s z.1) * L.Ct s c * deriv S.σ (limZ S L s c z.1) *
        limH1 S L s w z.1 ∂S.piData)

/-- Paths of (5.1), with the first-layer path depending on the full vector of W² initial values. -/
structure ParticlePaths (d N2 : ℕ) where
  Cp : ℝ → (Fin N2 → ℝ) → Fin N2 → ℝ
  W1p : ℝ → (Fin N2 → ℝ) → E d → (Fin N2 → ℝ) → E d
  W2p : ℝ → (Fin N2 → ℝ) → Fin N2 → E d → (Fin N2 → ℝ) → ℝ

def partH1 (S : Setting d) (Q : ParticlePaths d N2) (t : ℝ)
    (cv : Fin N2 → ℝ) (w : E d) (uv : Fin N2 → ℝ) (x : E d) : ℝ :=
  S.σ (inner ℝ (Q.W1p t cv w uv) x)

def partZ (S : Setting d) (Q : ParticlePaths d N2) (t : ℝ)
    (cv : Fin N2 → ℝ) (i : Fin N2) (x : E d) : ℝ :=
  ∫ w, ∫ uv, Q.W2p t cv i w uv * partH1 S Q t cv w uv x
    ∂(Measure.pi fun _ : Fin N2 => S.μW2) ∂S.μW1

def partH2 (S : Setting d) (Q : ParticlePaths d N2) (t : ℝ)
    (cv : Fin N2 → ℝ) (i : Fin N2) (x : E d) : ℝ :=
  S.σ (partZ S Q t cv i x)

def partG (S : Setting d) (Q : ParticlePaths d N2) (t : ℝ)
    (cv : Fin N2 → ℝ) (x : E d) : ℝ :=
  (1 / (N2 : ℝ)) * ∑ i : Fin N2, Q.Cp t cv i * partH2 S Q t cv i x

def partV (S : Setting d) (Q : ParticlePaths d N2) (t : ℝ)
    (cv : Fin N2 → ℝ) (w : E d) (uv : Fin N2 → ℝ) (x : E d) : ℝ :=
  (1 / (N2 : ℝ)) * ∑ i : Fin N2,
    Q.Cp t cv i * deriv S.σ (partZ S Q t cv i x) * Q.W2p t cv i w uv

/-- Integral form of (5.1), for all initial states in the compact product supports. -/
def IsParticleSolution (S : Setting d) (N2 : ℕ) (Q : ParticlePaths d N2) : Prop :=
  ContinuousOn (fun z : ℝ × (Fin N2 → ℝ) => Q.Cp z.1 z.2)
    (Icc 0 1 ×ˢ {cv | ∀ i, cv i ∈ S.Cset}) ∧
  ContinuousOn (fun z : ℝ × ((Fin N2 → ℝ) × (E d × (Fin N2 → ℝ))) =>
      Q.W1p z.1 z.2.1 z.2.2.1 z.2.2.2)
    (Icc 0 1 ×ˢ ({cv | ∀ i, cv i ∈ S.Cset} ×ˢ
      (S.W1set ×ˢ {uv | ∀ i, uv i ∈ S.W2set}))) ∧
  (∀ i : Fin N2, ContinuousOn (fun z : ℝ × ((Fin N2 → ℝ) × (E d × (Fin N2 → ℝ))) =>
      Q.W2p z.1 z.2.1 i z.2.2.1 z.2.2.2)
    (Icc 0 1 ×ˢ ({cv | ∀ i, cv i ∈ S.Cset} ×ˢ
      (S.W1set ×ˢ {uv | ∀ i, uv i ∈ S.W2set})))) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ cv : Fin N2 → ℝ, (∀ i, cv i ∈ S.Cset) → ∀ i,
    Q.Cp t cv i = cv i + ∫ s in 0..t, ∫ z,
      (z.2 - partG S Q s cv z.1) * partH2 S Q s cv i z.1 ∂S.piData) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ cv : Fin N2 → ℝ, (∀ i, cv i ∈ S.Cset) →
    ∀ w ∈ S.W1set, ∀ uv : Fin N2 → ℝ, (∀ i, uv i ∈ S.W2set) →
    Q.W1p t cv w uv = w + ∫ s in 0..t, ∫ z,
      ((z.2 - partG S Q s cv z.1) * partV S Q s cv w uv z.1 *
        deriv S.σ (inner ℝ (Q.W1p s cv w uv) z.1)) • z.1 ∂S.piData) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, ∀ cv : Fin N2 → ℝ, (∀ i, cv i ∈ S.Cset) →
    ∀ w ∈ S.W1set, ∀ uv : Fin N2 → ℝ, (∀ i, uv i ∈ S.W2set) → ∀ i,
    Q.W2p t cv i w uv = uv i + ∫ s in 0..t, ∫ z,
      (z.2 - partG S Q s cv z.1) * Q.Cp s cv i *
        deriv S.σ (partZ S Q s cv i z.1) * partH1 S Q s cv w uv z.1 ∂S.piData)

/-- The five squared discrepancies in the error function of §5.1. -/
def errFn (S : Setting d) (L : LimitPaths d) (Q : ParticlePaths d N2)
    (t : ℝ) (cv : Fin N2 → ℝ) (i : Fin N2) (w : E d)
    (uv : Fin N2 → ℝ) (x : E d) : ℝ :=
  (Q.Cp t cv i - L.Ct t (cv i)) ^ 2 +
  ‖Q.W1p t cv w uv - L.W1t t w‖ ^ 2 +
  (Q.W2p t cv i w uv - L.W2t t (cv i) w (uv i)) ^ 2 +
  (partH2 S Q t cv i x - limH2 S L t (cv i) x) ^ 2 +
  (partZ S Q t cv i x - limZ S L t (cv i) x) ^ 2

end MeanFieldDNN.TwoLayer


