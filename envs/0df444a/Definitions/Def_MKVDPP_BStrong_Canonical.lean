-- Prove2me | Definitions.Def_MKVDPP_BStrong_Canonical
-- name    : MKVDPP_BStrong_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:25:21.960582+00:00
-- url     : https://prove2.me/theorems/b23137f5-e93d-437a-83a8-cc99a5049d56
-- title:
--   Canonical weak and strong control rules
-- statement:
--   The canonical rule space records $(X,A,W,B,\hat\mu)$, with $A$ the integrated embedded control and $\hat\mu$ a continuous measure valued path. A weak rule satisfies the initial law, conditional law, moment and localized martingale conditions of Definition 4.1. A strong rule admits Borel feedback from the initial state and both noise increments; a $\mathbb B$ strong rule admits feedback from common noise alone.
--
--   The canonical reward is
--
--   $$J(t,\bar P)=\mathbb E^{\bar P}\!\left[\int_t^T L(s,X_{s\wedge\cdot},\bar\mu_s,\bar\alpha_s)\,ds+g(X,\mu_T)\right].$$
--
--   Wiener represented rule classes and stopped sigma algebras provide the objects used in the later milestones.
--
--   **Formalization Note** The control recovered from $A$ has a cemetery value on invalid paths; coefficients use a fixed default there. The localized martingale requirement uses the stopped processes displayed in the paper. Valid rules avoid the default almost surely.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, pp. 14–16, equations (4.1)–(4.9), Definitions 4.1 and 4.3; pp. 23–25, §4.3.3

import Definitions.Def_MKVDPP_BStrong_FixedSpace

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

variable {T : ℝ≥0} {n d ell : ℕ} {U : Type*}
variable [MetricSpace U] [CompleteSpace U] [TopologicalSpace.SeparableSpace U]
variable [Nonempty U] [MeasurableSpace U] [BorelSpace U]

instance {V : Type*} [MeasurableSpace V] : MeasurableSpace (Option V) :=
  MeasurableSpace.generateFrom <|
    {S | ∃ A : Set V, MeasurableSet A ∧ S = some '' A} ∪ { {none} }

/-- The state-plus-two-noises space for the controlled martingale problem. -/
abbrev Z (n d ell : ℕ) := EuclideanSpace ℝ (Fin n) ×
  EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin ell)

/-- The second canonical space Ω̄ of Section 4.1. -/
abbrev OmegaBar (T : ℝ≥0) (n d ell : ℕ) :=
  OmegaHat T n d ell ×
    C(Set.Icc (0 : ℝ) (T : ℝ), ProbabilityMeasure (OmegaHat T n d ell))

noncomputable instance (T : ℝ≥0) (n d ell : ℕ) :
    TopologicalSpace (ProbabilityMeasure (OmegaBar T n d ell)) :=
  @ProbabilityMeasure.instTopologicalSpace (OmegaBar T n d ell)
    (inferInstance : MeasurableSpace (OmegaBar T n d ell))
    (inferInstance : TopologicalSpace (OmegaBar T n d ell))
    (inferInstance : OpensMeasurableSpace (OmegaBar T n d ell))

/-- Coordinate processes on Ω̄. -/
noncomputable def barX (ω : OmegaBar T n d ell) : Cpath T n := ω.1.1
noncomputable def barA (ω : OmegaBar T n d ell) : CR T := ω.1.2.1
noncomputable def barW (ω : OmegaBar T n d ell) : Cpath T d := ω.1.2.2.1
noncomputable def barB (ω : OmegaBar T n d ell) : Cpath T ell := ω.1.2.2.2
noncomputable def barMuHat (ω : OmegaBar T n d ell) (s : ℝ≥0) :
    ProbabilityMeasure (OmegaHat T n d ell) :=
  ω.2 ⟨min (s : ℝ) (T : ℝ), ⟨le_min s.property T.property, min_le_right _ _⟩⟩

/-- The limsup derivative of an integrated scalar control. -/
noncomputable def controlDerivative (A : CR T) (s : ℝ≥0) : EReal :=
  Filter.limsup (fun k : ℕ =>
    (((k : ℝ) * (scalarAt A s - scalarAt A (s - (1 / (k : ℝ≥0))))) : EReal)) atTop

/-- The cemetery-valued canonical control α̂ and ᾱ. -/
noncomputable def hatAlpha (M : Model T n d ell U) (s : ℝ≥0)
    (z : OmegaHat T n d ell) : Option U := piInv M (controlDerivative z.2.1 s)

noncomputable def barAlpha (M : Model T n d ell U) (s : ℝ≥0)
    (ω : OmegaBar T n d ell) : Option U := piInv M (controlDerivative (barA ω) s)

/-- The canonical state conditional-law process μ_s. -/
noncomputable def barMu (s : ℝ≥0) (ω : OmegaBar T n d ell) :
    ProbabilityMeasure (Cpath T n) :=
  (barMuHat ω s).map
    ((measurable_stopPath s).comp measurable_fst |>.aemeasurable)

/-- Common-noise increments of the canonical B coordinate. -/
noncomputable def barBt (t s : ℝ≥0) (ω : OmegaBar T n d ell) :
    EuclideanSpace ℝ (Fin ell) :=
  pathAt (barB ω) (max s t) - pathAt (barB ω) t

/-- The raw common-noise filtration 𝒢̄ᵗ, equation (4.1). -/
noncomputable def rawGbar (t s : ℝ≥0) : MeasurableSpace (OmegaBar T n d ell) :=
  if s < t then ⊥ else
    ⨆ r : ℝ≥0, ⨆ _ : r ≤ s,
      MeasurableSpace.comap
        (fun ω : OmegaBar T n d ell => (barBt t r ω, barMuHat ω r)) inferInstance

/-- The natural canonical filtration F̄. -/
noncomputable def rawFbar (s : ℝ≥0) : MeasurableSpace (OmegaBar T n d ell) :=
  ⨆ r : ℝ≥0, ⨆ _ : r ≤ s,
    MeasurableSpace.comap
      (fun ω : OmegaBar T n d ell =>
        (pathAt (barX ω) r, scalarAt (barA ω) r,
          pathAt (barW ω) r, pathAt (barB ω) r, barMuHat ω r)) inferInstance

/-- A bounded C² test function and its first two bounded derivatives. -/
def IsC2b (φ : Z n d ell → ℝ) : Prop :=
  ContDiff ℝ 2 φ ∧ Bornology.IsBounded (Set.range φ) ∧
  Bornology.IsBounded (Set.range (fderiv ℝ φ)) ∧
  Bornology.IsBounded (Set.range (fderiv ℝ (fderiv ℝ φ)))

/-- The k-th column of the block diffusion matrix in (4.3). -/
noncomputable def diffusionColumn (M : Model T n d ell U)
    (s : ℝ≥0) (x : Cpath T n)
    (μ : ProbabilityMeasure (Cpath T n × U)) (u : U)
    (k : Fin (d + ell)) : Z n d ell :=
  if h : k.val < d then
    (WithLp.toLp 2 (fun i : Fin n => M.σ s x μ u i ⟨k.val, h⟩),
      WithLp.toLp 2 (fun j : Fin d => if j.val = k.val then 1 else 0),
      0)
  else
    (WithLp.toLp 2 (fun i : Fin n => M.σ₀ s x μ u i
      ⟨k.val - d, by omega⟩),
      0,
      WithLp.toLp 2 (fun j : Fin ell => if j.val = k.val - d then 1 else 0))

/-- The generator (4.2)–(4.3), expressed by the diffusion columns cₖ. -/
noncomputable def generator (M : Model T n d ell U)
    (s : ℝ≥0) (x : Cpath T n)
    (μ : ProbabilityMeasure (Cpath T n × U)) (u : U)
    (φ : Z n d ell → ℝ) (z : Z n d ell) : ℝ :=
  fderiv ℝ φ z (M.b s x μ u, 0, 0) +
    (1 / 2 : ℝ) * ∑ k : Fin (d + ell),
      fderiv ℝ (fderiv ℝ φ) z
        (diffusionColumn M s x μ u k) (diffusionColumn M s x μ u k)

/-- The Frobenius norm of the covariance matrix c cᵀ in (4.3). -/
noncomputable def covarianceNorm (M : Model T n d ell U)
    (s : ℝ≥0) (x : Cpath T n)
    (μ : ProbabilityMeasure (Cpath T n × U)) (u : U) : ℝ :=
  Real.sqrt (∑ i : Fin (n + d + ell), ∑ j : Fin (n + d + ell),
    (∑ k : Fin (d + ell),
      let c := diffusionColumn M s x μ u k
      let ci : ℝ := if h : i.val < n then c.1 ⟨i.val, h⟩ else
        if h : i.val < n + d then c.2.1 ⟨i.val - n, by omega⟩ else
          c.2.2 ⟨i.val - n - d, by omega⟩
      let cj : ℝ := if h : j.val < n then c.1 ⟨j.val, h⟩ else
        if h : j.val < n + d then c.2.1 ⟨j.val - n, by omega⟩ else
          c.2.2 ⟨j.val - n - d, by omega⟩
      ci * cj) ^ 2)

/-- Stop every Ω̂ coordinate, as in the initial law in Definition 4.1. -/
noncomputable def fullStopped (s : ℝ≥0) (z : OmegaHat T n d ell) :
    OmegaHat T n d ell :=
  (stopPath s z.1, z.2.1.comp (stopTimeMap s),
    stopPath s z.2.2.1, stopPath s z.2.2.2)

/-- Canonical U-valued and conditional control-law versions. They agree with
ᾱ and μ̄ outside the paper's dP ⊗ ds-null exceptional set. -/
structure CanonicalWitness (M : Model T n d ell U)
    (P : ProbabilityMeasure (OmegaBar T n d ell)) where
  start : ℝ≥0
  α : ℝ≥0 → OmegaBar T n d ell → U
  μbar : ℝ≥0 → OmegaBar T n d ell → ProbabilityMeasure (Cpath T n × U)
  α_measurable : Measurable (fun z : ℝ≥0 × OmegaBar T n d ell => α z.1 z.2)
  μbar_measurable : Measurable (fun z : ℝ≥0 × OmegaBar T n d ell => μbar z.1 z.2)
  α_version : ∀ᵐ s ∂volume.restrict (Set.Icc (start : ℝ) (T : ℝ)),
    ∀ᵐ ω ∂P.toMeasure,
      barAlpha M s.toNNReal ω = some (α s.toNNReal ω)
  μbar_version : ∀ᵐ s ∂volume.restrict (Set.Icc (start : ℝ) (T : ℝ)),
    ∀ᵐ ω ∂P.toMeasure,
      Measure.map (fun z : Cpath T n × U => (z.1, some z.2))
        ((μbar s.toNNReal ω : ProbabilityMeasure (Cpath T n × U)) : Measure (Cpath T n × U)) =
      Measure.map (fun z : OmegaHat T n d ell =>
        (stopPath s.toNNReal z.1, hatAlpha M s.toNNReal z))
        (barMuHat ω s.toNNReal : Measure (OmegaHat T n d ell))

/-- The canonical state, idiosyncratic noise and common noise at a time. -/
noncomputable def barZ (s : ℝ≥0) (ω : OmegaBar T n d ell) : Z n d ell :=
  (pathAt (barX ω) s, pathAt (barW ω) s, pathAt (barB ω) s)

/-- The localization size |S̄| of (4.4). -/
noncomputable def absSbar (M : Model T n d ell U)
    {P : ProbabilityMeasure (OmegaBar T n d ell)} (w : CanonicalWitness M P)
    (s : ℝ≥0) (ω : OmegaBar T n d ell) : ℝ≥0∞ :=
  ∫⁻ r in Set.Icc (0 : ℝ) (s : ℝ),
    ENNReal.ofReal
      (‖M.b r.toNNReal (stopPath r.toNNReal (barX ω))
        (w.μbar r.toNNReal ω) (w.α r.toNNReal ω)‖ +
      covarianceNorm M r.toNNReal (stopPath r.toNNReal (barX ω))
        (w.μbar r.toNNReal ω) (w.α r.toNNReal ω)) ∂volume

/-- τ_m = inf{r∈[0,T] : |S̄|_r ≥ m}, with inf ∅ = ∞. -/
noncomputable def tauM (M : Model T n d ell U)
    {P : ProbabilityMeasure (OmegaBar T n d ell)} (w : CanonicalWitness M P)
    (m : ℕ) (ω : OmegaBar T n d ell) : WithTop ℝ≥0 :=
  sInf (((↑) : ℝ≥0 → WithTop ℝ≥0) ''
    {r : ℝ≥0 | r ≤ T ∧ (m : ℝ≥0∞) ≤ absSbar M w r ω})

/-- The stopped time s∧τ_m, which is finite because s is finite. -/
noncomputable def stoppedAt (M : Model T n d ell U)
    {P : ProbabilityMeasure (OmegaBar T n d ell)} (w : CanonicalWitness M P)
    (m : ℕ) (s : ℝ≥0) (ω : OmegaBar T n d ell) : ℝ≥0 :=
  (min (s : WithTop ℝ≥0) (tauM M w m ω)).untopD 0

/-- The generator-corrected process S̄^φ of (4.4). -/
noncomputable def Sbar (M : Model T n d ell U)
    {P : ProbabilityMeasure (OmegaBar T n d ell)} (w : CanonicalWitness M P)
    (φ : Z n d ell → ℝ) (s : ℝ≥0) (ω : OmegaBar T n d ell) : EReal :=
  (φ (barZ s ω) : EReal) -
    timeInt 0 s (fun r =>
      (generator M r (barX ω) (w.μbar r ω) (w.α r ω) φ (barZ r ω) : EReal))

/-- Local martingale on [t,T], via the paper's τ_m localization. -/
def IsLocalMartingale (M : Model T n d ell U)
    {P : ProbabilityMeasure (OmegaBar T n d ell)} (w : CanonicalWitness M P)
    (t : ℝ≥0) (φ : Z n d ell → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ S : ℝ≥0 → OmegaBar T n d ell → ℝ,
    (∀ s, s ≤ T → ∀ᵐ ω ∂P.toMeasure,
      (S s ω : EReal) = Sbar M w φ (stoppedAt M w m s ω) ω) ∧
    (∀ s, t ≤ s → s ≤ T → Integrable (S s) P.toMeasure) ∧
    (∀ r s, t ≤ r → r ≤ s → s ≤ T →
      P.toMeasure[S s | rawFbar r] =ᵐ[P.toMeasure] S r)

/-- Definition 4.1: a weak control rule on Ω̄ with initial law ν̂. -/
def IsWeakControlRule (M : Model T n d ell U) (t : ℝ≥0)
    (νhat : ProbabilityMeasure (OmegaHat T n d ell))
    (P : ProbabilityMeasure (OmegaBar T n d ell)) : Prop :=
  ∃ w : CanonicalWitness M P,
    w.start = t ∧
    (∀ᵐ s ∂volume.restrict (Set.Icc (t : ℝ) (T : ℝ)),
      P.toMeasure {ω | barAlpha M s.toNNReal ω ≠ none} = 1) ∧
    (∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) (T : ℝ),
      edist (w.α s.toNNReal ω) M.u₀ ^ (2 : ℝ) ∂volume ∂P.toMeasure) < ⊤ ∧
    (∀ s, s ≤ t → s ≤ T → ∀ᵐ ω ∂P.toMeasure,
      (barMuHat ω s : Measure (OmegaHat T n d ell)) =
        Measure.map (hatStopped s ∘ fun ω => ω.1) P.toMeasure) ∧
    (∀ s, t < s → s ≤ T →
      ∃ m : OmegaBar T n d ell → ProbabilityMeasure (OmegaHat T n d ell),
        IsCondLaw (rawGbar t s) P.toMeasure
          (hatStopped s ∘ fun ω => ω.1) m ∧
        (fun ω => barMuHat ω s) =ᵐ[P.toMeasure] m) ∧
    Measure.map (fullStopped t ∘ fun ω : OmegaBar T n d ell => ω.1) P.toMeasure =
      Measure.map (fullStopped t) (νhat : Measure (OmegaHat T n d ell)) ∧
    (∫⁻ ω, ENNReal.ofReal (‖barX ω‖ ^ 2) ∂P.toMeasure) < ⊤ ∧
    P.toMeasure {ω | absSbar M w T ω < ⊤} = 1 ∧
    (∀ φ : Z n d ell → ℝ, IsC2b φ → IsLocalMartingale M w t φ)

/-- The weak-rule classes P̂_W and P̄_W. -/
def PhatW (M : Model T n d ell U) (t : ℝ≥0)
    (νhat : ProbabilityMeasure (OmegaHat T n d ell)) :
    Set (ProbabilityMeasure (OmegaBar T n d ell)) :=
  {P | IsWeakControlRule M t νhat P}

def PbarW (M : Model T n d ell U) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Cpath T n)) :
    Set (ProbabilityMeasure (OmegaBar T n d ell)) :=
  {P | ∃ νhat : ProbabilityMeasure (OmegaHat T n d ell),
    Measure.map (fun z : OmegaHat T n d ell => z.1) (νhat : Measure (OmegaHat T n d ell)) =
      (ν : Measure (Cpath T n)) ∧ P ∈ PhatW M t νhat}

/-- Reward (4.9), allowing any canonical versions (which agree P-a.s.). -/
noncomputable def Jbar (M : Model T n d ell U) (t : ℝ≥0)
    (P : ProbabilityMeasure (OmegaBar T n d ell)) : EReal :=
  ⨆ (w : CanonicalWitness M P),
    ⨆ (_ : w.start = t), eExp P.toMeasure (fun ω =>
      timeInt t T (fun s =>
        (M.L s (stopPath s (barX ω)) (w.μbar s ω) (w.α s ω) : EReal)) +
      (M.g (barX ω) (barMu T ω) : EReal))

/-- Restrict and stop a noise increment on [t,T]. -/
noncomputable def stoppedNoiseSegment {k : ℕ} (t : ℝ≥0) (ht : t ≤ T)
    (s : ℝ≥0) (b : Cpath T k) : Csegment t T k :=
  ⟨(fun r : Set.Icc (t : ℝ) (T : ℝ) =>
    b ⟨min (r : ℝ) (max (t : ℝ) (s : ℝ)),
      ⟨le_min (t.property.trans r.property.1)
        (t.property.trans (le_max_left _ _)),
        (min_le_left _ _).trans r.property.2⟩⟩ - pathAt b t), by fun_prop⟩

/-- The Bᵗ_{s∧·} input of Definition 4.3. -/
noncomputable def Bsegment (t : ℝ≥0) (ht : t ≤ T) (s : ℝ≥0)
    (b : Cpath T ell) : Csegment t T ell :=
  stoppedNoiseSegment t ht s b

/-- Definition 4.3: a B-strong rule has a Borel feedback from common noise. -/
def PbarSB (M : Model T n d ell U) (t : ℝ≥0) (ht : t ≤ T)
    (ν : ProbabilityMeasure (Cpath T n)) :
    Set (ProbabilityMeasure (OmegaBar T n d ell)) :=
  {P | P ∈ PbarW M t ν ∧
    ∃ φ : ℝ≥0 → Csegment t T ell → U,
      Measurable (fun z : ℝ≥0 × Csegment t T ell => φ z.1 z.2) ∧
      ∀ s, t ≤ s → s ≤ T →
        (fun ω => barAlpha M s ω) =ᵐ[P.toMeasure]
          (fun ω => some (φ s (Bsegment t ht s (barB ω))))}

/-- Restrict the state path to [0,t]. -/
noncomputable def initialSegment (t : ℝ≥0) (ht : t ≤ T)
    (x : Cpath T n) : Csegment 0 t n :=
  x.comp ⟨(fun r : Set.Icc (0 : ℝ) (t : ℝ) =>
    (⟨(r : ℝ), ⟨r.property.1, r.property.2.trans (by exact_mod_cast ht)⟩⟩ :
      Set.Icc (0 : ℝ) (T : ℝ))), by fun_prop⟩

/-- The (X_{t∧·}, Wᵗ_{s∧·}, Bᵗ_{s∧·}) selector input. -/
noncomputable def barOmegaT (t : ℝ≥0) (ht : t ≤ T) (s : ℝ≥0)
    (ω : OmegaBar T n d ell) : OmegaT T n d ell t :=
  (initialSegment t ht (barX ω),
    stoppedNoiseSegment t ht s (barW ω),
    stoppedNoiseSegment t ht s (barB ω))

/-- Definition 4.3: a strong control rule has Borel feedback from the full
initial-state and Brownian observations. -/
def PbarS (M : Model T n d ell U) (t : ℝ≥0) (ht : t ≤ T)
    (ν : ProbabilityMeasure (Cpath T n)) :
    Set (ProbabilityMeasure (OmegaBar T n d ell)) :=
  {P | P ∈ PbarW M t ν ∧
    ∃ φ : ℝ≥0 → OmegaT T n d ell t → U,
      Measurable (fun z : ℝ≥0 × OmegaT T n d ell t => φ z.1 z.2) ∧
      ∀ s, t ≤ s → s ≤ T →
        (fun ω => barAlpha M s ω) =ᵐ[P.toMeasure]
          (fun ω => some (φ s (barOmegaT t ht s ω)))}

/-- The canonical law P̄^γ of a weak control. -/
def InducedBy {Ω : Type} [MeasurableSpace Ω]
    {M : Model T n d ell U} {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}
    (γ : WeakControl M Ω t ν)
    (Pbar : ProbabilityMeasure (OmegaBar T n d ell)) : Prop :=
  (Pbar : Measure (OmegaBar T n d ell)) =
    Measure.map (fun ω => ((γ.X ω, γ.A ω, γ.W ω, γ.B ω), γ.μhat ω))
      γ.P.toMeasure

/-- The moment truncation P̄ᵗ_M of Section 4.2, with p=2. -/
def PbarM (M : Model T n d ell U) (t : ℝ≥0) (bound : ℝ≥0)
    (P : ProbabilityMeasure (OmegaBar T n d ell)) : Prop :=
  ∃ w : CanonicalWitness M P,
    w.start = t ∧
    (∫⁻ ω, ENNReal.ofReal (‖barX ω‖ ^ 2) ∂P.toMeasure) +
      (∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) (T : ℝ),
        edist (w.α s.toNNReal ω) M.u₀ ^ (2 : ℝ) ∂volume ∂P.toMeasure) ≤ bound

/-- Natural filtration of the Wiener path. -/
noncomputable def rawWiener (s : ℝ≥0) : MeasurableSpace (Cpath T ell) :=
  MeasurableSpace.comap (stopPath s) inferInstance

/-- A Wiener measure on C^ℓ, characterized by its coordinate process. -/
def IsWiener (Pstar : ProbabilityMeasure (Cpath T ell)) : Prop :=
  Pstar.toMeasure {b | pathAt b 0 = 0} = 1 ∧
  IsBrownianFor rawWiener Pstar.toMeasure 0 T (fun s b => pathAt b s)

/-- The square-integrable predictable real controls 𝒰 of Section 4.3.3.1. -/
def Utheta (Pstar : ProbabilityMeasure (Cpath T ell)) :
    Set (ℝ≥0 → Cpath T ell → ℝ) :=
  {θ | Measurable[predictableOf rawWiener]
      (fun z : ℝ≥0 × Cpath T ell => θ z.1 z.2) ∧
    ∫⁻ b, ∫⁻ s in Set.Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal ((θ s.toNNReal b) ^ 2) ∂volume ∂Pstar.toMeasure < ⊤}

/-- The image Υ(𝒰) of Brownian paths and their integrated controls. -/
def Upsilon (Pstar : ProbabilityMeasure (Cpath T ell)) :
    Set (ProbabilityMeasure (Cpath T ell × CR T)) :=
  {q | ∃ θ ∈ Utheta Pstar, ∃ Aθ : Cpath T ell → CR T,
    (∀ s, s ≤ T → ∀ᵐ b ∂Pstar.toMeasure,
      scalarAt (Aθ b) s = ∫ r in (0 : ℝ)..(s : ℝ), θ r.toNNReal b) ∧
    (q : Measure (Cpath T ell × CR T)) =
      Measure.map (fun b => (b, Aθ b)) Pstar.toMeasure}

/-- The post-t common-noise increment as a continuous path. -/
noncomputable def shiftedB (t : ℝ≥0) (b : Cpath T ell) : Cpath T ell :=
  ⟨(fun s : Set.Icc (0 : ℝ) (T : ℝ) =>
    b ⟨max (min (s : ℝ) (T : ℝ)) (min (t : ℝ) (T : ℝ)),
      ⟨le_max_of_le_left (le_min s.property.1 T.property),
        max_le (min_le_right _ _) (min_le_right _ _)⟩⟩ -
    pathAt b t), by fun_prop⟩

/-- The equivalent star class of Section 4.3.3.1. -/
def PbarStarS (M : Model T n d ell U)
    (Pstar : ProbabilityMeasure (Cpath T ell))
    (t : ℝ≥0) (ν : ProbabilityMeasure (Cpath T n)) :
    Set (ProbabilityMeasure (OmegaBar T n d ell)) :=
  {P | P ∈ PbarW M t ν ∧
    (∃ q ∈ Upsilon Pstar,
      (q : Measure (Cpath T ell × CR T)) =
        Measure.map (fun ω : OmegaBar T n d ell => (barB ω, barA ω)) P.toMeasure) ∧
    Indep (MeasurableSpace.comap (stopPath t ∘ barB) inferInstance)
      (MeasurableSpace.comap (fun ω : OmegaBar T n d ell =>
        (shiftedB t (barB ω), barA ω)) inferInstance) P.toMeasure}

/-- The star class with a specified initial four-coordinate law. -/
def PhatStarS (M : Model T n d ell U)
    (Pstar : ProbabilityMeasure (Cpath T ell))
    (t : ℝ≥0) (νhat : ProbabilityMeasure (OmegaHat T n d ell)) :
    Set (ProbabilityMeasure (OmegaBar T n d ell)) :=
  {P | P ∈ PhatW M t νhat ∧
    P ∈ PbarStarS M Pstar t
      (νhat.map (measurable_fst.aemeasurable))}

/-- The stopped σ-algebra associated with a stopping time τ. -/
def stoppedSigma {Ω : Type*} [MeasurableSpace Ω]
    (H : ℝ≥0 → MeasurableSpace Ω) (τ : Ω → ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom
    {A | ∀ s : ℝ≥0, MeasurableSet[H s] (A ∩ {ω | τ ω ≤ s})}

/-- The explicit stopping-time predicate for a raw filtration. -/
def IsStoppingFor {Ω : Type*} [MeasurableSpace Ω]
    (H : ℝ≥0 → MeasurableSpace Ω) (τ : Ω → ℝ≥0) : Prop :=
  ∀ s, MeasurableSet[H s] {ω | τ ω ≤ s}

end MKVDPP.BStrong


