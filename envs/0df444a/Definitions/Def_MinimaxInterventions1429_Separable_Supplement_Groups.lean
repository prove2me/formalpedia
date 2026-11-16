-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Groups
-- name    : MinimaxInterventions1429_Separable_Supplement_Groups
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:12:47.664848+00:00
-- url     : https://prove2.me/theorems/a93fdea2-60a0-4bda-bfcf-ad5681f6445f
-- title:
--   Public group designs, centered releases, spectral quantities, and mechanisms
-- statement:
--   There are $N$ binary private labels $y$, $m$ indexed nonempty public groups $G_g$, public weights $|w_x|\le1$, and $0\le\theta\le1/4$. With $A_{gx}=\mathbf1\{x\in G_g\}/|G_g|$, define
--   $$L_\theta(y)=\tfrac14\mathbf1+\tfrac12(Ay)\mathbf1_2^\top+\theta[0,Aw],\qquad\Lambda=\theta\operatorname{osc}(Aw).$$
--   Replacement adjacency changes exactly one label. The centered release error of $Ay$ uses half the oscillation of $v-Ay$, exactly $\inf_\lambda\|v-Ay-\lambda\mathbf1\|_\infty$. The infimal private error is $\mathrm{err}_A$. For compact added controls, $\Lambda_K=\max_{C\in K}\Lambda(L_\theta(0)+C)$.
--
--   For a row set $R\ne\varnothing$ and an even individual set $S$ of size at least two, $V_S$ consists of zero-sum vectors supported on $S$, and $\sigma_{R,S}$ minimizes $\|\Pi_RA_Rz\|_2$ on its unit sphere. The hereditary quantity is
--   $$\sigma(A)=\max_{R,S}\sigma_{R,S}(A)\sqrt{|S|/|R|}.$$
--   An empty outer maximum is zero. The balanced label class fixes labels off $S$ and has exactly $|S|/2$ ones on $S$. Define $\pi_{\varepsilon,\delta}=(1-(1+e^\varepsilon)\delta)/(1+e^{2\varepsilon})$ and $\varpi=\sqrt{(\pi-\beta)/(1-\beta)}$.
--
--   The known-contrast program skips estimation, uses tolerance $\alpha$, fails at diameter at most $8\alpha$, and runs the published level search with zero contrast error. The mechanisms are independent Laplace noise on individual labels or membership-atom counts, followed by averaging and exact minimization; public bound comparison selects between these and the public additive decoder. Neither privacy, accuracy, nor tail bounds is assumed by the definitions. Duplicate and singleton groups and zero interaction are included.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Sections 6.3–6.7, Eq. (4), Definition 6.2, printed pp.19–24 (PDF pp.21–26)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Privacy
set_option autoImplicit false

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

abbrev Labels (N : ℕ) := Fin N → Bool

def replacement {N : ℕ} (y z : Labels N) : Prop :=
  ∃ x, y x ≠ z x ∧ ∀ t, t ≠ x → y t = z t

structure GroupDesign (N m : ℕ) where
  groups : Fin m → Finset (Fin N)
  nonempty : ∀ g, (groups g).Nonempty
  w : Fin N → ℝ
  w_bound : ∀ x, |w x| ≤ 1
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  theta_le : theta ≤ 1 / 4

def GroupDesign.matrix {N m : ℕ} (d : GroupDesign N m) : Fin m → Fin N → ℝ :=
  fun g x => if x ∈ d.groups g then 1 / (d.groups g).card else 0

def GroupDesign.apply {N m : ℕ} (d : GroupDesign N m) (z : Fin N → ℝ) (g : Fin m) : ℝ :=
  ∑ x, d.matrix g x * z x

def labelVector {N : ℕ} (y : Labels N) : Fin N → ℝ := fun x => if y x then 1 else 0

def GroupDesign.table {N m : ℕ} (d : GroupDesign N m) (y : Labels N) : Table m 2 :=
  fun g h => 1 / 4 + d.apply (labelVector y) g / 2 +
    if h = 0 then 0 else d.theta * d.apply d.w g

def GroupDesign.lambda {N m : ℕ} (d : GroupDesign N m) : ℝ :=
  d.theta * ((⨆ g, d.apply d.w g) - (⨅ g, d.apply d.w g))

def GroupDesign.nmin {N m : ℕ} (d : GroupDesign N m) : ℝ :=
  ⨅ g, ((d.groups g).card : ℝ)

def GroupDesign.atoms {N m : ℕ} (d : GroupDesign N m) : Finset (Fin m → Bool) := by
  classical
  exact Finset.univ.image (fun x g => decide (x ∈ d.groups g))

abbrev GroupDesign.Atom {N m : ℕ} (d : GroupDesign N m) := {a // a ∈ d.atoms}

def GroupDesign.nat {N m : ℕ} (d : GroupDesign N m) : ℕ := d.atoms.card

def centeredError {m : ℕ} (v a : Fin m → ℝ) : ℝ :=
  ((⨆ g, v g - a g) - (⨅ g, v g - a g)) / 2

def centeredAccurate {N m : ℕ} (d : GroupDesign N m)
    (law : Labels N → Measure (Fin m → ℝ)) (β τ : ℝ)
    (X : Set (Labels N) := Set.univ) : Prop :=
  ∀ y ∈ X, Success (law y) β (fun v => centeredError v (d.apply (labelVector y)) ≤ τ)

def centeredReleaseError {N m : ℕ} (d : GroupDesign N m) (ε δ β : ℝ) : ℝ :=
  sInf {τ | 0 ≤ τ ∧ ∃ law : Labels N → Measure (Fin m → ℝ),
    (∀ y, IsProbabilityMeasure (law y)) ∧ DifferentiallyPrivate replacement ε δ law ∧
      centeredAccurate d law β τ}

def attainableInteraction {N m : ℕ} (d : GroupDesign N m) (K : Set (Table m 2)) : ℝ :=
  sSup {a | ∃ C ∈ K, a = interaction (d.table (fun _ => false) + C)}

def balancedClass {N : ℕ} (S : Finset (Fin N)) (y₀ : Labels N) : Set (Labels N) :=
  {y | (∀ x, x ∉ S → y x = y₀ x) ∧ (S.filter (fun x => y x)).card = S.card / 2}

def l2 {n : ℕ} (z : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, (z i)^2)

def balancedVector {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℝ) : Prop :=
  (∀ x, x ∉ S → z x = 0) ∧ ∑ x, z x = 0

def projectedLength {N m : ℕ} (A : Fin m → Fin N → ℝ)
    (R : Finset (Fin m)) (z : Fin N → ℝ) : ℝ :=
  let f := fun g => ∑ x, A g x * z x
  Real.sqrt (∑ g ∈ R, (f g - (∑ r ∈ R, f r) / R.card)^2)

/-- The inner sphere is used only for |S|≥2; otherwise its declared value is zero. -/
def restrictedSigma {N m : ℕ} (A : Fin m → Fin N → ℝ)
    (R : Finset (Fin m)) (S : Finset (Fin N)) : ℝ :=
  if R.Nonempty ∧ 2 ≤ S.card then
    sInf {t | ∃ z, balancedVector S z ∧ l2 z = 1 ∧ t = projectedLength A R z}
  else 0

def spectralSigma {N m : ℕ} (A : Fin m → Fin N → ℝ) : ℝ :=
  sSup {t | ∃ (R : Finset (Fin m)) (S : Finset (Fin N)),
    R.Nonempty ∧ 2 ≤ S.card ∧ Even S.card ∧
      t = restrictedSigma A R S * Real.sqrt ((S.card : ℝ) / R.card)}

def privacyPi (ε δ : ℝ) : ℝ := (1 - (1 + Real.exp ε) * δ) / (1 + Real.exp (2 * ε))
def varpi (ε δ β : ℝ) : ℝ := Real.sqrt ((privacyPi ε δ - β) / (1 - β))

/-- Exact public contrasts, failure threshold 8α and the same first diameter anchors. -/
def knownPlan {m k : ℕ} [NeZero m] [NeZero k] (α : ℝ) (w : Table m k) : Option (AnchorPlan m) := by
  classical
  if estimatedDiameter w ≤ 8 * α then exact none
  else
    let h := firstMax (fun j => (⨆ g, w g j) - (⨅ g, w g j))
    let g₀ := firstMax (fun g => w g h)
    let r₀ := firstMin (fun g => w g h)
    exact some ⟨g₀,r₀,fun g => if g = g₀ then g₀ else if g = r₀ then g₀
      else if rowDistance w g g₀ ≥ rowDistance w g r₀ then g₀ else r₀⟩

def knownLevels {m k : ℕ} [NeZero k] (α : ℝ) (T : ℕ) (w : Table m k) (plan : AnchorPlan m) :
    List (Fin m) → (Fin m → ℝ) → BitProgram m k (Option (Table m k))
  | [],a => .done (some (fun g h => a g + w g h))
  | g :: rest,a =>
    let r := plan.parent g
    match eligibleColumn w α g r with
    | none => .done none
    | some h => if w r h < w g h then
        (levelSearch α 0 T w g r h).bind (fun x => knownLevels α T w plan rest (Function.update a g (a r + x)))
      else (levelSearch α 0 T w r g h).bind (fun x => knownLevels α T w plan rest (Function.update a g (a r - x)))

def knownAlignment {m k : ℕ} [NeZero m] [NeZero k] (α : ℝ) (T : ℕ) (w : Table m k) :
    BitProgram m k (Option (Table m k)) :=
  match knownPlan α w with
  | none => .done none
  | some plan => knownLevels α T w plan (alignmentOrder plan) 0

/-- Single supplied public control; the private baselines never enter the query policy. -/
def knownCenteredOutput {N m : ℕ} [NeZero m] {S : Type*}
    (d : GroupDesign N m) (Dec : S → Table m 2 → Mixture 2)
    (C : Table m 2) (τ α : ℝ) (T : ℕ) (s : S) : Fin m → ℝ :=
  let w := contrasts (normalized (d.table (fun _ => false)) C τ)
  let M := ((shiftProgram C τ (knownAlignment (α / dilation τ) T w)).run
    (thresholdOracle (Dec s)) []).1.getD 0
  let L := unnormalize M C τ
  fun g => 2 * L g 0 - 1 / 2

/-- Density of Lap(1/ε), used only for ε>0 in the mechanisms. -/
def laplaceNoise (ε : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (ε / 2 * Real.exp (-ε * |x|)))

def individualRelease {N m : ℕ} (d : GroupDesign N m) (ε : ℝ)
    (y : Labels N) : Measure (Fin m → ℝ) :=
  (Measure.pi (fun _ : Fin N => laplaceNoise ε)).map
    (fun ξ => d.apply (fun x => labelVector y x + ξ x))

def atomCount {N m : ℕ} (d : GroupDesign N m) (y : Labels N) (a : d.Atom) : ℝ :=
  ∑ x : Fin N, if (fun g => decide (x ∈ d.groups g)) = a.val then labelVector y x else 0

def atomRelease {N m : ℕ} (d : GroupDesign N m) (ε : ℝ)
    (y : Labels N) : Measure (Fin m → ℝ) :=
  (Measure.pi (fun _ : d.Atom => laplaceNoise ε)).map (fun ξ g =>
    (∑ a : d.Atom, if a.val g then atomCount d y a + ξ a else 0) / (d.groups g).card)

def releasedTable {N m : ℕ} (d : GroupDesign N m) (v : Fin m → ℝ) : Table m 2 :=
  fun g h => 1 / 4 + v g / 2 + if h = 0 then 0 else d.theta * d.apply d.w g

def releaseDecoder {N m : ℕ} (d : GroupDesign N m) (v : Fin m → ℝ) (B : Table m 2) : Mixture 2 :=
  selectMinimizer (releasedTable d v + B)

def individualBound {N m : ℕ} (d : GroupDesign N m) (ε : ℝ) : ℝ :=
  (2 * Real.sqrt (Real.log (6 * m) / d.nmin) + Real.log (6 * m) / d.nmin) / ε

def atomBound {N m : ℕ} (d : GroupDesign N m) (ε : ℝ) : ℝ :=
  (d.nat + Real.sqrt (2 * d.nat * Real.log 3) + Real.log 3) / (ε * d.nmin)

/-- The midpoint additive approximation uses only public query contrasts. -/
def publicDecoder {N m : ℕ} [NeZero m] (d : GroupDesign N m) (B : Table m 2) : Mixture 2 :=
  let r := contrasts (d.table (fun _ => false) + B)
  let h := firstMin (fun j => ((⨆ g, r g j) + (⨅ g, r g j)) / 2)
  ⟨Pi.single h 1, single_mem_stdSimplex ℝ h⟩

def bestUpperLaw {N m : ℕ} (d : GroupDesign N m) (ε : ℝ) (y : Labels N) :
    Measure (Unit ⊕ (Fin m → ℝ)) :=
  if d.lambda ≤ individualBound d ε ∧ d.lambda ≤ atomBound d ε then Measure.dirac (Sum.inl ())
  else if individualBound d ε ≤ atomBound d ε then
    (individualRelease d ε y).map Sum.inr
  else (atomRelease d ε y).map Sum.inr

def bestUpperDecoder {N m : ℕ} [NeZero m] (d : GroupDesign N m)
    (s : Unit ⊕ (Fin m → ℝ)) (B : Table m 2) : Mixture 2 :=
  match s with
  | .inl _ => publicDecoder d B
  | .inr v => releaseDecoder d v B

end MinimaxInterventions1429.Separable.Supplement


