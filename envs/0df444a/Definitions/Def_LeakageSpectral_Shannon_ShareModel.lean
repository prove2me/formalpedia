-- Prove2me | Definitions.Def_LeakageSpectral_Shannon_ShareModel
-- name    : LeakageSpectral_Shannon_ShareModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:17.512454+00:00
-- url     : https://prove2.me/theorems/b0de3af2-e1df-4d89-aae9-dd199da6cb03
-- title:
--   §§1.1, 2.1, Definition 1, Theorems 1, 2, Lemma 1 — the laws of additive sharing, spectrum, alignment, sharpness and $\rho^*$
-- statement:
--   Let $\mathbb G$ be a finite abelian group with $m$ elements and the discrete $\sigma$-algebra. A secret $Z$ is split into shares $S_0,\dots,S_d$ with $Z=S_0+\dots+S_d$; the shares are independent and uniform on $\mathbb G$, and $L_i$ is drawn from a Markov kernel $\tau_i$ from $\mathbb G$ to a measurable space, given $S_i$ alone. The **law of one share and its leakage**, and the **law of the secret and the global leakage** $X=(L_0,\dots,L_d)$, are
--
--   $$
--   \frac1m\sum_{s\in\mathbb G}\delta_s\otimes\tau(s),\qquad m^{-(d+1)}\sum_{s_0,\dots,s_d\in\mathbb G}\delta_{s_0+\dots+s_d}\otimes\tau_0(s_0)\otimes\dots\otimes\tau_d(s_d).
--   $$
--
--   For a channel, with $\chi_w$ running over the non-trivial characters of $\mathbb G$, the **Fourier mode of leakage** and the **normalized spectrum** are
--
--   $$
--   \lambda(w)=\mathbb E_L\big[|\hat p_{S\mid L}(w\mid L)|^2\big],\qquad q(w)=\frac{\lambda(w)}{\sum_{w'\neq0}\lambda(w')}.
--   $$
--
--   The **spectral alignment factor** is $\kappa_d=\Pr[W_0=\dots=W_d]$ for independent $W_i\sim q_i$. With
--
--   $$
--   f(r)=r\ln r-r+1,\qquad g(r)=\frac{(r-1)^2}{f(r)}\quad(g(1):=2),
--   $$
--
--   the **$D_{\mathrm{KL}}$-weighted measure** and the **leakage sharpness** are
--
--   $$
--   \mu(s,\mathrm dl)=\frac{f(r(s,l))}{\ln(2)\,I(S;L)}\,p_S(s)\,p_L(\mathrm dl),\qquad \alpha=\ln(2)\,\mathbb E_\mu\,g(r).
--   $$
--
--   Finally, the **worst-case parameter** is
--
--   $$
--   \rho^*=\sup_i\max_{w\neq0}\operatorname*{ess\,sup}_{l}|\hat p_{S_i\mid L_i}(w\mid l)|.
--   $$
--
--   Every one of these is computed from the channels. Neither the global $\chi^2$-MI, nor $\kappa_d$, nor $\alpha$ is defined through the identity the mission's theorems assert about it.
--
--   **Formalization Note** The leakage spaces are arbitrary measurable spaces, and they and the channels may differ with $i$. Lean's $\log0=0$ gives $f(0)=1$ and $g(0)=1$, which are the values under $0\ln0=0$ needed for deterministic channels. If $I(S;L)=0$ the formula for $\mu$ divides by zero; the paper's standing assumption $I(S;L)>0$ excludes this, and every theorem carries it. $\rho^*$ is computed in $[0,\infty]$, where every supremum exists.
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, §1.1, p. 3; §2.1, p. 5; Definition 1, p. 7; Theorem 1, p. 8; Lemma 1, p. 9; Theorem 2, p. 10; the law of $(Z,X)$ as used on p. 27

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon

/-- The non-trivial characters `𝒲 ∖ {0}` of the finite abelian group `G`. -/
abbrev NontrivialChar (G : Type*) [AddCommGroup G] : Type _ := {w : AddChar G ℂ // w ≠ 0}

noncomputable instance (G : Type*) [AddCommGroup G] [Fintype G] : Fintype (NontrivialChar G) :=
  Fintype.ofFinite _

section Model

variable {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]

/-- **Law of one share and its leakage** `(S, L)`: `S` is uniform on `G` and `L` is drawn from the
channel `τ` given `S` (§1.1, p. 3, §2.1, p. 5): `(1/m) ∑_s δ_s ⊗ τ(s)`, where `m = |G|`. -/
noncomputable def localJoint {L : Type*} [MeasurableSpace L] (τ : Kernel G L) : Measure (G × L) :=
  (Fintype.card G : ℝ≥0∞)⁻¹ • ∑ s : G, (Measure.dirac s).prod (τ s)

/-- **Law of the secret and the global leakage** `(Z, X)` with `Z = S₀ + ⋯ + S_d` and
`X = (L₀, …, L_d)`, where the shares are independent and uniform on `G` and each `L_i` is drawn from the
channel `τ i` given `S_i` alone (§1.1, p. 3, §2.1, p. 5, and p. 27):
`m^{-(d+1)} ∑_{s : Fin (d+1) → G} δ_{s₀ + ⋯ + s_d} ⊗ (τ₀(s₀) ⊗ ⋯ ⊗ τ_d(s_d))`. -/
noncomputable def globalJoint {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)]
    (τ : ∀ i, Kernel G (L i)) (d : ℕ) : Measure (G × ∀ i : Fin (d + 1), L i) :=
  ((Fintype.card G : ℝ≥0∞)⁻¹) ^ (d + 1) •
    ∑ s : Fin (d + 1) → G,
      (Measure.dirac (∑ i, s i)).prod (Measure.pi fun i : Fin (d + 1) => τ i (s i))


/-- **Fourier mode of leakage** of a channel (Definition 1, p. 7): `λ(w) = E_L[|p̂_{S∣L}(w ∣ L)|²]`,
for the law of `(S, L)`. -/
noncomputable def fourierMode {L : Type*} [MeasurableSpace L] (τ : Kernel G L) (w : NontrivialChar G) : ℝ :=
  fourierEnergy (localJoint τ) w.1

/-- **Normalized Fourier leakage spectrum** of a channel (Theorem 1, p. 8):
`q(w) = λ(w) / ∑_{w' ≠ 0} λ(w')`, on the non-trivial characters. -/
noncomputable def spectrum {L : Type*} [MeasurableSpace L] (τ : Kernel G L) (w : NontrivialChar G) : ℝ :=
  fourierMode τ w / ∑ w', fourierMode τ w'

/-- **Spectral alignment factor** (Theorem 1, p. 8): `κ_d = Pr[W₀ = W₁ = ⋯ = W_d]` for independent
`W_i ∼ q_i`, where `q_i` is the normalized spectrum of `τ i`. -/
noncomputable def spectralAlignment {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)]
    (τ : ∀ i, Kernel G (L i)) (d : ℕ) : ℝ :=
  collisionProb fun i : Fin (d + 1) => spectrum (τ i)

/-- The function `f(r) = r ln r - r + 1` of Lemma 1, p. 9. `Real.log 0 = 0` gives `f(0) = 1`, the value
under the convention `0 ln 0 = 0`. -/
noncomputable def f (r : ℝ) : ℝ := r * Real.log r - r + 1

/-- The function `g(r) = (r - 1)² / f(r)` of Lemma 1, p. 9, with `g(1) := 2`. -/
noncomputable def g (r : ℝ) : ℝ :=
  open Classical in
  if r = 1 then 2 else (r - 1) ^ 2 / f r

/-- The **`D_KL`-weighted product measure** of Lemma 1, p. 9:
`μ(s, dl) = f(r(s, l)) / (ln(2) I(S; L)) · p_S(s) p_L(dl)`, for the law of `(S, L)` of the channel `τ`. -/
noncomputable def sharpnessMeasure {L : Type*} [MeasurableSpace L] (τ : Kernel G L) : Measure (G × L) :=
  ((localJoint τ).fst.prod (localJoint τ).snd).withDensity fun x =>
    ENNReal.ofReal (f (likelihoodRatio (localJoint τ) x.1 x.2) / (Real.log 2 * shannonMI (localJoint τ)))

/-- The **leakage sharpness** of a channel (Lemma 1, p. 9): `α = ln(2) E_μ g(r)`. -/
noncomputable def sharpness {L : Type*} [MeasurableSpace L] (τ : Kernel G L) : ℝ :=
  Real.log 2 * ∫ x, g (likelihoodRatio (localJoint τ) x.1 x.2) ∂(sharpnessMeasure τ)

/-- The **worst-case parameter** of Theorem 2, p. 10:
`ρ* = sup_i max_{w ≠ 0} ess sup_l |p̂_{S_i∣L_i}(w ∣ l)|`, computed in `[0, ∞]`, where suprema of every set
exist and the essential supremum is with respect to `p_{L_i}`. -/
noncomputable def rhoStar {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)] (τ : ∀ i, Kernel G (L i)) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ w : NontrivialChar G,
    essSup (fun l => ‖posteriorDFT (localJoint (τ i)) w.1 l‖ₑ) (localJoint (τ i)).snd

end Model

end LeakageSpectral.Shannon


