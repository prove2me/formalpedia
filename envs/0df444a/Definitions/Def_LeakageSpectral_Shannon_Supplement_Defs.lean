-- Prove2me | Definitions.Def_LeakageSpectral_Shannon_Supplement_Defs
-- name    : LeakageSpectral_Shannon_Supplement_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:36.532677+00:00
-- url     : https://prove2.me/theorems/0e96a2ce-c418-443b-9fc2-058b934d05a7
-- title:
--   Supplement definitions — min-entropy, order classes, quotient leakage, automorphism-weighted sharing
-- statement:
--   Objects used by the supplement's statements, on top of the base mission's definitions (χ²- and Shannon MI, the local and global joint laws, Fourier modes, the normalized spectrum $q$, the spectral alignment $\kappa_d$, the sharpness $\alpha$ and $\rho^*$).
--
--   1. **Min-entropy in bits** (Eq. (4), p. 12): $H_\infty(q)=-\log_2\max_w q(w)$ for a function $q$ on a finite set.
--   2. **Conjugate symmetry** (p. 11): $q(\bar w)=q(w)$ for every non-trivial character $w$, where $\chi_{\bar w}(s)=\chi_w(-s)$.
--   3. **Order classes** (p. 16): $\mathcal W_\gamma$, the non-trivial characters of order $\gamma$ in the character group; the **primitive spectral mass** $Q(\gamma)=\sum_{w\in\mathcal W_\gamma}q(w)$; the **conditional spectrum** $q_\gamma(w)=q(w)/Q(\gamma)$ on $\mathcal W_\gamma$ (used only where $Q(\gamma)>0$); the **within-class alignment** $\kappa_{d,\gamma}=\sum_{w\in\mathcal W_\gamma}q_\gamma(w)^{d+1}$ (p. 17).
--   4. **Quotient variable** (p. 18): for a character $\chi_w$, its kernel $\ker\chi_w=\{s:\chi_w(s)=1\}$, the joint law of $(Y^{(w)},L)$ with $Y^{(w)}=S+\ker\chi_w\in\mathbb G/\ker\chi_w$, and the **normalized quotient leakage** $I_{\chi^2}(Y^{(w)};L)/I_{\chi^2}(S;L)$.
--   5. **Automorphism-weighted sharing** (§5.3, p. 19): the law of $(Z,X)$ with $Z=\sum_i\varphi_i(S_i)$ for automorphisms $\varphi_i$ of $\mathbb G$, independent uniform shares and $L_i\sim\tau_i(S_i)$:
--   $$m^{-(d+1)}\sum_{s\in\mathbb G^{d+1}}\delta_{\sum_i\varphi_i(s_i)}\otimes\bigotimes_i\tau_i(s_i).$$
--   With every $\varphi_i$ the identity it is the base mission's global law.
--   6. **Full support** of a binary channel (pp. 11–12, 21): $p_{L\mid S}(l\mid s)>0$ for every $s$ and $l$.
--   7. **Permutation invariance** of a function $J$ of the channel (p. 14): $J(\tau\circ\pi)=J(\tau)$ for every channel $\tau$ and permutation $\pi$ of $\mathbb G$, where $(\tau\circ\pi)(s)=\tau(\pi(s))$.
--
--   **Formalization Note** The maximum in $H_\infty$ is a supremum over a finite type, nonempty in every use. The quotient $\mathbb G/\ker\chi_w$ is finite and carries the quotient σ-algebra, which is discrete.
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Eq. (4), p. 12; pp. 11–12, 14, 16–18; §5.3, p. 19

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
import Definitions.Def_LeakageSpectral_Shannon_JointLaw
import Definitions.Def_LeakageSpectral_Shannon_ShareModel
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeakageSpectral.Shannon.Supplement

open LeakageSpectral.Shannon

/-- **Min-entropy in bits** of a mass function `q` on a finite type (Ueno, STOC 2027 submission #326,
Eq. (4), p. 12): `H∞(q) = -log₂ max_w q(w)`. For the normalized spectrum of a channel the maximum is
a maximum of finitely many values and is positive. -/
noncomputable def minEntropy {ι : Type*} [Fintype ι] (q : ι → ℝ) : ℝ :=
  -Real.logb 2 (⨆ w, q w)

section General

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- **Conjugate symmetry** of a function on the non-trivial characters (p. 11):
`q(w̄) = q(w)`, where the conjugate character `w̄` is `s ↦ conj (χ_w s) = χ_w (-s)`. Stated for every
pair `w, w'` with `χ_{w'}(s) = χ_w(-s)` for all `s`, i.e. `w' = w̄`. -/
def IsConjSymm (q : NontrivialChar G → ℝ) : Prop :=
  ∀ w w' : NontrivialChar G, (∀ s, w'.1 s = w.1 (-s)) → q w' = q w

/-- The **order class** `𝒲_γ = {w ≠ 0 : ord χ_w = γ}` (p. 16): the non-trivial characters whose order,
in the group of characters, is `γ`. -/
abbrev OrderClass (G : Type*) [AddCommGroup G] [Fintype G] (γ : ℕ) : Type _ :=
  {w : NontrivialChar G // orderOf w.1 = γ}

variable [MeasurableSpace G]

/-- **Order-`γ` primitive spectral mass** (p. 16): `Q(γ) = ∑_{w ∈ 𝒲_γ} q(w)`, for the normalized
spectrum `q` of the channel `τ`. -/
noncomputable def primitiveMass {L : Type*} [MeasurableSpace L] (τ : Kernel G L) (γ : ℕ) : ℝ :=
  ∑ w : OrderClass G γ, spectrum τ w.1

/-- **Conditional spectrum** on the order class (Theorem 8, p. 16): `q_γ(w) = q(w) / Q(γ)` for
`w ∈ 𝒲_γ`. The source defines it for `Q(γ) > 0`; every statement uses it only there. -/
noncomputable def condSpectrum {L : Type*} [MeasurableSpace L] (τ : Kernel G L) (γ : ℕ)
    (w : OrderClass G γ) : ℝ :=
  spectrum τ w.1 / primitiveMass τ γ

/-- **Within-class alignment** (p. 17): `κ_{d,γ} = ∑_{w ∈ 𝒲_γ} q_γ(w)^{d+1}`. -/
noncomputable def classAlignment {L : Type*} [MeasurableSpace L] (τ : Kernel G L) (γ d : ℕ) : ℝ :=
  ∑ w : OrderClass G γ, condSpectrum τ γ w ^ (d + 1)

end General

section Quotient

variable {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]

/-- The kernel `ker χ_w = {s : χ_w(s) = 1}` of a character, as an additive subgroup of `G`
(§5, p. 16). -/
def charKer (w : AddChar G ℂ) : AddSubgroup G where
  carrier := {s | w s = 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change w (a + b) = 1
    rw [AddChar.map_add_eq_mul, show w a = 1 from ha, show w b = 1 from hb, one_mul]
  neg_mem' := by
    intro a ha
    change w (-a) = 1
    rw [AddChar.map_neg_eq_inv, show w a = 1 from ha, inv_one]

/-- **Joint law of the quotient variable and the leakage** (p. 18): the law of
`(Y^{(w)}, L)` with `Y^{(w)} = S + ker χ_w ∈ G ⧸ ker χ_w`, i.e. the push-forward of the law of
`(S, L)` under `(s, l) ↦ (s + ker χ_w, l)`. -/
noncomputable def quotientJoint {L : Type*} [MeasurableSpace L] (τ : Kernel G L) (w : AddChar G ℂ) :
    Measure ((G ⧸ charKer w) × L) :=
  (localJoint τ).map fun x => ((x.1 : G ⧸ charKer w), x.2)

/-- **Normalized quotient leakage** (Theorem 10, p. 18):
`R = I_χ²(Y^{(w)}; L) / I_χ²(S; L)`, for the character `w` (of order `γ = ord χ_w`). The quotient
`G ⧸ ker χ_w` is finite and carries the quotient σ-algebra. -/
noncomputable def quotientLeakage {L : Type*} [MeasurableSpace L] (τ : Kernel G L) (w : AddChar G ℂ) :
    ℝ :=
  open Classical in
  chiSquareMI (quotientJoint τ w) / chiSquareMI (localJoint τ)

/-- **Law of the secret and the global leakage under automorphism-weighted sharing** (§5.3, p. 19):
`Z = φ₀(S₀) + ⋯ + φ_d(S_d)` with independent uniform shares and each `L_i` drawn from `τ i` given `S_i`:
`m^{-(d+1)} ∑_{s : Fin (d+1) → G} δ_{φ₀(s₀) + ⋯ + φ_d(s_d)} ⊗ (τ₀(s₀) ⊗ ⋯ ⊗ τ_d(s_d))`.
With every `φ i` the identity it is the base `globalJoint`. -/
noncomputable def weightedGlobalJoint {L : ℕ → Type*} [∀ i, MeasurableSpace (L i)]
    (τ : ∀ i, Kernel G (L i)) {d : ℕ} (φ : Fin (d + 1) → (G ≃+ G)) :
    Measure (G × ∀ i : Fin (d + 1), L i) :=
  ((Fintype.card G : ℝ≥0∞)⁻¹) ^ (d + 1) •
    ∑ s : Fin (d + 1) → G,
      (Measure.dirac (∑ i, φ i (s i))).prod (Measure.pi fun i : Fin (d + 1) => τ i (s i))

end Quotient

section Channels

variable {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]

/-- A **full-support binary channel** (pp. 11–12, 14, 21): `p_{L∣S}(l ∣ s) ∈ (0, 1)`, i.e. every
leakage value has positive probability given every share value. -/
def FullSupport (τ : Kernel G Bool) : Prop :=
  ∀ s b, 0 < τ s {b}

/-- A **permutation-invariant local leakage magnitude** (p. 14): a function `J` of the channel that
takes the same value on `τ` and on `τ ∘ π`, `(τ ∘ π)(s) = τ(π s)`, for every channel `τ` and every
permutation `π` of `G` (channels related by an input permutation). -/
def IsPermInvariant [DiscreteMeasurableSpace G] {L : Type*} [MeasurableSpace L] {β : Sort*}
    (J : Kernel G L → β) : Prop :=
  ∀ (τ₀ : Kernel G L) (π : Equiv.Perm G), J (τ₀.comap π (Measurable.of_discrete)) = J τ₀

end Channels

end LeakageSpectral.Shannon.Supplement


