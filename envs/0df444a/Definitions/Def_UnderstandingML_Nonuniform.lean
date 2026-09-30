-- Prove2me | Definitions.Def_UnderstandingML_Nonuniform
-- name    : UnderstandingML_Nonuniform
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:46:11.653988+00:00
-- url     : https://prove2.me/theorems/f88f0386-d9e8-4219-bd77-8dd2b19807ba
-- title:
--   Chapter 7: nonuniform learnability (Def. 7.1), the rates εₙ and n(h), the SRM rule and its δ-indexed learners, prefix-free description languages and the MDL rule, shattering an infinite set
-- statement:
--   Chapter 7 of Shalev-Shwartz and Ben-David. **Definition 7.1:** $H$ is nonuniformly learnable if there are a learning algorithm $A$ and $m^{NUL}_H : (0,1)^2 \times H \to \mathbb{N}$ such that for every $\epsilon, \delta \in (0,1)$ and $h \in H$, if $m \ge m^{NUL}_H(\epsilon,\delta,h)$ then for every distribution $D$, with probability at least $1-\delta$ over $S \sim D^m$, $L_D(A(S)) \le L_D(h) + \epsilon$ (`IsNonuniformLearnerWith`, `NonuniformLearnable`; as in Definition 3.4 the outputs lie in $H$; `IsNonuniformFamilyWith` is the same for a family of learners indexed by $\delta$). **SRM (§7.2):** for $H = \bigcup_n H_n$ with uniform-convergence rates $m^{UC}_{H_n}$, $\epsilon_n(m,\delta) = \min\{\epsilon \in (0,1) : m^{UC}_{H_n}(\epsilon,\delta) \le m\}$ (7.1, `epsRate`, an infimum, meaningful when the set is nonempty, `RateDefined`), $n(h) = \min\{n : h \in H_n\}$ (7.4, `firstIndex`), and the SRM rule returns $h \in \operatorname{argmin}_{h \in H}[L_S(h) + \epsilon_{n(h)}(m, w(n(h))\delta)]$ over the admissible hypotheses (`Admissible`, `srmObjective`, `IsSRM`, `IsSRMFamily`); `srmWeight n = 6/(\pi^2 n^2)`. **MDL (§7.3):** a description language $d : H \to \{0,1\}^*$ is prefix-free if for distinct $h, h'$ the string $d(h)$ is not a prefix of $d(h')$ (`PrefixFreeOn`); the MDL rule returns $h \in \operatorname{argmin}_{h \in H}[L_S(h) + \sqrt{(|h| + \ln(2/\delta))/(2m)}]$ (`mdlObjective`, `IsMDL`). `ShattersSet H K`: every labeling of the (possibly infinite) set $K$ is the restriction of a member of $H$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.1 Definition 7.1 (p. 84), §7.2 Equations (7.1), (7.4) and the SRM rule (pp. 86-87), §7.3 description languages and the MDL rule (pp. 89-90), Exercise 7.5 (p. 98)

import Definitions.Def_UnderstandingML_VC

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 7:
# nonuniform learnability, structural risk minimization and minimum description length

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.1–§7.3.

**Nonuniform learnability (Definition 7.1).** `H` is nonuniformly learnable if there are a
learning algorithm `A` and a function `m^{NUL}_H : (0,1)² × H → ℕ` such that for every
`ε, δ ∈ (0,1)` and every `h ∈ H`, if `m ≥ m^{NUL}_H(ε, δ, h)` then for every distribution `D`,
with probability at least `1 − δ` over `S ∼ D^m`, `L_D(A(S)) ≤ L_D(h) + ε`.

**Structural risk minimization (§7.2).** For `H = ⋃ₙ Hₙ` with each `Hₙ` uniformly convergent
with rate `m^{UC}_{Hₙ}`, `εₙ(m, δ) = min{ε ∈ (0,1) : m^{UC}_{Hₙ}(ε, δ) ≤ m}` (7.1),
`n(h) = min{n : h ∈ Hₙ}` (7.4), and for a weight function `w : ℕ → [0,1]` with `∑ w(n) ≤ 1`
the SRM rule returns `h ∈ argmin_{h ∈ H} [L_S(h) + ε_{n(h)}(m, w(n(h))·δ)]`.

**Description languages (§7.3).** A description language `d : H → {0,1}*` is prefix-free if
for distinct `h, h'` the string `d(h)` is not a prefix of `d(h')`; `|h|` is the length of `d(h)`,
and the MDL rule returns `h ∈ argmin_{h ∈ H} [L_S(h) + √((|h| + ln(2/δ))/(2m))]`.

**Conventions.** As in Definition 3.4, the learner's outputs are required to lie in `H`
(the SRM and MDL rules do so; for the 0–1 loss this is what keeps the Bochner integral `risk`
honest). The book's `εₙ` is the infimum `epsRate` of a set that may be empty for small `m`;
a hypothesis is *admissible* for SRM when that set is nonempty at its index, and the SRM rule
minimizes over admissible hypotheses. The SRM rule takes the confidence `δ` as an input, so
"the SRM algorithm" is a family of learners indexed by `δ`; `IsNonuniformFamilyWith` is
Definition 7.1 for such a family. Weight functions are indexed by `ℕ`, with `w(0)` allowed to
be `0` so that the book's `n ∈ {1, 2, …}` is the case `H₀ = ∅`.
-/

open MeasureTheory

namespace UnderstandingML

section Nonuniform

variable {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}

/-- **Definition 7.1** with the algorithm `A` and the function `mNUL` explicit: `A` returns
hypotheses in `H`, and for every `ε, δ ∈ (0,1)`, every `h ∈ H`, every distribution `D` and every
`m ≥ mNUL(ε, δ, h)`, the probability that `L_D(A(S)) > L_D(h) + ε` is at most `δ`. -/
def IsNonuniformLearnerWith (loss : Hyp → Z → ℝ) (H : Set Hyp) (A : Learner Z Hyp)
    (mNUL : ℝ → ℝ → Hyp → ℕ) : Prop :=
  (∀ (m : ℕ) (S : Fin m → Z), A m S ∈ H) ∧
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ h ∈ H, ∀ D : Measure Z, IsProbabilityMeasure D →
    ∀ m : ℕ, mNUL ε δ h ≤ m →
      iidLaw D m {S | risk loss D h + ε < risk loss D (A m S)} ≤ ENNReal.ofReal δ

/-- `H` is **nonuniformly learnable** (Definition 7.1). -/
def NonuniformLearnable (loss : Hyp → Z → ℝ) (H : Set Hyp) : Prop :=
  ∃ (A : Learner Z Hyp) (mNUL : ℝ → ℝ → Hyp → ℕ), IsNonuniformLearnerWith loss H A mNUL

/-- Definition 7.1 for a family of learners `A δ` indexed by the confidence parameter (the SRM
and MDL rules take `δ` as an input): outputs in `H`, and for `m ≥ mNUL(ε, δ, h)` the learner
`A δ` satisfies `L_D(A δ (S)) ≤ L_D(h) + ε` with probability at least `1 − δ`. -/
def IsNonuniformFamilyWith (loss : Hyp → Z → ℝ) (H : Set Hyp) (A : ℝ → Learner Z Hyp)
    (mNUL : ℝ → ℝ → Hyp → ℕ) : Prop :=
  (∀ (δ : ℝ) (m : ℕ) (S : Fin m → Z), A δ m S ∈ H) ∧
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ h ∈ H, ∀ D : Measure Z, IsProbabilityMeasure D →
    ∀ m : ℕ, mNUL ε δ h ≤ m →
      iidLaw D m {S | risk loss D h + ε < risk loss D (A δ m S)} ≤ ENNReal.ofReal δ

/-- The set `{ε ∈ (0,1) : m^{UC}(ε, δ) ≤ m}` of Equation (7.1) is nonempty. -/
def RateDefined (mUC : ℝ → ℝ → ℕ) (m : ℕ) (δ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ mUC ε δ ≤ m

/-- **Equation (7.1)**: `εₙ(m, δ) = min{ε ∈ (0,1) : m^{UC}_{Hₙ}(ε, δ) ≤ m}`, as an infimum
(meaningful when `RateDefined`). -/
noncomputable def epsRate (mUC : ℝ → ℝ → ℕ) (m : ℕ) (δ : ℝ) : ℝ :=
  sInf {ε : ℝ | 0 < ε ∧ ε < 1 ∧ mUC ε δ ≤ m}

/-- **Equation (7.4)**: `n(h) = min{n : h ∈ Hₙ}`. -/
noncomputable def firstIndex (Hn : ℕ → Set Hyp) (h : Hyp) : ℕ :=
  sInf {n | h ∈ Hn n}

/-- `h` is **admissible** for SRM at sample size `m` and confidence `δ`: it lies in `⋃ₙ Hₙ`, its
index has positive weight, and `ε_{n(h)}(m, w(n(h))·δ)` is defined. -/
def Admissible (Hn : ℕ → Set Hyp) (mUC : ℕ → ℝ → ℝ → ℕ) (w : ℕ → ℝ) (δ : ℝ) (m : ℕ)
    (h : Hyp) : Prop :=
  h ∈ ⋃ n, Hn n ∧ 0 < w (firstIndex Hn h) ∧
    RateDefined (mUC (firstIndex Hn h)) m (w (firstIndex Hn h) * δ)

/-- The SRM objective `L_S(h) + ε_{n(h)}(m, w(n(h))·δ)`. -/
noncomputable def srmObjective (loss : Hyp → Z → ℝ) (Hn : ℕ → Set Hyp)
    (mUC : ℕ → ℝ → ℝ → ℕ) (w : ℕ → ℝ) (δ : ℝ) {m : ℕ} (S : Fin m → Z) (h : Hyp) : ℝ :=
  empRisk loss S h + epsRate (mUC (firstIndex Hn h)) m (w (firstIndex Hn h) * δ)

/-- **The SRM rule** (§7.2): `h` is an SRM hypothesis for `S` at confidence `δ` if it is
admissible and minimizes the SRM objective over the admissible hypotheses. -/
def IsSRM (loss : Hyp → Z → ℝ) (Hn : ℕ → Set Hyp) (mUC : ℕ → ℝ → ℝ → ℕ) (w : ℕ → ℝ)
    (δ : ℝ) {m : ℕ} (S : Fin m → Z) (h : Hyp) : Prop :=
  Admissible Hn mUC w δ m h ∧
    ∀ h', Admissible Hn mUC w δ m h' → srmObjective loss Hn mUC w δ S h ≤
      srmObjective loss Hn mUC w δ S h'

/-- `A` implements the SRM rule: it returns hypotheses in `⋃ₙ Hₙ`, and whenever some hypothesis
is admissible for `(δ, m)` with `δ ∈ (0,1)` it returns an SRM hypothesis (the book's
`argmin`, assumed to be attained). -/
def IsSRMFamily (loss : Hyp → Z → ℝ) (Hn : ℕ → Set Hyp) (mUC : ℕ → ℝ → ℝ → ℕ) (w : ℕ → ℝ)
    (A : ℝ → Learner Z Hyp) : Prop :=
  (∀ (δ : ℝ) (m : ℕ) (S : Fin m → Z), A δ m S ∈ ⋃ n, Hn n) ∧
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (m : ℕ) (S : Fin m → Z),
    (∃ h, Admissible Hn mUC w δ m h) → IsSRM loss Hn mUC w δ S (A δ m S)

/-- The weight function `w(n) = 6/(π² n²)` of Theorem 7.5 (`w(0) = 0`). -/
noncomputable def srmWeight (n : ℕ) : ℝ := 6 / (Real.pi ^ 2 * n ^ 2)

end Nonuniform

/-! ### Description languages and the MDL rule (§7.3) -/

section MDL

variable {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}

/-- `d` is a **prefix-free description language** for `H` over `{0,1}` (§7.3): for distinct
`h, h' ∈ H`, `d(h)` is not a prefix of `d(h')`. -/
def PrefixFreeOn (H : Set Hyp) (d : Hyp → List Bool) : Prop :=
  ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ¬ (d h <+: d h')

/-- The MDL objective `L_S(h) + √((|h| + ln(2/δ))/(2m))` with `|h|` the length of `d(h)`. -/
noncomputable def mdlObjective (loss : Hyp → Z → ℝ) (d : Hyp → List Bool) (δ : ℝ) {m : ℕ}
    (S : Fin m → Z) (h : Hyp) : ℝ :=
  empRisk loss S h + Real.sqrt (((d h).length + Real.log (2 / δ)) / (2 * m))

/-- **The MDL rule** (§7.3): `h ∈ argmin_{h ∈ H} [L_S(h) + √((|h| + ln(2/δ))/(2m))]`. -/
def IsMDL (loss : Hyp → Z → ℝ) (H : Set Hyp) (d : Hyp → List Bool) (δ : ℝ) {m : ℕ}
    (S : Fin m → Z) (h : Hyp) : Prop :=
  h ∈ H ∧ ∀ h' ∈ H, mdlObjective loss d δ S h ≤ mdlObjective loss d δ S h'

end MDL

/-! ### Shattering an infinite set (Exercise 7.5) -/

section Infinite

variable {X : Type*}

/-- `H` shatters the (possibly infinite) set `K`: every labeling of `K` is the restriction of a
member of `H` (for finite `K` this is Definition 6.3). -/
def ShattersSet (H : Set (X → Bool)) (K : Set X) : Prop :=
  ∀ g : K → Bool, ∃ h ∈ H, ∀ x : K, h x = g x

end Infinite

end UnderstandingML


