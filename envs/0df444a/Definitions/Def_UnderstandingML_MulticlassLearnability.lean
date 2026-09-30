-- Prove2me | Definitions.Def_UnderstandingML_MulticlassLearnability
-- name    : UnderstandingML_MulticlassLearnability
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:56:55.62599+00:00
-- url     : https://prove2.me/theorems/de970139-ff0f-4930-9d5a-c53428b1c85f
-- title:
--   Chapter 29: multiclass shattering and the Natarajan dimension (Definitions 29.1–29.2), multiclass PAC notions, One-versus-All and reduction classes, linear predictors (29.1), the ERMs of §29.4
-- statement:
--   Chapter 29 of Shalev-Shwartz and Ben-David. **Definition 29.1.** `NShatters H C` says $C$ is shattered by $H \subseteq [k]^X$: there are $f_0, f_1$ with $f_0(x) \ne f_1(x)$ on $C$ such that for every $B \subseteq C$ some $h \in H$ agrees with $f_0$ on $B$ and with $f_1$ on $C \setminus B$. **Definition 29.2.** `ndim H` is the Natarajan dimension, the maximal size of a shattered set. `lossMulti` is the multiclass 0–1 loss; `NPointwiseSeparable` is the countable-approximation property of Remark 3.1; `IsMulticlassPACWith H A mH` is realizable PAC learnability of a multiclass class (Definition 3.1 with $D(\{h \ne f\})$ as the error). **§29.3:** `ovaPredict hbar` is $T(\bar h)(x) = \operatorname{argmax}_i h_i(x)$ with the smaller label on ties and `ovaClass Hbin k` is $H^{OvA,k}_{bin}$; `reductionClass Hbin l r` is $H^r_{bin} = \{x \mapsto r(h_1(x), \dots, h_l(x))\}$; `argmaxMin Ψ w` is $x \mapsto \operatorname{argmax}_i\langle w, \Psi(x,i)\rangle$ (smallest label on ties) and `linearMulticlassClass Ψ` is $H_\Psi$ (29.1). **§29.4:** `CofinLabel X` is $P_f(X) \cup \{\ast\}$, `hSet A` is $h_A$, `cofinClass X` is $H = \{h_A\}$, `IsGoodERM A` / `IsBadERM A` say $A$ is an ERM for $H$ returning $h_\emptyset$, respectively $h_{\{x_1, \dots, x_m\}^c}$, on all-$\ast$ samples, and `badDist x₀ ε` is the distribution $P[x_0] = 1 - 2\epsilon$, $P[x_i] = 2\epsilon/(d-1)$ of the proof of Claim 29.9.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.1 p. 403 (Definitions 29.1-29.2), §29.3 pp. 404-405 (One-versus-All, reductions, Equation (29.1)), §29.4 p. 407 (P_f(X), h_A, H, A_good, A_bad) and p. 408 (the distribution of the proof of Claim 29.9)

import Definitions.Def_UnderstandingML_Linear
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 29: multiclass
# learnability

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.1–§29.4.

**Natarajan dimension (Definitions 29.1–29.2, p. 403).** `C ⊆ X` is shattered by a class `H` of
functions `X → [k]` if there are `f₀, f₁ : C → [k]` with `f₀(x) ≠ f₁(x)` for every `x ∈ C` such
that for every `B ⊆ C` some `h ∈ H` agrees with `f₀` on `B` and with `f₁` on `C \ B`;
`Ndim(H)` is the maximal size of a shattered set.

**Multiclass-to-binary reductions (§29.3.1–§29.3.2, pp. 404–405).** For a binary class
`H_bin` and `h̄ = (h₁, …, h_k) ∈ (H_bin)^k`, One-versus-All predicts
`T(h̄)(x) = argmaxᵢ hᵢ(x)`, the smaller label on ties; a general reduction with `l` binary
classifiers and a rule `r : {0,1}^l → [k]` predicts `R(h̄)(x) = r(h₁(x), …, h_l(x))`.

**Linear multiclass predictors (29.1, p. 405).** `H_Ψ = {x ↦ argmaxᵢ ⟨w, Ψ(x, i)⟩ : w ∈ ℝ^d}`.

**Good and bad ERMs (§29.4, p. 407).** `P_f(X)` is the collection of finite and cofinite
subsets of `X`, the label set is `P_f(X) ∪ {∗}`, `h_A(x) = A` if `x ∈ A` and `∗` otherwise, and
`H = {h_A : A ∈ P_f(X)}`. `A_good` returns `h_∅` on an all-`∗` sample; `A_bad` returns
`h_{{x₁, …, x_m}ᶜ}`.

**Conventions.** Labels are an arbitrary finite type `Y` (`k = |Y|`); the multiclass 0–1 loss
is `lossMulti`. Argmax predictors break ties towards the smallest label (the book's rule for
One-versus-All; for `H_Ψ` some fixed rule is needed, since with arbitrary tie-breaking every
function is an argmax predictor of the zero mapping). `ℕ`-valued "sample complexities" are
the functions of Chapter 2; the multiclass realizable PAC property mirrors Definition 3.1 with
`D({x : h(x) ≠ f(x)})` in place of the binary true error. The countable-approximation
property of Chapter 6 (Remark 3.1) is restated for multiclass classes.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-! ### The Natarajan dimension and the multiclass learning notions -/

section Natarajan

variable {X Y : Type*}

/-- **Definition 29.1 (Shattering, multiclass version).** `C` is shattered by `H` if there are
`f₀, f₁` with `f₀(x) ≠ f₁(x)` on `C` such that for every `B ⊆ C` some `h ∈ H` agrees with `f₀`
on `B` and with `f₁` on `C \ B`. -/
def NShatters (H : Set (X → Y)) (C : Finset X) : Prop :=
  ∃ f₀ f₁ : X → Y, (∀ x ∈ C, f₀ x ≠ f₁ x) ∧
    ∀ B ⊆ C, ∃ h ∈ H, (∀ x ∈ B, h x = f₀ x) ∧ ∀ x ∈ C, x ∉ B → h x = f₁ x

/-- **Definition 29.2.** The **Natarajan dimension** `Ndim(H)`: the maximal size of a shattered
set. -/
noncomputable def ndim (H : Set (X → Y)) : ℕ∞ :=
  ⨆ (C : Finset X) (_ : NShatters H C), (C.card : ℕ∞)

open Classical in
/-- The multiclass 0–1 loss `ℓ(h, (x, y)) = 𝟙[h(x) ≠ y]`. -/
noncomputable def lossMulti (h : X → Y) (z : X × Y) : ℝ := if h z.1 = z.2 then 0 else 1

/-- The countable-approximation property of Remark 3.1 for a multiclass class (as
`PointwiseSeparable` in Chapter 6): a countable subclass approximates every member pointwise. -/
def NPointwiseSeparable (H : Set (X → Y)) : Prop :=
  ∃ H₀ ⊆ H, H₀.Countable ∧ ∀ h ∈ H, ∃ u : ℕ → (X → Y), (∀ n, u n ∈ H₀) ∧
    ∀ x, ∃ N, ∀ n, N ≤ n → u n x = h x

/-- **Multiclass PAC learnability (realizable case)** with sample complexity `mH` and algorithm
`A`, mirroring Definition 3.1: for every `ε, δ ∈ (0,1)`, every distribution `D` over `X` and
every measurable labeling `f` realized by `H` (`D({h ≠ f}) = 0` for some `h ∈ H`), running `A` on
`m ≥ mH(ε, δ)` examples labeled by `f` returns `h` with `D({h ≠ f}) > ε` with probability at
most `δ`. -/
def IsMulticlassPACWith [MeasurableSpace X] [MeasurableSpace Y] (H : Set (X → Y))
    (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ D : Measure X, IsProbabilityMeasure D →
    ∀ f : X → Y, Measurable f → (∃ h ∈ H, D {x | h x ≠ f x} = 0) → ∀ m : ℕ, mH ε δ ≤ m →
      iidLaw (D.map (fun x ↦ (x, f x))) m {S | ENNReal.ofReal ε < D {x | A m S x ≠ f x}} ≤
        ENNReal.ofReal δ

end Natarajan

/-! ### Reductions to binary classes and linear multiclass predictors -/

section Reductions

variable {X : Type*}

open Classical in
/-- **One-versus-All** (p. 404): `T(h̄)(x) = argmaxᵢ hᵢ(x)`, the smallest label `i` with
`hᵢ(x) = 1`, and the smallest label of all when no `hᵢ(x)` is `1`. -/
noncomputable def ovaPredict {k : ℕ} [NeZero k] (hbar : Fin k → X → Bool) (x : X) : Fin k :=
  if h : (Finset.univ.filter (fun i ↦ hbar i x = true)).Nonempty then
    (Finset.univ.filter (fun i ↦ hbar i x = true)).min' h else 0

/-- The One-versus-All class `H^{OvA,k}_bin = {T(h̄) : h̄ ∈ (H_bin)^k}` (p. 404). -/
def ovaClass (Hbin : Set (X → Bool)) (k : ℕ) [NeZero k] : Set (X → Fin k) :=
  {h | ∃ hbar : Fin k → X → Bool, (∀ i, hbar i ∈ Hbin) ∧ h = ovaPredict hbar}

/-- The class `H^r_bin = {R(h̄) : h̄ ∈ (H_bin)^l}` of a general multiclass-to-binary reduction
with rule `r` (p. 405). -/
def reductionClass {Y : Type*} (Hbin : Set (X → Bool)) (l : ℕ) (r : (Fin l → Bool) → Y) :
    Set (X → Y) :=
  {h | ∃ hbar : Fin l → X → Bool, (∀ i, hbar i ∈ Hbin) ∧ h = fun x ↦ r (fun i ↦ hbar i x)}

open Classical in
/-- `argmaxᵢ ⟨w, Ψ(x, i)⟩` with ties broken towards the smallest label. -/
noncomputable def argmaxMin {d k : ℕ} [NeZero k] (Ψ : X → Fin k → Vec d) (w : Vec d) (x : X) :
    Fin k :=
  if h : (Finset.univ.filter (fun i ↦ ∀ j, ⟪w, Ψ x j⟫_ℝ ≤ ⟪w, Ψ x i⟫_ℝ)).Nonempty then
    (Finset.univ.filter (fun i ↦ ∀ j, ⟪w, Ψ x j⟫_ℝ ≤ ⟪w, Ψ x i⟫_ℝ)).min' h else 0

/-- The class of **linear multiclass predictors** `H_Ψ = {x ↦ argmaxᵢ ⟨w, Ψ(x, i)⟩ : w ∈ ℝ^d}`
(29.1). -/
def linearMulticlassClass {d k : ℕ} [NeZero k] (Ψ : X → Fin k → Vec d) : Set (X → Fin k) :=
  {h | ∃ w : Vec d, h = argmaxMin Ψ w}

end Reductions

/-! ### The class of §29.4 and its two ERMs -/

section GoodBad

variable {X : Type*}

/-- The label set `P_f(X) ∪ {∗}` of §29.4: `some A` for a finite or cofinite `A ⊆ X`, `none` for
`∗`. -/
abbrev CofinLabel (X : Type*) := Option {A : Set X // A.Finite ∨ Aᶜ.Finite}

instance : MeasurableSpace (CofinLabel X) := ⊤

open Classical in
/-- `h_A(x) = A` if `x ∈ A`, `∗` otherwise (p. 407). -/
noncomputable def hSet (A : {A : Set X // A.Finite ∨ Aᶜ.Finite}) : X → CofinLabel X :=
  fun x ↦ if x ∈ A.1 then some A else none

/-- The class `H = {h_A : A ∈ P_f(X)}` (p. 407). -/
def cofinClass (X : Type*) : Set (X → CofinLabel X) := Set.range (hSet (X := X))

/-- `A` is the ERM `A_good` (p. 407): an ERM for `H` that returns `h_∅` on every all-`∗` sample. -/
def IsGoodERM (A : Learner (X × CofinLabel X) (X → CofinLabel X)) : Prop :=
  IsERMLearner lossMulti (cofinClass X) A ∧
    ∀ (m : ℕ) (S : Fin m → X × CofinLabel X), (∀ i, (S i).2 = none) →
      A m S = hSet ⟨∅, Or.inl Set.finite_empty⟩

/-- `A` is the ERM `A_bad` (p. 407): an ERM for `H` that returns `h_{{x₁, …, x_m}ᶜ}` on every
all-`∗` sample `(x₁, ∗), …, (x_m, ∗)`. -/
def IsBadERM (A : Learner (X × CofinLabel X) (X → CofinLabel X)) : Prop :=
  IsERMLearner lossMulti (cofinClass X) A ∧
    ∀ (m : ℕ) (S : Fin m → X × CofinLabel X), (∀ i, (S i).2 = none) →
      A m S = hSet ⟨(Set.range (fun i ↦ (S i).1))ᶜ,
        Or.inr (by rw [compl_compl]; exact Set.finite_range _)⟩

open Classical in
/-- The distribution of the proof of Claim 29.9(2) (p. 408): `P[x₀] = 1 − 2ε` and
`P[x] = 2ε/(d − 1)` for the `d − 1` other points. -/
noncomputable def badDist [MeasurableSpace X] [Fintype X] (x₀ : X) (ε : ℝ) : Measure X :=
  ENNReal.ofReal (1 - 2 * ε) • Measure.dirac x₀ +
    ENNReal.ofReal (2 * ε / (Fintype.card X - 1)) • ∑ x ∈ Finset.univ.erase x₀, Measure.dirac x

end GoodBad

end UnderstandingML


