-- Prove2me | Definitions.Def_OODLearnable_Basic
-- name    : OODLearnable_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T19:23:31.208487+00:00
-- url     : https://prove2.me/theorems/9e22be5f-5adc-4dd9-aef3-6ca1bd2b3b82
-- title:
--   Domains, risks, learnability and conditions for OOD detection (Fang et al. 2022)
-- statement:
--   Objects of Sections 2-5 and Appendices D-J of Fang, Li, Lu, Dong, Han and Liu (NeurIPS 2022).
--
--   1. **Spaces and loss.** The feature space is a set $\mathcal X\subseteq\mathbb R^d$ with its Borel $\sigma$-algebra and subspace topology. The ID labels are $\mathcal Y=\{1,\dots,K\}$, all OOD data carry the label $K+1$, and $\mathcal Y_{\rm all}=\mathcal Y\cup\{K+1\}$. A loss is $\ell:\mathcal Y_{\rm all}\times\mathcal Y_{\rm all}\to\mathbb R_{\ge0}$ with $\ell(y_1,y_2)=0$ if and only if $y_1=y_2$. A hypothesis space is a set $\mathcal H$ of functions $\mathcal X\to\mathcal Y_{\rm all}$.
--   2. **Domains.** A domain $D_{XY}=(1-\pi^{\rm out})D_{X_{\rm I}Y_{\rm I}}+\pi^{\rm out}D_{X_{\rm O}Y_{\rm O}}$ is given by a probability measure $D_{X_{\rm I}Y_{\rm I}}$ on $\mathcal X\times\mathcal Y$, a probability measure $D_{X_{\rm O}}$ on $\mathcal X$ and a class prior $\pi^{\rm out}\in[0,1)$. $D_{X_{\rm I}}$ is the $\mathcal X$-marginal of $D_{X_{\rm I}Y_{\rm I}}$, and $D^\alpha_{XY}$ is the same domain with prior $\alpha\in[0,1)$.
--   3. **Risks.** $R^{\rm in}_D(h)=\mathbb E_{(x,y)\sim D_{X_{\rm I}Y_{\rm I}}}\ell(h(x),y)$, $R^{\rm out}_D(h)=\mathbb E_{x\sim D_{X_{\rm O}}}\ell(h(x),K+1)$, $R^\alpha_D(h)=(1-\alpha)R^{\rm in}_D(h)+\alpha R^{\rm out}_D(h)$ for $\alpha\in[0,1]$, and $R_D(h)=R^{\pi^{\rm out}}_D(h)$ (eq. 1).
--   4. **Learnability (Definitions 1-2).** An algorithm maps every sample $S\in(\mathcal X\times\mathcal Y)^n$, $n\ge1$, to an element of $\mathcal H$. OOD detection is *learnable* in a domain space $\mathscr D$ for $\mathcal H$ if there are an algorithm $\mathbf A$ and a non-increasing sequence $\epsilon(n)\to0$ with
--   $$\mathbb E_{S\sim D^n_{X_{\rm I}Y_{\rm I}}}R_D(\mathbf A(S))\le\inf_{h\in\mathcal H}R_D(h)+\epsilon(n)\qquad\text{for all }D\in\mathscr D,\ n\ge1.$$
--   It is *strongly learnable* if the same holds with $R^\alpha_D$ in place of $R_D$ for every $\alpha\in[0,1]$, with one algorithm and one sequence. Learnability *at rate* $r$ means that in addition $\epsilon(n)\le C\,r(n)$ for some constant $C$.
--   5. **Domain spaces.** $\mathscr D$ is *priori-unknown* if $D^\alpha_{XY}\in\mathscr D$ whenever $D_{XY}\in\mathscr D$ and $\alpha\in[0,1)$ (Definition 3). For any $\mathscr D$, $\mathscr D'=\{D^\alpha_{XY}:D_{XY}\in\mathscr D,\alpha\in[0,1)\}$. The single-distribution space of $D_{XY}$ is $\{D^\alpha_{XY}:\alpha\in[0,1)\}$, the total space consists of all domains, the separate space $\mathscr D^s$ of all domains with $\operatorname{supp}D_{X_{\rm O}}\cap\operatorname{supp}D_{X_{\rm I}}=\emptyset$, and a finite-ID-distribution space is a priori-unknown space containing only finitely many distinct $D_{X_{\rm I}Y_{\rm I}}$.
--   6. **Conditions.** *Condition 1 (linear condition):* $\inf_{h\in\mathcal H}R^\alpha_D(h)=(1-\alpha)\inf_{h\in\mathcal H}R^{\rm in}_D(h)+\alpha\inf_{h\in\mathcal H}R^{\rm out}_D(h)$ for every $D\in\mathscr D$ and $\alpha\in[0,1)$. *Condition 2:* $\ell(y_2,y_1)\le\ell(K+1,y_1)$ for all $y_1,y_2\in\mathcal Y$. *Condition 3 (compatibility):* for every $D'\in\mathscr D$ and $\epsilon>0$ some $h_\epsilon\in\mathcal H$ satisfies $R^{\rm out}_D(h_\epsilon)\le\inf_{h\in\mathcal H}R^{\rm out}_D(h)+\epsilon$ and $R^{\rm in}_D(h_\epsilon)\le\inf_{h\in\mathcal H}R^{\rm in}_D(h)+\epsilon$ for every $D\in\mathscr D$ with $D_{X_{\rm I}Y_{\rm I}}=D'_{X_{\rm I}Y_{\rm I}}$ (Definition 5: such $D,D'$ are ID-consistent).
--   7. **Overlap (Definition 4).** $D_{XY}$ has overlap if some $\sigma$-finite measure $\tilde\mu$ with $D_{X_{\rm I}},D_{X_{\rm O}}\ll\tilde\mu$ gives positive mass to $\{x:f_{\rm I}(x)>0,\ f_{\rm O}(x)>0\}$, where $f_{\rm I},f_{\rm O}$ are the Radon-Nikodym derivatives of $D_{X_{\rm I}},D_{X_{\rm O}}$ with respect to $\tilde\mu$.
--   8. **Assumption 1 and VC dimension.** $\mathcal H$ is *separate for OOD* if every $x\in\mathcal X$ has some $h_x\in\mathcal H$ with $h_x(x)=K+1$. $\phi$ maps ID labels to $1$ and $K+1$ to $2$, $\phi\circ\mathcal H=\{\phi\circ h:h\in\mathcal H\}$, and ${\rm VCdim}$ is the largest size of a finite set on which a binary class realises every labelling ($\infty$ if unbounded).
--   9. **Finite discrete domains and $\mathcal H^{\rm in}\bullet\mathcal H^{\rm b}$.** A domain is finite discrete if $D_{X_{\rm I}Y_{\rm I}}$ and $D_{X_{\rm O}}$ are concentrated on finite sets. For $\mathcal H^{\rm in}\subseteq\{\mathcal X\to\mathcal Y\}$ and $\mathcal H^{\rm b}\subseteq\{\mathcal X\to\{1,2\}\}$, $\mathcal H^{\rm in}\bullet\mathcal H^{\rm b}$ consists of the $h$ with $h(x)=h^{\rm in}(x)$ if $h^{\rm b}(x)=1$ and $h(x)=K+1$ otherwise, for some $h^{\rm in}\in\mathcal H^{\rm in}$, $h^{\rm b}\in\mathcal H^{\rm b}$ (eq. 4).
--
--   **Formalization Note** The ID label $i\in\{1,\dots,K\}$ is `Fin.castSucc (i-1)` in `Fin (K+1)` and the OOD label is `Fin.last K`; the binary labels $1,2$ are $0,1$ in `Fin 2`. A domain is stored as the triple $(D_{X_{\rm I}Y_{\rm I}},D_{X_{\rm O}},\pi^{\rm out})$, because $R^{\rm out}_D$ and $D^\alpha_{XY}$ depend on $D_{X_{\rm O}}$ even when $\pi^{\rm out}=0$. Risks take values in $[0,\infty]$ (they are finite because $\ell$ is bounded and the measures are probability measures). In Definitions 1-2 the map $S\mapsto R_D(\mathbf A(S))$ (resp. $R^\alpha_D(\mathbf A(S))$) is required to be almost-everywhere measurable, so that the expectation is defined. Supports are topological supports in $\mathcal X$. All infima are taken in $[0,\infty]$.
-- source:
--   Fang, Li, Lu, Dong, Han and Liu, Is Out-of-Distribution Detection Learnable?, NeurIPS 2022, arXiv:2210.14707v3, Section 2 (Definitions 1-2, eqs. (1)-(3)), Section 3 (Definition 3, domain spaces), Section 4 (Condition 1, Definition 4, Assumption 1), Section 5 (eq. (4), Condition 2, Definition 5, Condition 3), Appendix H (Lemma 4), pp. 2-7, 33

import Mathlib

/-!
Fang, Li, Lu, Dong, Han and Liu, *Is Out-of-Distribution Detection Learnable?*, NeurIPS 2022,
arXiv:2210.14707v3: domains, risks, learnability, domain spaces, conditions and assumptions of
Sections 2-5 and Appendices D-J.

Conventions. The feature space is a measurable space `X` (in every statement, a subset of
`ℝ^d` with its Borel structure). The label space `𝒴_all = {1, …, K+1}` is `Fin (K + 1)`: the
in-distribution (ID) label `i ∈ {1, …, K}` is `Fin.castSucc (i - 1)` and the out-of-distribution
(OOD) label `K + 1` is `Fin.last K`. ID samples are labelled by `Fin K`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace OODLearnable

variable {X : Type*} [MeasurableSpace X] {K : ℕ}

/-- Section 2, "Loss and Risks": a loss `ℓ : 𝒴_all × 𝒴_all → ℝ_{≥0}` with `ℓ(y₁, y₂) = 0` if and
only if `y₁ = y₂`. -/
def IsOODLoss (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) : Prop :=
  ∀ y₁ y₂, ℓ y₁ y₂ = 0 ↔ y₁ = y₂

/-- Section 2: a domain `D_XY = (1 - π^out) D_{X_I Y_I} + π^out D_{X_O Y_O}`, recorded as its ID
joint distribution `D_{X_I Y_I}` on `X × {1, …, K}`, its OOD distribution `D_{X_O}` on `X` (all OOD
data carry the label `K + 1`) and its class-prior `π^out ∈ [0, 1)`. -/
structure Domain (X : Type*) [MeasurableSpace X] (K : ℕ) where
  /-- The ID joint distribution `D_{X_I Y_I}`. -/
  DI : ProbabilityMeasure (X × Fin K)
  /-- The OOD marginal distribution `D_{X_O}`. -/
  DO : ProbabilityMeasure X
  /-- The class-prior probability `π^out ∈ [0, 1)`. -/
  piOut : Set.Ico (0 : ℝ) 1

/-- Section 2: the ID marginal distribution `D_{X_I}`. -/
def marginalIn (D : Domain X K) : Measure X :=
  (D.DI : Measure (X × Fin K)).map Prod.fst

/-- Definition 3 (Section 3): `D^α_XY = (1 - α) D_{X_I Y_I} + α D_{X_O Y_O}` for `α ∈ [0, 1)`. -/
def withPrior (D : Domain X K) (α : Set.Ico (0 : ℝ) 1) : Domain X K :=
  { D with piOut := α }

/-- Section 2: the ID risk `R^in_D(h) = E_{(x,y)∼D_{X_I Y_I}} ℓ(h(x), y)`. -/
def riskIn (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (D : Domain X K) (h : X → Fin (K + 1)) : ℝ≥0∞ :=
  ∫⁻ p, (ℓ (h p.1) (Fin.castSucc p.2) : ℝ≥0∞) ∂(D.DI : Measure (X × Fin K))

/-- Section 2: the OOD risk `R^out_D(h) = E_{x∼D_{X_O}} ℓ(h(x), K + 1)`. -/
def riskOut (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (D : Domain X K) (h : X → Fin (K + 1)) :
    ℝ≥0∞ :=
  ∫⁻ x, (ℓ (h x) (Fin.last K) : ℝ≥0∞) ∂(D.DO : Measure X)

/-- Section 2: the `α`-risk `R^α_D(h) = (1 - α) R^in_D(h) + α R^out_D(h)`, `α ∈ [0, 1]`. -/
def alphaRisk (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (D : Domain X K) (α : ℝ)
    (h : X → Fin (K + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - α) * riskIn ℓ D h + ENNReal.ofReal α * riskOut ℓ D h

/-- Eq. (1) (Section 2): the risk `R_D(h) = E_{(x,y)∼D_XY} ℓ(h(x), y)`, which equals
`(1 - π^out) R^in_D(h) + π^out R^out_D(h)`. -/
def risk (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (D : Domain X K) (h : X → Fin (K + 1)) : ℝ≥0∞ :=
  alphaRisk ℓ D D.piOut h

/-- Definition 1, footnote 2 (Section 2): an algorithm maps a training sample
`S ∈ (X × 𝒴)^n` to a hypothesis function (only sample sizes `n ≥ 1` are used). -/
abbrev Algorithm (X : Type*) (K : ℕ) : Type _ :=
  (n : ℕ) → (Fin n → X × Fin K) → X → Fin (K + 1)

/-- Section 2: the law `D^n_{X_I Y_I}` of an i.i.d. training sample of size `n`. -/
def sampleMeasure (D : Domain X K) (n : ℕ) : Measure (Fin n → X × Fin K) :=
  Measure.pi fun _ : Fin n => (D.DI : Measure (X × Fin K))

/-- Definition 1 (Section 2), eq. (2): the algorithm `A` takes values in `H` and is consistent
with respect to the domain space `𝒟` with the monotonically decreasing sequence `ε → 0`:
`E_{S∼D^n_{X_I Y_I}} R_D(A(S)) ≤ inf_{h∈H} R_D(h) + ε(n)` for every `D ∈ 𝒟` and `n ≥ 1`. The
expectation is required to be defined, i.e. `S ↦ R_D(A(S))` is a.e.-measurable. -/
def IsConsistent (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (𝒟 : Set (Domain X K))
    (H : Set (X → Fin (K + 1))) (A : Algorithm X K) (ε : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → ∀ S, A n S ∈ H) ∧ Antitone ε ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ D ∈ 𝒟, ∀ n, 1 ≤ n →
      AEMeasurable (fun S => risk ℓ D (A n S)) (sampleMeasure D n) ∧
      ∫⁻ S, risk ℓ D (A n S) ∂(sampleMeasure D n) ≤
        (⨅ h ∈ H, risk ℓ D h) + ENNReal.ofReal (ε n)

/-- Definition 1 (Section 2): OOD detection is learnable in `𝒟` for `H`. -/
def IsLearnable (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (𝒟 : Set (Domain X K))
    (H : Set (X → Fin (K + 1))) : Prop :=
  ∃ (A : Algorithm X K) (ε : ℕ → ℝ), IsConsistent ℓ 𝒟 H A ε

/-- Definition 2 (Section 2), eq. (3): OOD detection is strongly learnable in `𝒟` for `H`: one
algorithm and one sequence `ε` give `E_S R^α_D(A(S)) ≤ inf_{h∈H} R^α_D(h) + ε(n)` for every
`α ∈ [0, 1]`, every `D ∈ 𝒟` and every `n ≥ 1` (each expectation being defined). -/
def IsStronglyLearnable (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (𝒟 : Set (Domain X K))
    (H : Set (X → Fin (K + 1))) : Prop :=
  ∃ (A : Algorithm X K) (ε : ℕ → ℝ),
    (∀ n, 1 ≤ n → ∀ S, A n S ∈ H) ∧ Antitone ε ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ D ∈ 𝒟, ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ n, 1 ≤ n →
        AEMeasurable (fun S => alphaRisk ℓ D α (A n S)) (sampleMeasure D n) ∧
        ∫⁻ S, alphaRisk ℓ D α (A n S) ∂(sampleMeasure D n) ≤
          (⨅ h ∈ H, alphaRisk ℓ D α h) + ENNReal.ofReal (ε n)

/-- Theorem 8 (Section 5): OOD detection is learnable in `𝒟` for `H` with a learning rate
`ε_cons(n) = O(r(n))`. -/
def IsLearnableAtRate (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (𝒟 : Set (Domain X K))
    (H : Set (X → Fin (K + 1))) (r : ℕ → ℝ) : Prop :=
  ∃ (A : Algorithm X K) (ε : ℕ → ℝ) (C : ℝ), IsConsistent ℓ 𝒟 H A ε ∧ ∀ n, 1 ≤ n → ε n ≤ C * r n

/-- Definition 3 (Section 3): `𝒟` is a priori-unknown space: `D^α_XY ∈ 𝒟` for every `D_XY ∈ 𝒟`
and every `α ∈ [0, 1)`. -/
def IsPriorUnknown (𝒟 : Set (Domain X K)) : Prop :=
  ∀ D ∈ 𝒟, ∀ α : Set.Ico (0 : ℝ) 1, withPrior D α ∈ 𝒟

/-- Theorem 1 (Section 3): `𝒟' = {D^α_XY : D_XY ∈ 𝒟, α ∈ [0, 1)}`. -/
def priorClosure (𝒟 : Set (Domain X K)) : Set (Domain X K) :=
  {D' | ∃ D ∈ 𝒟, ∃ α : Set.Ico (0 : ℝ) 1, D' = withPrior D α}

/-- Section 3: the single-distribution space `𝒟^{D_XY} = {D^α_XY : α ∈ [0, 1)}`. -/
def singleSpace (D : Domain X K) : Set (Domain X K) :=
  Set.range (withPrior D)

/-- Section 3: the total space `𝒟^all`, which consists of all domains. -/
def totalSpace : Set (Domain X K) :=
  Set.univ

/-- Section 3: the separate space `𝒟^s` of all domains with `supp D_{X_O} ∩ supp D_{X_I} = ∅`
(supports in the topology of the feature space). -/
def separateSpace [TopologicalSpace X] : Set (Domain X K) :=
  {D | Disjoint (marginalIn D).support (D.DO : Measure X).support}

/-- Section 3: the finite-ID-distribution space `𝒟^F`: a priori-unknown space containing only
finitely many distinct ID joint distributions `D_{X_I Y_I}`. -/
def IsFiniteIDSpace (𝒟 : Set (Domain X K)) : Prop :=
  IsPriorUnknown 𝒟 ∧ (Domain.DI '' 𝒟).Finite

/-- Condition 1 (Linear Condition, Section 4): for every `D_XY ∈ 𝒟` and `α ∈ [0, 1)`,
`inf_{h∈H} R^α_D(h) = (1 - α) inf_{h∈H} R^in_D(h) + α inf_{h∈H} R^out_D(h)`. -/
def LinearCondition (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (𝒟 : Set (Domain X K))
    (H : Set (X → Fin (K + 1))) : Prop :=
  ∀ D ∈ 𝒟, ∀ α ∈ Set.Ico (0 : ℝ) 1,
    (⨅ h ∈ H, alphaRisk ℓ D α h) =
      ENNReal.ofReal (1 - α) * (⨅ h ∈ H, riskIn ℓ D h) +
        ENNReal.ofReal α * (⨅ h ∈ H, riskOut ℓ D h)

/-- Definition 4 (Section 4): `D_XY` has overlap between ID and OOD distributions: there is a
σ-finite measure `μ̃` with `D_{X_I}, D_{X_O} ≪ μ̃` such that `μ̃(A_overlap) > 0`, where
`A_overlap = {x : f_I(x) > 0 and f_O(x) > 0}` and `f_I = dD_{X_I}/dμ̃`, `f_O = dD_{X_O}/dμ̃`. -/
def HasOverlap (D : Domain X K) : Prop :=
  ∃ μ : Measure X, SigmaFinite μ ∧ marginalIn D ≪ μ ∧ (D.DO : Measure X) ≪ μ ∧
    0 < μ {x | 0 < (marginalIn D).rnDeriv μ x ∧ 0 < (D.DO : Measure X).rnDeriv μ x}

/-- Assumption 1 (Section 4): `H` is separate for OOD data: every `x ∈ X` is sent to the OOD
label `K + 1` by some `h_x ∈ H`. -/
def SeparateForOOD (H : Set (X → Fin (K + 1))) : Prop :=
  ∀ x, ∃ h ∈ H, h x = Fin.last K

/-- Theorems 4 and 5 (Section 4): the map `φ` sending the ID labels to `1` and the OOD label to
`2`, written with values `0` (ID) and `1` (OOD) in `Fin 2`. -/
def phi (K : ℕ) (y : Fin (K + 1)) : Fin 2 :=
  if y = Fin.last K then 1 else 0

/-- Theorems 4 and 5 (Section 4): the binary hypothesis space `φ ∘ H = {φ ∘ h : h ∈ H}`. -/
def phiComp (H : Set (X → Fin (K + 1))) : Set (X → Fin 2) :=
  (fun h => phi K ∘ h) '' H

/-- Theorem 5 (Section 4): a finite set `C ⊆ X` is shattered by a class `F` of binary
functions: every labelling of `C` is realised by some `f ∈ F`. -/
def VCShatters {X : Type*} (F : Set (X → Fin 2)) (C : Finset X) : Prop :=
  ∀ g : X → Fin 2, ∃ f ∈ F, ∀ x ∈ C, f x = g x

/-- Theorem 5 (Section 4): the VC dimension of a class of binary functions, the largest size of
a shattered finite set (`⊤` if there is none). -/
def vcDim {X : Type*} (F : Set (X → Fin 2)) : ℕ∞ :=
  ⨆ (C : Finset X) (_ : VCShatters F C), (C.card : ℕ∞)

/-- Lemma 4 (Appendix H): a finite discrete domain: `D_{X_I Y_I}` and `D_{X_O}` are concentrated
on finite sets. -/
def IsFiniteDiscrete (D : Domain X K) : Prop :=
  (∃ s : Finset (X × Fin K), (D.DI : Measure (X × Fin K)) (↑s)ᶜ = 0) ∧
    ∃ t : Finset X, (D.DO : Measure X) (↑t)ᶜ = 0

/-- Eq. (4) (Section 5): `H^in • H^b`, the hypotheses `h` built from `h^in ∈ H^in` and
`h^b ∈ H^b` by `h(x) = h^in(x)` if `h^b(x) = 1` (ID) and `h(x) = K + 1` otherwise. The binary
labels `1` (ID) and `2` (OOD) are written `0` and `1` in `Fin 2`. -/
def dotSpace (Hin : Set (X → Fin K)) (Hb : Set (X → Fin 2)) : Set (X → Fin (K + 1)) :=
  {h | ∃ hin ∈ Hin, ∃ hb ∈ Hb,
    ∀ x, h x = if hb x = 0 then Fin.castSucc (hin x) else Fin.last K}

/-- Condition 2 (Section 5): `ℓ(y₂, y₁) ≤ ℓ(K + 1, y₁)` for all ID labels `y₁, y₂`. -/
def LossCondition2 (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) : Prop :=
  ∀ y₁ y₂ : Fin K, ℓ (Fin.castSucc y₂) (Fin.castSucc y₁) ≤ ℓ (Fin.last K) (Fin.castSucc y₁)

/-- Condition 3 (Compatibility, Section 5), with the ID-consistency classes of Definition 5:
for every `D'_XY ∈ 𝒟` and `ε > 0` there is `h_ε ∈ H` which, for every `D_XY ∈ 𝒟` with
`D_{X_I Y_I} = D'_{X_I Y_I}`, satisfies `R^out_D(h_ε) ≤ inf_{h∈H} R^out_D(h) + ε` and
`R^in_D(h_ε) ≤ inf_{h∈H} R^in_D(h) + ε`. -/
def Compatibility (ℓ : Fin (K + 1) → Fin (K + 1) → ℝ≥0) (𝒟 : Set (Domain X K))
    (H : Set (X → Fin (K + 1))) : Prop :=
  ∀ D' ∈ 𝒟, ∀ ε : ℝ, 0 < ε → ∃ hε ∈ H, ∀ D ∈ 𝒟, D.DI = D'.DI →
    riskOut ℓ D hε ≤ (⨅ h ∈ H, riskOut ℓ D h) + ENNReal.ofReal ε ∧
      riskIn ℓ D hε ≤ (⨅ h ∈ H, riskIn ℓ D h) + ENNReal.ofReal ε

end OODLearnable


